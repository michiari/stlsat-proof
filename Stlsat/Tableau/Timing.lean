/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Tableau.Syntax

/-!
# Shared timing and syntactic measures

This file defines the horizon, same-time expansion work, and timeliness
invariants used by both tableau configurations.

The rule relation is not well-founded on arbitrary nodes: an unmarked temporal
formula whose interval has already expired would be propagated forever by
`STEP`. The termination modules therefore use the following two invariants,
which are enjoyed by every initial node and preserved by every rule:

* all absolute temporal horizons are bounded by the horizon of the input;
* every temporal formula exposed through propositional structure is timely.
-/

namespace Stlsat

universe u

namespace Formula

variable {Atom : Type u}

/-- The paper's time horizon: the maximum accumulated temporal deadline. -/
def horizon : Formula Atom → ℕ
  | .truth | .atom _ => 0
  | .neg body => body.horizon
  | .and left right | .or left right => max left.horizon right.horizon
  | .eventually interval body | .always interval body => interval.upper + body.horizon
  | .strictUntil interval left right | .strictRelease interval left right =>
      interval.upper + max left.horizon right.horizon

/-- Syntactic work left for expansion rules; interval endpoints are ignored. -/
def expansionWeight : Formula Atom → ℕ
  | .truth | .atom _ => 0
  | .neg body => body.expansionWeight
  | .and left right | .or left right =>
      left.expansionWeight + right.expansionWeight + 1
  | .eventually _ body | .always _ body => body.expansionWeight + 1
  | .strictUntil _ left right | .strictRelease _ left right =>
      left.expansionWeight + right.expansionWeight + 1

/--
Every temporal operator exposed through propositional structure is still in
time.  Recursion stops at a temporal operator because intervals in its
arguments remain relative until `temporalExpansion` extracts those arguments.
-/
def Timely (time : ℕ) : Formula Atom → Prop
  | .truth | .atom _ => True
  | .neg body => body.Timely time
  | .and left right | .or left right => left.Timely time ∧ right.Timely time
  | .eventually interval _ | .always interval _ => time ≤ interval.upper
  | .strictUntil interval _ _ | .strictRelease interval _ _ => time ≤ interval.upper

@[simp]
theorem expansionWeight_temporalExpansion (formula : Formula Atom) (time : ℕ) :
    (formula.temporalExpansion time).expansionWeight = formula.expansionWeight := by
  induction formula <;> simp_all [expansionWeight, temporalExpansion]

theorem horizon_temporalExpansion_le (formula : Formula Atom) (time : ℕ) :
    (formula.temporalExpansion time).horizon ≤ time + formula.horizon := by
  induction formula with
  | truth => simp [horizon, temporalExpansion]
  | atom => simp [horizon, temporalExpansion]
  | neg body ih => simpa [horizon, temporalExpansion] using ih
  | and left right ihLeft ihRight =>
      simp only [temporalExpansion, horizon]
      apply max_le
      · exact ihLeft.trans (Nat.add_le_add_left (Nat.le_max_left _ _) _)
      · exact ihRight.trans (Nat.add_le_add_left (Nat.le_max_right _ _) _)
  | or left right ihLeft ihRight =>
      simp only [temporalExpansion, horizon]
      apply max_le
      · exact ihLeft.trans (Nat.add_le_add_left (Nat.le_max_left _ _) _)
      · exact ihRight.trans (Nat.add_le_add_left (Nat.le_max_right _ _) _)
  | eventually interval body ih =>
      simp [temporalExpansion, horizon, Interval.shift]
      omega
  | always interval body ih =>
      simp [temporalExpansion, horizon, Interval.shift]
      omega
  | strictUntil interval left right ihLeft ihRight =>
      simp [temporalExpansion, horizon, Interval.shift]
      omega
  | strictRelease interval left right ihLeft ihRight =>
      simp [temporalExpansion, horizon, Interval.shift]
      omega

@[simp]
theorem timely_zero (formula : Formula Atom) : formula.Timely 0 := by
  induction formula <;> simp_all [Timely]

@[simp]
theorem timely_temporalExpansion (formula : Formula Atom) (time : ℕ) :
    (formula.temporalExpansion time).Timely time := by
  induction formula <;> simp_all [Timely, temporalExpansion, Interval.shift]

end Formula

namespace Occurrence

variable {Atom : Type u}

/-- The horizon of the underlying (possibly marked) formula occurrence. -/
def horizon : Occurrence Atom → ℕ
  | .unmarked formula => formula.horizon
  | .markedEventually interval body | .markedAlways interval body =>
      interval.upper + body.horizon
  | .markedStrictUntil interval left right | .markedStrictRelease interval left right =>
      interval.upper + max left.horizon right.horizon

/-- Marked occurrences require no further expansion at the current instant. -/
def expansionWeight : Occurrence Atom → ℕ
  | .unmarked formula => formula.expansionWeight
  | _ => 0

/-- Timeliness of a marked or unmarked occurrence at a node time. -/
def Timely (time : ℕ) : Occurrence Atom → Prop
  | .unmarked formula => formula.Timely time
  | .markedEventually interval _ | .markedAlways interval _ => time < interval.upper
  | .markedStrictUntil interval _ _ | .markedStrictRelease interval _ _ =>
      time < interval.upper

@[simp]
theorem horizon_unmark (occurrence : Occurrence Atom) :
    occurrence.unmark.horizon = occurrence.horizon := by
  cases occurrence <;> rfl

theorem time_le_horizon_of_timely_of_temporal {occurrence : Occurrence Atom} {time : ℕ}
    (timely : occurrence.Timely time) (temporal : occurrence.isTemporal = true) :
    time ≤ occurrence.horizon := by
  cases occurrence with
  | unmarked formula =>
      cases formula <;>
        simp_all [Timely, horizon, Occurrence.isTemporal, Formula.isTemporal,
          Formula.Timely, Formula.horizon] <;> omega
  | markedEventually interval body =>
      simp only [Timely] at timely
      simp only [horizon]
      omega
  | markedAlways interval body =>
      simp only [Timely] at timely
      simp only [horizon]
      omega
  | markedStrictUntil interval left right =>
      simp only [Timely] at timely
      simp only [horizon]
      omega
  | markedStrictRelease interval left right =>
      simp only [Timely] at timely
      simp only [horizon]
      omega

end Occurrence

namespace ObligationSet

variable {Atom : Type u}

/-- Every exposed temporal occurrence is timely at the node's counter. -/
def Timely (node : ObligationSet Atom) : Prop :=
  ∀ occurrence ∈ node.label, occurrence.Timely node.time

@[simp]
theorem initial_timely (formula : Formula Atom) : (initial formula).Timely := by
  simp [Timely, initial, Occurrence.Timely]

/-- A semantically ready, timely obligation set remains timely after STEP. -/
theorem step_timely [DecidableEq Atom] {node : ObligationSet Atom}
    (nodeTimely : node.Timely) (ready : node.Ready) : node.step.Timely := by
  intro occurrence occurrenceMem
  change occurrence.Timely (node.time + 1)
  change occurrence ∈ node.stepLabel at occurrenceMem
  rw [stepLabel, Finset.mem_union] at occurrenceMem
  rcases occurrenceMem with unmarkedMem | markedMem
  · have present := (Finset.mem_filter.mp unmarkedMem).1
    have temporal := (Finset.mem_filter.mp unmarkedMem).2
    cases occurrence with
    | unmarked formula =>
        have beforeLower := ready (.unmarked formula) present
        have timely := nodeTimely (.unmarked formula) present
        cases formula with
        | truth => simp [Occurrence.isUnmarkedTemporal, Formula.isTemporal] at temporal
        | atom atom => simp [Occurrence.isUnmarkedTemporal, Formula.isTemporal] at temporal
        | neg body => simp [Occurrence.isUnmarkedTemporal, Formula.isTemporal] at temporal
        | and left right => simp [Occurrence.isUnmarkedTemporal, Formula.isTemporal] at temporal
        | or left right => simp [Occurrence.isUnmarkedTemporal, Formula.isTemporal] at temporal
        | eventually interval body =>
            simpa [Occurrence.Timely, Formula.Timely] using
              Nat.succ_le_of_lt (beforeLower.trans_le interval.lower_le_upper)
        | always interval body =>
            simpa [Occurrence.Timely, Formula.Timely] using
              Nat.succ_le_of_lt (beforeLower.trans_le interval.lower_le_upper)
        | strictUntil interval invariant target =>
            simpa [Occurrence.Timely, Formula.Timely] using
              Nat.succ_le_of_lt (beforeLower.trans_le interval.lower_le_upper)
        | strictRelease interval target invariant =>
            simpa [Occurrence.Timely, Formula.Timely] using
              Nat.succ_le_of_lt (beforeLower.trans_le interval.lower_le_upper)
    | markedEventually interval body => simp [Occurrence.isUnmarkedTemporal] at temporal
    | markedAlways interval body => simp [Occurrence.isUnmarkedTemporal] at temporal
    | markedStrictUntil interval left right =>
        simp [Occurrence.isUnmarkedTemporal] at temporal
    | markedStrictRelease interval left right =>
        simp [Occurrence.isUnmarkedTemporal] at temporal
  · rcases Finset.mem_image.mp markedMem with ⟨source, sourceMem, rfl⟩
    have continues := (Finset.mem_filter.mp sourceMem).2
    cases source <;>
      simp_all [Occurrence.markedContinuesAt, Occurrence.unmark, Occurrence.Timely,
        Formula.Timely] <;> omega

end ObligationSet

end Stlsat
