/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.Canonical

/-! # Rank-stratified construction of skipped invariant models -/

namespace Stlsat.Jump
universe u

variable {Atom : Type u}

/-- Structural rank used to order nested marked temporal obligations. -/
def formulaRank : Stlsat.Formula Atom → Nat
  | .truth | .atom _ => 0
  | .neg body => formulaRank body + 1
  | .and left right | .or left right => max (formulaRank left) (formulaRank right) + 1
  | .eventually _ body | .always _ body => formulaRank body + 1
  | .strictUntil _ invariant target | .strictRelease _ invariant target =>
      max (formulaRank invariant) (formulaRank target) + 1

@[simp] theorem rank_temporalExpansion (formula : Stlsat.Formula Atom) (time : Nat) :
    formulaRank (formula.temporalExpansion time) = formulaRank formula := by
  induction formula <;> simp_all [formulaRank, Stlsat.Formula.temporalExpansion]

/-- Translate a signal to the right by a fixed number of instants. -/
def shiftSignal {semantics : Stlsat.AtomicSemantics Atom}
    (signal : Stlsat.Signal semantics) (shift : Nat) : Stlsat.Signal semantics :=
  fun instant => signal (instant - shift)

theorem satisfies_shift_iff (formula : Stlsat.Formula Atom)
    (semantics : Stlsat.AtomicSemantics Atom) (signal : Stlsat.Signal semantics)
    (start shift : Nat) :
    formula.Satisfies semantics (shiftSignal signal shift) (start + shift) ↔
      formula.Satisfies semantics signal start := by
  induction formula generalizing start <;>
    simp_all [Stlsat.Formula.Satisfies, shiftSignal,
      Nat.add_comm, Nat.add_left_comm]

theorem satisfies_shift (formula : Stlsat.Formula Atom)
    (semantics : Stlsat.AtomicSemantics Atom) (signal : Stlsat.Signal semantics)
    (start shift : Nat) (holds : formula.Satisfies semantics signal start) :
    formula.Satisfies semantics (shiftSignal signal shift) (start + shift) :=
  (satisfies_shift_iff formula semantics signal start shift).mpr holds

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

/-- The obligations which do not require a skipped invariant: every live
unmarked occurrence and the residual of every marked eventuality. -/
def BaseHolds (node : Node Atom) (size : Nat) (semantics : Stlsat.AtomicSemantics Atom)
    (signal : Stlsat.Signal semantics) : Prop :=
  (∀ occurrence ∈ node.label,
      match occurrence.payload with
      | .unmarked formula => formula.SatisfiesFrom semantics signal node.time
      | .markedEventually _ _ => occurrence.SatisfiedBy semantics signal node.time
      | _ => True) ∧
    ∀ occurrence ∈ node.label, occurrence.isTemporal = true →
      occurrence.unmark.SatisfiedBy semantics signal (node.time + size)

/-- Base obligations together with all marked non-eventual residuals up to a
given structural rank. -/
def RankedHolds (node : Node Atom) (size rank : Nat)
    (semantics : Stlsat.AtomicSemantics Atom) (signal : Stlsat.Signal semantics) : Prop :=
  node.BaseHolds size semantics signal ∧
    ∀ occurrence ∈ node.label,
      (match occurrence.payload with
      | .markedAlways _ _ | .markedStrictUntil _ _ _ |
          .markedStrictRelease _ _ _ => True
      | _ => False) →
      formulaRank occurrence.formula ≤ rank →
        occurrence.SatisfiedBy semantics signal node.time

/-- A successor model supplies the base signal at a poised source node.  The
only instantaneous change is the locally consistent valuation at the source
time. -/
theorem exists_baseSignal {node : Node Atom} {size : Nat}
    {semantics : Stlsat.AtomicSemantics Atom}
    (notRejected : ¬node.Rejected semantics) (poised : node.Poised)
    (computed : node.jumpSize? = some size) (timely : node.Timely)
    (normal : node.InStrictNormalForm)
    (childModel : (node.jump size).Model semantics) :
    ∃ signal : Stlsat.Signal semantics, node.BaseHolds size semantics signal := by
  have positive := node.jumpSize_pos computed
  have locallyConsistent : node.erase.LocallyConsistent semantics := by
    by_contra inconsistent
    exact notRejected (Or.inr inconsistent)
  rcases locallyConsistent with ⟨valuation, valuationSatisfies⟩
  let signal : Stlsat.Signal semantics :=
    Function.update childModel.signal node.time valuation
  have childHolds (occurrence : AnnotatedOccurrence Atom) (present : occurrence ∈ node.label)
      (temporal : occurrence.isTemporal = true) :
      occurrence.unmark.SatisfiedBy semantics signal (node.time + size) := by
    have survives := node.temporal_survives_computed_jump poised timely computed occurrence
      present temporal
    have childMem : occurrence.unmark ∈ (node.jump size).label := by
      change occurrence.unmark ∈ node.jumpLabel size
      exact Finset.mem_image.mpr
        ⟨occurrence, Finset.mem_filter.mpr ⟨present, survives⟩, rfl⟩
    have old := (Node.satisfiedBy_iff (node.jump size) semantics childModel.signal).1
      childModel.satisfies occurrence.unmark childMem
    have updated := (Stlsat.Occurrence.satisfiedBy_congr_of_eqOn_ge
      occurrence.unmark.payload semantics (leftSignal := childModel.signal)
      (rightSignal := signal) (time := node.time + size) (by
        intro instant instantGe
        change childModel.signal instant =
          Function.update childModel.signal node.time valuation instant
        simp [Function.update, show instant ≠ node.time by omega])).mp old
    simpa [Node.jump] using updated
  refine ⟨signal, ?_, childHolds⟩
  intro occurrence present
  have occurrenceNormal := (normal_iff node).mp normal occurrence present
  cases occurrence with
  | mk id payload parent =>
      cases payload with
      | unmarked formula =>
          cases formula with
          | truth => simp [Stlsat.Formula.SatisfiesFrom]
          | atom atom =>
              have erasedMem : Stlsat.Occurrence.unmarked (.atom atom) ∈ node.erase.label :=
                Finset.mem_image.mpr ⟨_, present, rfl⟩
              have literal := valuationSatisfies _ erasedMem
              simpa [Stlsat.Formula.SatisfiesFrom, Stlsat.Occurrence.LiteralSatisfied,
                signal] using literal
          | neg body =>
              cases body with
              | truth =>
                  exfalso
                  apply notRejected
                  exact Or.inl (Finset.mem_image.mpr ⟨_, present, rfl⟩)
              | atom atom =>
                  have erasedMem : Stlsat.Occurrence.unmarked (.neg (.atom atom)) ∈
                      node.erase.label := Finset.mem_image.mpr ⟨_, present, rfl⟩
                  have literal := valuationSatisfies _ erasedMem
                  simpa [Stlsat.Formula.SatisfiesFrom,
                    Stlsat.Occurrence.LiteralSatisfied, signal] using literal
              | neg body => simp [AnnotatedOccurrence.InStrictNormalForm,
                  Stlsat.Occurrence.InStrictNormalForm,
                  Stlsat.Formula.InStrictNormalForm] at occurrenceNormal
              | and left right => simp [AnnotatedOccurrence.InStrictNormalForm,
                  Stlsat.Occurrence.InStrictNormalForm,
                  Stlsat.Formula.InStrictNormalForm] at occurrenceNormal
              | or left right => simp [AnnotatedOccurrence.InStrictNormalForm,
                  Stlsat.Occurrence.InStrictNormalForm,
                  Stlsat.Formula.InStrictNormalForm] at occurrenceNormal
              | eventually interval body => simp [AnnotatedOccurrence.InStrictNormalForm,
                  Stlsat.Occurrence.InStrictNormalForm,
                  Stlsat.Formula.InStrictNormalForm] at occurrenceNormal
              | always interval body => simp [AnnotatedOccurrence.InStrictNormalForm,
                  Stlsat.Occurrence.InStrictNormalForm,
                  Stlsat.Formula.InStrictNormalForm] at occurrenceNormal
              | strictUntil interval left right =>
                  simp [AnnotatedOccurrence.InStrictNormalForm,
                    Stlsat.Occurrence.InStrictNormalForm,
                    Stlsat.Formula.InStrictNormalForm] at occurrenceNormal
              | strictRelease interval left right =>
                  simp [AnnotatedOccurrence.InStrictNormalForm,
                    Stlsat.Occurrence.InStrictNormalForm,
                    Stlsat.Formula.InStrictNormalForm] at occurrenceNormal
          | and left right =>
              exfalso
              exact poised ⟨_, Expansion.conjunction _ left right rfl present⟩
          | or left right =>
              exfalso
              exact poised ⟨_, Expansion.disjunction _ left right rfl present⟩
          | eventually interval body =>
              have beforeLower := beforeLower_of_unmarked_temporal poised timely _ present
                interval (.eventually interval body) rfl rfl
              have destinationLe := node.jump_destination_le_lower _ interval present rfl
                computed beforeLower
              have later := childHolds _ present (by
                simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal,
                  Stlsat.Formula.isTemporal])
              exact eventually_satisfiedFrom_earlier (by omega) later
          | always interval body =>
              have beforeLower := beforeLower_of_unmarked_temporal poised timely _ present
                interval (.always interval body) rfl rfl
              have destinationLe := node.jump_destination_le_lower _ interval present rfl
                computed beforeLower
              have later := childHolds _ present (by
                simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal,
                  Stlsat.Formula.isTemporal])
              exact always_satisfiedFrom_earlier_beforeLower (by omega) destinationLe later
          | strictUntil interval invariant target =>
              have beforeLower := beforeLower_of_unmarked_temporal poised timely _ present
                interval (.strictUntil interval invariant target) rfl rfl
              have destinationLe := node.jump_destination_le_lower _ interval present rfl
                computed beforeLower
              have later := childHolds _ present (by
                simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal,
                  Stlsat.Formula.isTemporal])
              exact strictUntil_satisfiedFrom_earlier_beforeLower (by omega)
                destinationLe later
          | strictRelease interval target invariant =>
              have beforeLower := beforeLower_of_unmarked_temporal poised timely _ present
                interval (.strictRelease interval target invariant) rfl rfl
              have destinationLe := node.jump_destination_le_lower _ interval present rfl
                computed beforeLower
              have later := childHolds _ present (by
                simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal,
                  Stlsat.Formula.isTemporal])
              exact strictRelease_satisfiedFrom_earlier_beforeLower (by omega)
                destinationLe later
      | markedEventually interval body =>
          have later := childHolds _ present (by
            simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal])
          have transported := eventually_satisfiedFrom_earlier
            (start := node.time + 1) (finish := node.time + size) (by omega) later
          simpa [AnnotatedOccurrence.SatisfiedBy, Stlsat.Occurrence.SatisfiedBy] using
            transported
      | markedAlways interval body => trivial
      | markedStrictUntil interval invariant target => trivial
      | markedStrictRelease interval target invariant => trivial

end Node


namespace ExpansionFrontier

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom}

/-- A frontier whose formula rank is already available in `RankedHolds` is
semantically reconstructible.  Proper subfrontiers decrease rank; postponed
temporal roots are supplied by the ranked residual hypothesis. -/
theorem satisfiedBy_of_ranked {node : Node Atom} {id parent formula size rank}
    (frontier : ExpansionFrontier node id parent formula)
    {signal : Stlsat.Signal semantics} (holds : node.RankedHolds size rank semantics signal)
    (bounded : formulaRank formula ≤ rank) :
    formula.SatisfiesFrom semantics signal node.time := by
  induction frontier with
  | live id parent formula present => exact holds.1.1 _ present
  | disjunctionLeft id parent left right frontier ih =>
      simp only [formulaRank] at bounded
      simpa only [Stlsat.Formula.SatisfiesFrom] using Or.inl (ih (by omega))
  | disjunctionRight id parent left right frontier ih =>
      simp only [formulaRank] at bounded
      simpa only [Stlsat.Formula.SatisfiesFrom] using Or.inr (ih (by omega))
  | conjunction id parent left right leftFrontier rightFrontier ihLeft ihRight =>
      simp only [formulaRank] at bounded
      simpa only [Stlsat.Formula.SatisfiesFrom] using
        And.intro (ihLeft (by omega)) (ihRight (by omega))
  | eventuallyNow id parent interval body active notAfter bodyFrontier ih =>
      simp only [formulaRank] at bounded
      have now := (Stlsat.Formula.satisfiesFrom_temporalExpansion body semantics signal
        node.time).mp (ih (by simpa using show formulaRank body ≤ rank by omega))
      by_cases beforeEnd : node.time < interval.upper
      · exact Stlsat.Formula.eventually_now active beforeEnd now
      · exact Stlsat.Formula.eventually_atEnd (by omega) now
  | eventuallyPostpone id parent interval body active beforeEnd present =>
      have later := holds.1.1 _ present
      simpa [Node.BaseHolds, AnnotatedOccurrence.SatisfiedBy,
        Stlsat.Occurrence.SatisfiedBy] using Stlsat.Formula.eventually_later later
  | alwaysPostpone id parent interval body active beforeEnd present bodyFrontier ih =>
      let occurrence : AnnotatedOccurrence Atom :=
        .mk id (.markedAlways interval body) parent
      have later := holds.2 occurrence present (by trivial)
        (by simpa [occurrence, AnnotatedOccurrence.formula] using bounded)
      apply Stlsat.Formula.always_now_later active
      · simp only [formulaRank] at bounded
        exact (Stlsat.Formula.satisfiesFrom_temporalExpansion body semantics signal
          node.time).mp (ih (by simpa using show formulaRank body ≤ rank by omega))
      · simpa [occurrence, AnnotatedOccurrence.SatisfiedBy,
          Stlsat.Occurrence.SatisfiedBy] using later
  | alwaysAtEnd id parent interval body atEnd bodyFrontier ih =>
      simp only [formulaRank] at bounded
      apply Stlsat.Formula.always_atEnd atEnd
      exact (Stlsat.Formula.satisfiesFrom_temporalExpansion body semantics signal
        node.time).mp (ih (by simpa using show formulaRank body ≤ rank by omega))
  | strictUntilNow id parent interval invariant target active notAfter targetFrontier ih =>
      simp only [formulaRank] at bounded
      have now := (Stlsat.Formula.satisfiesFrom_temporalExpansion target semantics signal
        node.time).mp (ih (by simpa using show formulaRank target ≤ rank by omega))
      by_cases beforeEnd : node.time < interval.upper
      · exact Stlsat.Formula.strictUntil_now active beforeEnd now
      · exact Stlsat.Formula.strictUntil_atEnd (by omega) now
  | strictUntilPostpone id parent interval invariant target active beforeEnd present
      invariantFrontier ih =>
      let occurrence : AnnotatedOccurrence Atom :=
        .mk id (.markedStrictUntil interval invariant target) parent
      have later := holds.2 occurrence present (by trivial)
        (by simpa [occurrence, AnnotatedOccurrence.formula] using bounded)
      apply Stlsat.Formula.strictUntil_later active
      · simp only [formulaRank] at bounded
        exact (Stlsat.Formula.satisfiesFrom_temporalExpansion invariant semantics signal
          node.time).mp (ih (by simpa using show formulaRank invariant ≤ rank by omega))
      · simpa [occurrence, AnnotatedOccurrence.SatisfiedBy,
          Stlsat.Occurrence.SatisfiedBy] using later
  | strictReleaseNow id parent interval target invariant active beforeEnd targetFrontier
      invariantFrontier ihTarget ihInvariant =>
      simp only [formulaRank] at bounded
      apply Stlsat.Formula.strictRelease_now active beforeEnd
      · exact (Stlsat.Formula.satisfiesFrom_temporalExpansion target semantics signal
          node.time).mp (ihTarget (by
            simpa using show formulaRank target ≤ rank by omega))
      · exact (Stlsat.Formula.satisfiesFrom_temporalExpansion invariant semantics signal
          node.time).mp (ihInvariant (by
            simpa using show formulaRank invariant ≤ rank by omega))
  | strictReleasePostpone id parent interval target invariant active beforeEnd present
      invariantFrontier ih =>
      let occurrence : AnnotatedOccurrence Atom :=
        .mk id (.markedStrictRelease interval target invariant) parent
      have later := holds.2 occurrence present (by trivial)
        (by simpa [occurrence, AnnotatedOccurrence.formula] using bounded)
      apply Stlsat.Formula.strictRelease_later
      · simp only [formulaRank] at bounded
        exact (Stlsat.Formula.satisfiesFrom_temporalExpansion invariant semantics signal
          node.time).mp (ih (by
            simpa using show formulaRank invariant ≤ rank by omega))
      · simpa [occurrence, AnnotatedOccurrence.SatisfiedBy,
          Stlsat.Occurrence.SatisfiedBy] using later
  | strictReleaseAtEnd id parent interval target invariant atEnd invariantFrontier ih =>
      simp only [formulaRank] at bounded
      apply Stlsat.Formula.strictRelease_atEnd atEnd
      exact (Stlsat.Formula.satisfiesFrom_temporalExpansion invariant semantics signal
        node.time).mp (ih (by
          simpa using show formulaRank invariant ≤ rank by omega))

end ExpansionFrontier
end Stlsat.Jump
