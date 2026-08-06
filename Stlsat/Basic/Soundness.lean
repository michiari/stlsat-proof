/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Semantics
import Stlsat.Basic.Termination

/-!
# Soundness of the basic STL tableau

This file proves that an accepting branch of the basic tableau yields a
satisfying signal. The `JUMP` rule is deliberately outside this development.

The paper presents a model as a finite sequence of formula sets closed under
the tableau expansion laws. Taken literally, its clauses do not constrain
temporal formulas in the last set: choosing a sequence of length zero would,
for example, make `F_[1,1] ¬⊤` a model. Its stated local-consistency condition
also omits time zero. We instead give the corrected proof obligations a
semantic representation. `Formula.SatisfiesFrom` interprets an absolute-time
formula in a tableau label from the node's current time, and `Node.Model`
contains one signal realizing every occurrence in the label. Marked
occurrences are the residual temporal obligation starting at the next
instant. This retains the paper's proof structure: build a model backwards
along an accepting branch, then use the initial-node bridge to obtain ordinary
STL satisfiability.

At a `STEP`, the child model is extended backwards by replacing the signal's
valuation at the parent time with a locally consistent valuation. Future
locality ensures that this replacement preserves all child obligations.

The paper's displayed strict-release endpoint law appears to contain a typo:
under the Background dual semantics (and the formal tableau rule), only the
invariant is required at the upper endpoint. This proof follows that semantics.
-/

namespace Stlsat

universe u

namespace Formula

variable {Atom : Type u}

/-- Satisfaction of an absolute tableau obligation from a current instant. -/
def SatisfiesFrom (formula : Formula Atom) (semantics : AtomicSemantics Atom)
    (signal : Signal semantics) (time : ℕ) : Prop :=
  match formula with
  | .truth => True
  | .atom proposition => semantics.holds (signal time) proposition
  | .neg body => ¬body.SatisfiesFrom semantics signal time
  | .and left right =>
      left.SatisfiesFrom semantics signal time ∧ right.SatisfiesFrom semantics signal time
  | .or left right =>
      left.SatisfiesFrom semantics signal time ∨ right.SatisfiesFrom semantics signal time
  | .eventually interval body =>
      ∃ offset, interval.Contains (time + offset) ∧
        body.Satisfies semantics signal (time + offset)
  | .always interval body =>
      ∀ offset, interval.Contains (time + offset) →
        body.Satisfies semantics signal (time + offset)
  | .strictUntil interval invariant target =>
      ∃ targetOffset,
        interval.Contains (time + targetOffset) ∧
          target.Satisfies semantics signal (time + targetOffset) ∧
          ∀ invariantOffset,
            interval.lower ≤ time + invariantOffset → invariantOffset < targetOffset →
              invariant.Satisfies semantics signal (time + invariantOffset)
  | .strictRelease interval target invariant =>
      ¬∃ violatingOffset,
        interval.Contains (time + violatingOffset) ∧
          ¬invariant.Satisfies semantics signal (time + violatingOffset) ∧
          ∀ targetOffset,
            interval.lower ≤ time + targetOffset → targetOffset < violatingOffset →
              ¬target.Satisfies semantics signal (time + targetOffset)
termination_by formula

@[simp]
theorem satisfiesFrom_temporalExpansion (formula : Formula Atom)
    (semantics : AtomicSemantics Atom) (signal : Signal semantics) (time : ℕ) :
    (formula.temporalExpansion time).SatisfiesFrom semantics signal time ↔
      formula.Satisfies semantics signal time := by
  induction formula <;>
    simp_all [SatisfiesFrom, Satisfies, temporalExpansion, Interval.shift,
      Interval.Contains, Nat.add_comm]

@[simp]
theorem temporalExpansion_zero (formula : Formula Atom) :
    formula.temporalExpansion 0 = formula := by
  induction formula <;>
    simp_all [temporalExpansion, Interval.shift]

@[simp]
theorem inStrictNormalForm_temporalExpansion (formula : Formula Atom) (time : ℕ) :
    (formula.temporalExpansion time).InStrictNormalForm ↔ formula.InStrictNormalForm := by
  induction formula with
  | truth => simp [temporalExpansion, InStrictNormalForm]
  | atom proposition => simp [temporalExpansion, InStrictNormalForm]
  | neg body ih => cases body <;> simp [temporalExpansion, InStrictNormalForm]
  | and left right ihLeft ihRight =>
      simp [temporalExpansion, InStrictNormalForm, ihLeft, ihRight]
  | or left right ihLeft ihRight =>
      simp [temporalExpansion, InStrictNormalForm, ihLeft, ihRight]
  | eventually interval body ih => simp [temporalExpansion, InStrictNormalForm]
  | always interval body ih => simp [temporalExpansion, InStrictNormalForm]
  | strictUntil interval left right ihLeft ihRight => simp [temporalExpansion, InStrictNormalForm]
  | strictRelease interval left right ihLeft ihRight => simp [temporalExpansion, InStrictNormalForm]

theorem satisfies_congr_of_eqOn_ge (formula : Formula Atom)
    (semantics : AtomicSemantics Atom) {leftSignal rightSignal : Signal semantics}
    {time : ℕ} (agree : ∀ instant, time ≤ instant → leftSignal instant = rightSignal instant) :
    formula.Satisfies semantics leftSignal time ↔
      formula.Satisfies semantics rightSignal time := by
  induction formula generalizing time with
  | truth => simp [Satisfies]
  | atom proposition => simp [Satisfies, agree time (by omega)]
  | neg body ih => simp only [Satisfies]; exact not_congr (ih agree)
  | and left right ihLeft ihRight =>
      simp only [Satisfies]
      exact and_congr (ihLeft agree) (ihRight agree)
  | or left right ihLeft ihRight =>
      simp only [Satisfies]
      exact or_congr (ihLeft agree) (ihRight agree)
  | eventually interval body ih =>
      simp only [Satisfies]
      apply exists_congr
      intro offset
      apply and_congr_right
      intro _
      apply ih
      intro instant instant_ge
      apply agree instant
      omega
  | always interval body ih =>
      simp only [Satisfies]
      apply forall_congr'
      intro offset
      apply imp_congr_right
      intro _
      apply ih
      intro instant instant_ge
      apply agree instant
      omega
  | strictUntil interval invariant target ihInvariant ihTarget =>
      simp only [Satisfies]
      apply exists_congr
      intro targetOffset
      apply and_congr_right
      intro _
      apply and_congr
      · apply ihTarget
        intro instant instant_ge
        apply agree instant
        omega
      · apply forall_congr'
        intro invariantOffset
        apply imp_congr_right
        intro _
        apply imp_congr_right
        intro _
        apply ihInvariant
        intro instant instant_ge
        apply agree instant
        omega
  | strictRelease interval target invariant ihTarget ihInvariant =>
      simp only [Satisfies]
      apply not_congr
      apply exists_congr
      intro violatingOffset
      apply and_congr_right
      intro _
      apply and_congr
      · exact not_congr (ihInvariant (by
          intro instant instant_ge
          apply agree instant
          omega))
      · apply forall_congr'
        intro targetOffset
        apply imp_congr_right
        intro _
        apply imp_congr_right
        intro _
        exact not_congr (ihTarget (by
          intro instant instant_ge
          apply agree instant
          omega))

theorem satisfiesFrom_congr_of_eqOn_ge (formula : Formula Atom)
    (semantics : AtomicSemantics Atom) {leftSignal rightSignal : Signal semantics}
    {time : ℕ} (agree : ∀ instant, time ≤ instant → leftSignal instant = rightSignal instant) :
    formula.SatisfiesFrom semantics leftSignal time ↔
      formula.SatisfiesFrom semantics rightSignal time := by
  cases formula with
  | truth => simp [SatisfiesFrom]
  | atom proposition => simp [SatisfiesFrom, agree time (by omega)]
  | neg body =>
      simp only [SatisfiesFrom]
      exact not_congr (satisfiesFrom_congr_of_eqOn_ge body semantics agree)
  | and left right =>
      simp only [SatisfiesFrom]
      exact and_congr
        (satisfiesFrom_congr_of_eqOn_ge left semantics agree)
        (satisfiesFrom_congr_of_eqOn_ge right semantics agree)
  | or left right =>
      simp only [SatisfiesFrom]
      exact or_congr
        (satisfiesFrom_congr_of_eqOn_ge left semantics agree)
        (satisfiesFrom_congr_of_eqOn_ge right semantics agree)
  | eventually interval body =>
      simp only [SatisfiesFrom]
      apply exists_congr
      intro offset
      apply and_congr_right
      intro _
      apply satisfies_congr_of_eqOn_ge
      intro instant instant_ge
      apply agree instant
      omega
  | always interval body =>
      simp only [SatisfiesFrom]
      apply forall_congr'
      intro offset
      apply imp_congr_right
      intro _
      apply satisfies_congr_of_eqOn_ge
      intro instant instant_ge
      apply agree instant
      omega
  | strictUntil interval invariant target =>
      simp only [SatisfiesFrom]
      apply exists_congr
      intro targetOffset
      apply and_congr_right
      intro _
      apply and_congr
      · apply satisfies_congr_of_eqOn_ge
        intro instant instant_ge
        apply agree instant
        omega
      · apply forall_congr'
        intro invariantOffset
        apply imp_congr_right
        intro _
        apply imp_congr_right
        intro _
        apply satisfies_congr_of_eqOn_ge
        intro instant instant_ge
        apply agree instant
        omega
  | strictRelease interval target invariant =>
      simp only [SatisfiesFrom]
      apply not_congr
      apply exists_congr
      intro violatingOffset
      apply and_congr_right
      intro _
      apply and_congr
      · exact not_congr (satisfies_congr_of_eqOn_ge invariant semantics (by
          intro instant instant_ge
          apply agree instant
          omega))
      · apply forall_congr'
        intro targetOffset
        apply imp_congr_right
        intro _
        apply imp_congr_right
        intro _
        exact not_congr (satisfies_congr_of_eqOn_ge target semantics (by
          intro instant instant_ge
          apply agree instant
          omega))
termination_by formula

theorem eventually_now {interval : Interval} {body : Formula Atom}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics} {time : ℕ}
    (active : interval.lower ≤ time) (beforeEnd : time < interval.upper)
    (now : body.Satisfies semantics signal time) :
    (eventually interval body).SatisfiesFrom semantics signal time := by
  simp only [SatisfiesFrom]
  refine ⟨0, ?_, by simpa using now⟩
  simp [Interval.Contains]
  omega

theorem eventually_later {interval : Interval} {body : Formula Atom}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics} {time : ℕ}
    (later : (eventually interval body).SatisfiesFrom semantics signal (time + 1)) :
    (eventually interval body).SatisfiesFrom semantics signal time := by
  simp only [SatisfiesFrom] at later ⊢
  rcases later with ⟨offset, contained, holds⟩
  refine ⟨offset + 1, ?_, ?_⟩
  · simpa [SatisfiesFrom, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using contained
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using holds

theorem always_now_later {interval : Interval} {body : Formula Atom}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics} {time : ℕ}
    (_active : interval.lower ≤ time)
    (now : body.Satisfies semantics signal time)
    (later : (always interval body).SatisfiesFrom semantics signal (time + 1)) :
    (always interval body).SatisfiesFrom semantics signal time := by
  simp only [SatisfiesFrom] at later ⊢
  intro offset contained
  rcases offset with _ | offset
  · simpa using now
  · exact (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        later offset (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using contained))

theorem strictUntil_now {interval : Interval} {invariant target : Formula Atom}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics} {time : ℕ}
    (active : interval.lower ≤ time) (beforeEnd : time < interval.upper)
    (now : target.Satisfies semantics signal time) :
    (strictUntil interval invariant target).SatisfiesFrom semantics signal time := by
  simp only [SatisfiesFrom]
  refine ⟨0, ?_, by simpa using now, ?_⟩
  · simp [Interval.Contains]
    omega
  · intro invariantOffset _ impossible
    omega

theorem strictUntil_later {interval : Interval} {invariant target : Formula Atom}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics} {time : ℕ}
    (_active : interval.lower ≤ time)
    (now : invariant.Satisfies semantics signal time)
    (later : (strictUntil interval invariant target).SatisfiesFrom semantics signal (time + 1)) :
    (strictUntil interval invariant target).SatisfiesFrom semantics signal time := by
  simp only [SatisfiesFrom] at later ⊢
  rcases later with ⟨targetOffset, contained, targetHolds, invariantHolds⟩
  refine ⟨targetOffset + 1, ?_, ?_, ?_⟩
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using contained
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using targetHolds
  · intro invariantOffset lower ltTarget
    rcases invariantOffset with _ | invariantOffset
    · simpa using now
    · exact (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          invariantHolds invariantOffset
            (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lower)
            (by omega))

theorem strictRelease_now {interval : Interval} {target invariant : Formula Atom}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics} {time : ℕ}
    (active : interval.lower ≤ time) (_beforeEnd : time < interval.upper)
    (targetNow : target.Satisfies semantics signal time)
    (invariantNow : invariant.Satisfies semantics signal time) :
    (strictRelease interval target invariant).SatisfiesFrom semantics signal time := by
  simp only [SatisfiesFrom]
  rintro ⟨violatingOffset, contained, invariantFails, targetsFail⟩
  rcases violatingOffset with _ | violatingOffset
  · exact invariantFails (by simpa using invariantNow)
  · exact targetsFail 0 (by omega) (by omega) (by simpa using targetNow)

theorem strictRelease_later {interval : Interval} {target invariant : Formula Atom}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics} {time : ℕ}
    (invariantNow : invariant.Satisfies semantics signal time)
    (later : (strictRelease interval target invariant).SatisfiesFrom semantics signal (time + 1)) :
    (strictRelease interval target invariant).SatisfiesFrom semantics signal time := by
  simp only [SatisfiesFrom] at later ⊢
  rintro ⟨violatingOffset, contained, invariantFails, targetsFail⟩
  rcases violatingOffset with _ | violatingOffset
  · exact invariantFails (by simpa using invariantNow)
  · apply later
    refine ⟨violatingOffset, ?_, ?_, ?_⟩
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using contained
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using invariantFails
    · intro targetOffset lower ltTarget
      exact (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          targetsFail (targetOffset + 1)
            (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lower)
            (by omega))

theorem eventually_atEnd {interval : Interval} {body : Formula Atom}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics} {time : ℕ}
    (atEnd : time = interval.upper)
    (now : body.Satisfies semantics signal time) :
    (eventually interval body).SatisfiesFrom semantics signal time := by
  simp only [SatisfiesFrom]
  refine ⟨0, ?_, by simpa using now⟩
  simp [Interval.Contains]
  have := interval.lower_le_upper
  omega

theorem always_atEnd {interval : Interval} {body : Formula Atom}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics} {time : ℕ}
    (atEnd : time = interval.upper)
    (now : body.Satisfies semantics signal time) :
    (always interval body).SatisfiesFrom semantics signal time := by
  simp only [SatisfiesFrom]
  intro offset contained
  have : offset = 0 := by
    simp [Interval.Contains] at contained
    omega
  subst offset
  simpa using now

theorem strictUntil_atEnd {interval : Interval} {invariant target : Formula Atom}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics} {time : ℕ}
    (atEnd : time = interval.upper)
    (now : target.Satisfies semantics signal time) :
    (strictUntil interval invariant target).SatisfiesFrom semantics signal time := by
  simp only [SatisfiesFrom]
  refine ⟨0, ?_, by simpa using now, ?_⟩
  · simp [Interval.Contains]
    have := interval.lower_le_upper
    omega
  · omega

theorem strictRelease_atEnd {interval : Interval} {target invariant : Formula Atom}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics} {time : ℕ}
    (atEnd : time = interval.upper)
    (invariantNow : invariant.Satisfies semantics signal time) :
    (strictRelease interval target invariant).SatisfiesFrom semantics signal time := by
  simp only [SatisfiesFrom]
  rintro ⟨violatingOffset, contained, invariantFails, targetsFail⟩
  have : violatingOffset = 0 := by
    simp [Interval.Contains] at contained
    omega
  subst violatingOffset
  exact invariantFails (by simpa using invariantNow)

theorem always_beforeLower {interval : Interval} {body : Formula Atom}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics} {time : ℕ}
    (beforeLower : time < interval.lower)
    (later : (always interval body).SatisfiesFrom semantics signal (time + 1)) :
    (always interval body).SatisfiesFrom semantics signal time := by
  simp only [SatisfiesFrom] at later ⊢
  intro offset contained
  rcases offset with _ | offset
  · simp [Interval.Contains] at contained
    omega
  · exact (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        later offset (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using contained))

theorem strictUntil_beforeLower {interval : Interval} {invariant target : Formula Atom}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics} {time : ℕ}
    (beforeLower : time < interval.lower)
    (later : (strictUntil interval invariant target).SatisfiesFrom semantics signal (time + 1)) :
    (strictUntil interval invariant target).SatisfiesFrom semantics signal time := by
  simp only [SatisfiesFrom] at later ⊢
  rcases later with ⟨targetOffset, contained, targetHolds, invariantHolds⟩
  refine ⟨targetOffset + 1, ?_, ?_, ?_⟩
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using contained
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using targetHolds
  · intro invariantOffset lower ltTarget
    rcases invariantOffset with _ | invariantOffset
    · omega
    · exact (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          invariantHolds invariantOffset
            (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lower)
            (by omega))

theorem strictRelease_beforeLower {interval : Interval} {target invariant : Formula Atom}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics} {time : ℕ}
    (beforeLower : time < interval.lower)
    (later : (strictRelease interval target invariant).SatisfiesFrom semantics signal (time + 1)) :
    (strictRelease interval target invariant).SatisfiesFrom semantics signal time := by
  simp only [SatisfiesFrom] at later ⊢
  rintro ⟨violatingOffset, contained, invariantFails, targetsFail⟩
  rcases violatingOffset with _ | violatingOffset
  · simp [Interval.Contains] at contained
    omega
  · apply later
    refine ⟨violatingOffset, ?_, ?_, ?_⟩
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using contained
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using invariantFails
    · intro targetOffset lower ltTarget
      exact (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          targetsFail (targetOffset + 1)
            (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lower)
            (by omega))

end Formula

namespace Occurrence

variable {Atom : Type u}

/-- The proof obligation denoted by an occurrence at a tableau node. -/
def SatisfiedBy (occurrence : Occurrence Atom) (semantics : AtomicSemantics Atom)
    (signal : Signal semantics) (time : ℕ) : Prop :=
  match occurrence with
  | .unmarked formula => formula.SatisfiesFrom semantics signal time
  | .markedEventually interval body =>
      (Formula.eventually interval body).SatisfiesFrom semantics signal (time + 1)
  | .markedAlways interval body =>
      (Formula.always interval body).SatisfiesFrom semantics signal (time + 1)
  | .markedStrictUntil interval invariant target =>
      (Formula.strictUntil interval invariant target).SatisfiesFrom semantics signal (time + 1)
  | .markedStrictRelease interval target invariant =>
      (Formula.strictRelease interval target invariant).SatisfiesFrom semantics signal (time + 1)

/-- Normality of the formula denoted by an occurrence. -/
def InStrictNormalForm (occurrence : Occurrence Atom) : Prop :=
  match occurrence with
  | .unmarked formula => formula.InStrictNormalForm
  | .markedEventually interval body =>
      (Formula.eventually interval body).InStrictNormalForm
  | .markedAlways interval body => (Formula.always interval body).InStrictNormalForm
  | .markedStrictUntil interval invariant target =>
      (Formula.strictUntil interval invariant target).InStrictNormalForm
  | .markedStrictRelease interval target invariant =>
      (Formula.strictRelease interval target invariant).InStrictNormalForm

@[simp]
theorem inStrictNormalForm_unmark (occurrence : Occurrence Atom) :
    occurrence.unmark.InStrictNormalForm ↔ occurrence.InStrictNormalForm := by
  cases occurrence <;> rfl

theorem satisfiedBy_congr_of_eqOn_ge (occurrence : Occurrence Atom)
    (semantics : AtomicSemantics Atom) {leftSignal rightSignal : Signal semantics}
    {time : ℕ} (agree : ∀ instant, time ≤ instant → leftSignal instant = rightSignal instant) :
    occurrence.SatisfiedBy semantics leftSignal time ↔
      occurrence.SatisfiedBy semantics rightSignal time := by
  cases occurrence <;> simp only [SatisfiedBy] <;>
    apply Formula.satisfiesFrom_congr_of_eqOn_ge <;>
    intro instant instant_ge <;> apply agree instant <;> omega

end Occurrence

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

/-- One signal realizes every proof obligation in the node label. -/
def SatisfiedBy (node : Node Atom) (semantics : AtomicSemantics Atom)
    (signal : Signal semantics) : Prop :=
  ∀ occurrence ∈ node.label, occurrence.SatisfiedBy semantics signal node.time

/-- A semantic model of all the proof obligations stored in a tableau node. -/
structure Model (node : Node Atom) (semantics : AtomicSemantics Atom) where
  /-- The signal reconstructed from the branch suffix rooted at this node. -/
  signal : Signal semantics
  /-- Every marked or unmarked occurrence in the node is realized by `signal`. -/
  satisfies : node.SatisfiedBy semantics signal

/-- A tableau node has a semantic model. -/
def HasModel (node : Node Atom) (semantics : AtomicSemantics Atom) : Prop :=
  Nonempty (node.Model semantics)

/-- Every formula occurrence in a node is in strict normal form. -/
def InStrictNormalForm (node : Node Atom) : Prop :=
  ∀ occurrence ∈ node.label, occurrence.InStrictNormalForm

theorem inStrictNormalForm_replace {node : Node Atom} {selected : Occurrence Atom}
    {replacement : List (Occurrence Atom)} (node_normal : node.InStrictNormalForm)
    (replacement_normal : ∀ occurrence ∈ replacement, occurrence.InStrictNormalForm) :
    (node.replace selected replacement).InStrictNormalForm := by
  intro occurrence occurrence_mem
  change occurrence ∈ node.label.erase selected ∪ replacement.toFinset at occurrence_mem
  rw [Finset.mem_union] at occurrence_mem
  rcases occurrence_mem with old_mem | replacement_mem
  · exact node_normal occurrence (Finset.mem_of_mem_erase old_mem)
  · exact replacement_normal occurrence (by simpa using replacement_mem)

theorem step_inStrictNormalForm {node : Node Atom} (normal : node.InStrictNormalForm) :
    node.step.InStrictNormalForm := by
  intro occurrence occurrence_mem
  change occurrence ∈ node.stepLabel at occurrence_mem
  simp only [stepLabel, Finset.mem_union] at occurrence_mem
  rcases occurrence_mem with unmarked_mem | marked_mem
  · exact normal occurrence (Finset.mem_filter.mp unmarked_mem).1
  · rcases Finset.mem_image.mp marked_mem with ⟨source, source_mem, rfl⟩
    exact (Occurrence.inStrictNormalForm_unmark source).mpr
      (normal source (Finset.mem_filter.mp source_mem).1)

theorem satisfiedBy_of_replace {node : Node Atom} {selected : Occurrence Atom}
    {replacement : List (Occurrence Atom)} {semantics : AtomicSemantics Atom}
    {signal : Signal semantics}
    (child : (node.replace selected replacement).SatisfiedBy semantics signal)
    (replacement_entails :
      (∀ occurrence ∈ replacement,
          occurrence.SatisfiedBy semantics signal node.time) →
        selected.SatisfiedBy semantics signal node.time) :
    node.SatisfiedBy semantics signal := by
  intro occurrence occurrence_mem
  by_cases equal : occurrence = selected
  · subst occurrence
    apply replacement_entails
    intro replacementOccurrence replacement_mem
    apply child replacementOccurrence
    change replacementOccurrence ∈
      node.label.erase selected ∪ replacement.toFinset
    simp only [Finset.mem_union, List.mem_toFinset]
    exact Or.inr replacement_mem
  · apply child occurrence
    change occurrence ∈ node.label.erase selected ∪ replacement.toFinset
    simp only [Finset.mem_union]
    exact Or.inl (Finset.mem_erase.mpr ⟨equal, occurrence_mem⟩)

theorem hasModel_of_step {node : Node Atom} {semantics : AtomicSemantics Atom}
    (notRejected : ¬node.Rejected semantics) (poised : node.Poised)
    (timely : node.Timely) (normal : node.InStrictNormalForm)
    (child_model : node.step.HasModel semantics) :
    node.HasModel semantics := by
  rcases child_model with ⟨⟨signal, child_satisfied⟩⟩
  have locallyConsistent : node.LocallyConsistent semantics := by
    by_contra inconsistent
    exact notRejected (Or.inr inconsistent)
  rcases locallyConsistent with ⟨valuation, valuation_satisfies⟩
  let updatedSignal : Signal semantics := Function.update signal node.time valuation
  have child_satisfied_updated : node.step.SatisfiedBy semantics updatedSignal := by
    intro occurrence occurrence_mem
    have old := child_satisfied occurrence occurrence_mem
    apply (Occurrence.satisfiedBy_congr_of_eqOn_ge occurrence semantics
      (time := node.time + 1) ?_).mp old
    intro instant instant_ge
    simp only [updatedSignal]
    simp [Function.update, show instant ≠ node.time by omega]
  refine ⟨⟨updatedSignal, ?_⟩⟩
  intro occurrence occurrence_mem
  have occurrence_timely := timely occurrence occurrence_mem
  have occurrence_normal := normal occurrence occurrence_mem
  cases occurrence with
  | unmarked formula =>
      cases formula with
      | truth => simp [Occurrence.SatisfiedBy, Formula.SatisfiesFrom]
      | atom proposition =>
          have literal := valuation_satisfies (.unmarked (.atom proposition)) occurrence_mem
          simpa [Occurrence.SatisfiedBy, Formula.SatisfiesFrom,
            Occurrence.LiteralSatisfied, updatedSignal] using literal
      | neg body =>
          cases body with
          | truth =>
              exfalso
              apply notRejected
              exact Or.inl occurrence_mem
          | atom proposition =>
              have literal := valuation_satisfies
                (.unmarked (.neg (.atom proposition))) occurrence_mem
              simpa [Occurrence.SatisfiedBy, Formula.SatisfiesFrom,
                Occurrence.LiteralSatisfied, updatedSignal] using literal
          | neg body =>
              simp [Occurrence.InStrictNormalForm, Formula.InStrictNormalForm] at occurrence_normal
          | and left right =>
              simp [Occurrence.InStrictNormalForm, Formula.InStrictNormalForm] at occurrence_normal
          | or left right =>
              simp [Occurrence.InStrictNormalForm, Formula.InStrictNormalForm] at occurrence_normal
          | eventually interval body =>
              simp [Occurrence.InStrictNormalForm, Formula.InStrictNormalForm] at occurrence_normal
          | always interval body =>
              simp [Occurrence.InStrictNormalForm, Formula.InStrictNormalForm] at occurrence_normal
          | strictUntil interval left right =>
              simp [Occurrence.InStrictNormalForm, Formula.InStrictNormalForm] at occurrence_normal
          | strictRelease interval left right =>
              simp [Occurrence.InStrictNormalForm, Formula.InStrictNormalForm] at occurrence_normal
      | and left right =>
          exfalso
          apply poised
          exact ⟨_, Expansion.conjunction left right occurrence_mem⟩
      | or left right =>
          exfalso
          apply poised
          exact ⟨_, Expansion.disjunction left right occurrence_mem⟩
      | eventually interval body =>
          have beforeLower : node.time < interval.lower := by
            by_contra notBefore
            have active : interval.lower ≤ node.time := by omega
            have upper := occurrence_timely
            simp only [Occurrence.Timely, Formula.Timely] at upper
            apply poised
            by_cases beforeEnd : node.time < interval.upper
            · exact ⟨_, Expansion.eventuallyBeforeEnd interval body occurrence_mem active beforeEnd⟩
            · have atEnd : node.time = interval.upper := by omega
              exact ⟨_, Expansion.eventuallyAtEnd interval body occurrence_mem atEnd⟩
          have child_occurrence :
              Occurrence.unmarked (.eventually interval body) ∈ node.step.label := by
            change Occurrence.unmarked (.eventually interval body) ∈ node.stepLabel
            apply Finset.mem_union.mpr
            left
            apply Finset.mem_filter.mpr
            exact ⟨occurrence_mem, by simp [Occurrence.isUnmarkedTemporal, Formula.isTemporal]⟩
          have later := child_satisfied_updated _ child_occurrence
          simp only [Occurrence.SatisfiedBy, step] at later
          simp only [Occurrence.SatisfiedBy]
          exact Formula.eventually_later later
      | always interval body =>
          have beforeLower : node.time < interval.lower := by
            by_contra notBefore
            have active : interval.lower ≤ node.time := by omega
            have upper := occurrence_timely
            simp only [Occurrence.Timely, Formula.Timely] at upper
            apply poised
            by_cases beforeEnd : node.time < interval.upper
            · exact ⟨_, Expansion.alwaysBeforeEnd interval body occurrence_mem active beforeEnd⟩
            · have atEnd : node.time = interval.upper := by omega
              exact ⟨_, Expansion.alwaysAtEnd interval body occurrence_mem atEnd⟩
          have child_occurrence :
              Occurrence.unmarked (.always interval body) ∈ node.step.label := by
            change Occurrence.unmarked (.always interval body) ∈ node.stepLabel
            apply Finset.mem_union.mpr
            left
            exact Finset.mem_filter.mpr
              ⟨occurrence_mem, by simp [Occurrence.isUnmarkedTemporal, Formula.isTemporal]⟩
          have later := child_satisfied_updated _ child_occurrence
          simp only [Occurrence.SatisfiedBy, step] at later
          simp only [Occurrence.SatisfiedBy]
          exact Formula.always_beforeLower beforeLower later
      | strictUntil interval invariant target =>
          have beforeLower : node.time < interval.lower := by
            by_contra notBefore
            have active : interval.lower ≤ node.time := by omega
            have upper := occurrence_timely
            simp only [Occurrence.Timely, Formula.Timely] at upper
            apply poised
            by_cases beforeEnd : node.time < interval.upper
            · exact ⟨_, Expansion.strictUntilBeforeEnd interval invariant target
                occurrence_mem active beforeEnd⟩
            · have atEnd : node.time = interval.upper := by omega
              exact ⟨_, Expansion.strictUntilAtEnd interval invariant target occurrence_mem atEnd⟩
          have child_occurrence :
              Occurrence.unmarked (.strictUntil interval invariant target) ∈ node.step.label := by
            change Occurrence.unmarked (.strictUntil interval invariant target) ∈ node.stepLabel
            apply Finset.mem_union.mpr
            left
            exact Finset.mem_filter.mpr
              ⟨occurrence_mem, by simp [Occurrence.isUnmarkedTemporal, Formula.isTemporal]⟩
          have later := child_satisfied_updated _ child_occurrence
          simp only [Occurrence.SatisfiedBy, step] at later
          simp only [Occurrence.SatisfiedBy]
          exact Formula.strictUntil_beforeLower beforeLower later
      | strictRelease interval target invariant =>
          have beforeLower : node.time < interval.lower := by
            by_contra notBefore
            have active : interval.lower ≤ node.time := by omega
            have upper := occurrence_timely
            simp only [Occurrence.Timely, Formula.Timely] at upper
            apply poised
            by_cases beforeEnd : node.time < interval.upper
            · exact ⟨_, Expansion.strictReleaseBeforeEnd interval target invariant
                occurrence_mem active beforeEnd⟩
            · have atEnd : node.time = interval.upper := by omega
              exact ⟨_, Expansion.strictReleaseAtEnd interval target invariant occurrence_mem atEnd⟩
          have child_occurrence :
              Occurrence.unmarked (.strictRelease interval target invariant) ∈ node.step.label := by
            change Occurrence.unmarked (.strictRelease interval target invariant) ∈ node.stepLabel
            apply Finset.mem_union.mpr
            left
            exact Finset.mem_filter.mpr
              ⟨occurrence_mem, by simp [Occurrence.isUnmarkedTemporal, Formula.isTemporal]⟩
          have later := child_satisfied_updated _ child_occurrence
          simp only [Occurrence.SatisfiedBy, step] at later
          simp only [Occurrence.SatisfiedBy]
          exact Formula.strictRelease_beforeLower beforeLower later
  | markedEventually interval body =>
      have beforeEnd := occurrence_timely
      simp only [Occurrence.Timely] at beforeEnd
      have child_occurrence :
          Occurrence.unmarked (.eventually interval body) ∈ node.step.label := by
        change Occurrence.unmarked (.eventually interval body) ∈ node.stepLabel
        apply Finset.mem_union.mpr
        right
        apply Finset.mem_image.mpr
        refine ⟨.markedEventually interval body, ?_, rfl⟩
        exact Finset.mem_filter.mpr
          ⟨occurrence_mem, by simp [Occurrence.markedContinuesAt, beforeEnd]⟩
      have later := child_satisfied_updated _ child_occurrence
      simpa [Occurrence.SatisfiedBy, step] using later
  | markedAlways interval body =>
      have beforeEnd := occurrence_timely
      simp only [Occurrence.Timely] at beforeEnd
      have child_occurrence :
          Occurrence.unmarked (.always interval body) ∈ node.step.label := by
        change Occurrence.unmarked (.always interval body) ∈ node.stepLabel
        apply Finset.mem_union.mpr
        right
        apply Finset.mem_image.mpr
        refine ⟨.markedAlways interval body, ?_, rfl⟩
        exact Finset.mem_filter.mpr
          ⟨occurrence_mem, by simp [Occurrence.markedContinuesAt, beforeEnd]⟩
      have later := child_satisfied_updated _ child_occurrence
      simpa [Occurrence.SatisfiedBy, step] using later
  | markedStrictUntil interval invariant target =>
      have beforeEnd := occurrence_timely
      simp only [Occurrence.Timely] at beforeEnd
      have child_occurrence :
          Occurrence.unmarked (.strictUntil interval invariant target) ∈ node.step.label := by
        change Occurrence.unmarked (.strictUntil interval invariant target) ∈ node.stepLabel
        apply Finset.mem_union.mpr
        right
        apply Finset.mem_image.mpr
        refine ⟨.markedStrictUntil interval invariant target, ?_, rfl⟩
        exact Finset.mem_filter.mpr
          ⟨occurrence_mem, by simp [Occurrence.markedContinuesAt, beforeEnd]⟩
      have later := child_satisfied_updated _ child_occurrence
      simpa [Occurrence.SatisfiedBy, step] using later
  | markedStrictRelease interval target invariant =>
      have beforeEnd := occurrence_timely
      simp only [Occurrence.Timely] at beforeEnd
      have child_occurrence :
          Occurrence.unmarked (.strictRelease interval target invariant) ∈ node.step.label := by
        change Occurrence.unmarked (.strictRelease interval target invariant) ∈ node.stepLabel
        apply Finset.mem_union.mpr
        right
        apply Finset.mem_image.mpr
        refine ⟨.markedStrictRelease interval target invariant, ?_, rfl⟩
        exact Finset.mem_filter.mpr
          ⟨occurrence_mem, by simp [Occurrence.markedContinuesAt, beforeEnd]⟩
      have later := child_satisfied_updated _ child_occurrence
      simpa [Occurrence.SatisfiedBy, step] using later

theorem hasModel_of_accepting {node : Node Atom} {semantics : AtomicSemantics Atom}
    (accepting : node.Accepting semantics) (timely : node.Timely)
    (normal : node.InStrictNormalForm) : node.HasModel semantics := by
  rcases accepting with ⟨poised, notRejected, empty⟩
  apply node.hasModel_of_step notRejected poised timely normal
  let defaultSignal : Signal semantics := fun _ => Classical.choice semantics.nonempty
  refine ⟨⟨defaultSignal, ?_⟩⟩
  intro occurrence occurrence_mem
  change occurrence ∈ node.stepLabel at occurrence_mem
  rw [empty] at occurrence_mem
  simp at occurrence_mem

end Node

namespace Expansion

variable {Atom : Type u} [DecidableEq Atom]

theorem satisfiedBy_parent {node child : Node Atom} {children : List (Node Atom)}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics}
    (expansion : Expansion node children) (child_mem : child ∈ children)
    (child_satisfied : child.SatisfiedBy semantics signal) :
    node.SatisfiedBy semantics signal := by
  cases expansion with
  | disjunction left right present =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.satisfiedBy_of_replace child_satisfied
        intro replacements
        have leftHolds := replacements (.unmarked left) (by simp)
        simp only [Occurrence.SatisfiedBy, Formula.SatisfiesFrom] at leftHolds ⊢
        exact Or.inl leftHolds
      · apply Node.satisfiedBy_of_replace child_satisfied
        intro replacements
        have rightHolds := replacements (.unmarked right) (by simp)
        simp only [Occurrence.SatisfiedBy, Formula.SatisfiesFrom] at rightHolds ⊢
        exact Or.inr rightHolds
  | conjunction left right present =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.satisfiedBy_of_replace child_satisfied
      intro replacements
      have leftHolds := replacements (.unmarked left) (by simp)
      have rightHolds := replacements (.unmarked right) (by simp)
      simpa [Occurrence.SatisfiedBy, Formula.SatisfiesFrom] using And.intro leftHolds rightHolds
  | eventuallyBeforeEnd interval body present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.satisfiedBy_of_replace child_satisfied
        intro replacements
        have bodyHolds := replacements (.unmarked (body.temporalExpansion node.time)) (by simp)
        have bodyHolds' : body.Satisfies semantics signal node.time := by
          simpa [Occurrence.SatisfiedBy] using bodyHolds
        simp only [Occurrence.SatisfiedBy]
        exact Formula.eventually_now active beforeEnd bodyHolds'
      · apply Node.satisfiedBy_of_replace child_satisfied
        intro replacements
        have later := replacements (.markedEventually interval body) (by simp)
        simp only [Occurrence.SatisfiedBy] at later ⊢
        exact Formula.eventually_later later
  | eventuallyAtEnd interval body present atEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.satisfiedBy_of_replace child_satisfied
      intro replacements
      have bodyHolds := replacements (.unmarked (body.temporalExpansion node.time)) (by simp)
      have bodyHolds' : body.Satisfies semantics signal node.time := by
        simpa [Occurrence.SatisfiedBy] using bodyHolds
      simp only [Occurrence.SatisfiedBy]
      exact Formula.eventually_atEnd atEnd bodyHolds'
  | alwaysBeforeEnd interval body present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.satisfiedBy_of_replace child_satisfied
      intro replacements
      have later := replacements (.markedAlways interval body) (by simp)
      have bodyHolds := replacements (.unmarked (body.temporalExpansion node.time)) (by simp)
      have bodyHolds' : body.Satisfies semantics signal node.time := by
        simpa [Occurrence.SatisfiedBy] using bodyHolds
      simp only [Occurrence.SatisfiedBy] at later ⊢
      exact Formula.always_now_later active bodyHolds' later
  | alwaysAtEnd interval body present atEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.satisfiedBy_of_replace child_satisfied
      intro replacements
      have bodyHolds := replacements (.unmarked (body.temporalExpansion node.time)) (by simp)
      have bodyHolds' : body.Satisfies semantics signal node.time := by
        simpa [Occurrence.SatisfiedBy] using bodyHolds
      simp only [Occurrence.SatisfiedBy]
      exact Formula.always_atEnd atEnd bodyHolds'
  | strictUntilBeforeEnd interval invariant target present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.satisfiedBy_of_replace child_satisfied
        intro replacements
        have targetHolds := replacements (.unmarked (target.temporalExpansion node.time)) (by simp)
        have targetHolds' : target.Satisfies semantics signal node.time := by
          simpa [Occurrence.SatisfiedBy] using targetHolds
        simp only [Occurrence.SatisfiedBy]
        exact Formula.strictUntil_now active beforeEnd targetHolds'
      · apply Node.satisfiedBy_of_replace child_satisfied
        intro replacements
        have later := replacements (.markedStrictUntil interval invariant target) (by simp)
        have invariantHolds := replacements
          (.unmarked (invariant.temporalExpansion node.time)) (by simp)
        have invariantHolds' : invariant.Satisfies semantics signal node.time := by
          simpa [Occurrence.SatisfiedBy] using invariantHolds
        simp only [Occurrence.SatisfiedBy] at later ⊢
        exact Formula.strictUntil_later active invariantHolds' later
  | strictUntilAtEnd interval invariant target present atEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.satisfiedBy_of_replace child_satisfied
      intro replacements
      have targetHolds := replacements (.unmarked (target.temporalExpansion node.time)) (by simp)
      have targetHolds' : target.Satisfies semantics signal node.time := by
        simpa [Occurrence.SatisfiedBy] using targetHolds
      simp only [Occurrence.SatisfiedBy]
      exact Formula.strictUntil_atEnd atEnd targetHolds'
  | strictReleaseBeforeEnd interval target invariant present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.satisfiedBy_of_replace child_satisfied
        intro replacements
        have targetHolds := replacements (.unmarked (target.temporalExpansion node.time)) (by simp)
        have invariantHolds := replacements
          (.unmarked (invariant.temporalExpansion node.time)) (by simp)
        have targetHolds' : target.Satisfies semantics signal node.time := by
          simpa [Occurrence.SatisfiedBy] using targetHolds
        have invariantHolds' : invariant.Satisfies semantics signal node.time := by
          simpa [Occurrence.SatisfiedBy] using invariantHolds
        simp only [Occurrence.SatisfiedBy]
        exact Formula.strictRelease_now active beforeEnd targetHolds' invariantHolds'
      · apply Node.satisfiedBy_of_replace child_satisfied
        intro replacements
        have later := replacements (.markedStrictRelease interval target invariant) (by simp)
        have invariantHolds := replacements
          (.unmarked (invariant.temporalExpansion node.time)) (by simp)
        have invariantHolds' : invariant.Satisfies semantics signal node.time := by
          simpa [Occurrence.SatisfiedBy] using invariantHolds
        simp only [Occurrence.SatisfiedBy] at later ⊢
        exact Formula.strictRelease_later invariantHolds' later
  | strictReleaseAtEnd interval target invariant present atEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.satisfiedBy_of_replace child_satisfied
      intro replacements
      have invariantHolds := replacements
        (.unmarked (invariant.temporalExpansion node.time)) (by simp)
      have invariantHolds' : invariant.Satisfies semantics signal node.time := by
        simpa [Occurrence.SatisfiedBy] using invariantHolds
      simp only [Occurrence.SatisfiedBy]
      exact Formula.strictRelease_atEnd atEnd invariantHolds'

theorem child_inStrictNormalForm {node child : Node Atom} {children : List (Node Atom)}
    (expansion : Expansion node children) (node_normal : node.InStrictNormalForm)
    (child_mem : child ∈ children) : child.InStrictNormalForm := by
  cases expansion with
  | disjunction left right present =>
      have selected := node_normal (.unmarked (.or left right)) present
      simp only [Occurrence.InStrictNormalForm, Formula.InStrictNormalForm] at selected
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.inStrictNormalForm_replace node_normal
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        subst occurrence
        simpa [Occurrence.InStrictNormalForm] using selected.1
      · apply Node.inStrictNormalForm_replace node_normal
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        subst occurrence
        simpa [Occurrence.InStrictNormalForm] using selected.2
  | conjunction left right present =>
      have selected := node_normal (.unmarked (.and left right)) present
      simp only [Occurrence.InStrictNormalForm, Formula.InStrictNormalForm] at selected
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.inStrictNormalForm_replace node_normal
      intro occurrence mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · simpa [Occurrence.InStrictNormalForm] using selected.1
      · simpa [Occurrence.InStrictNormalForm] using selected.2
  | eventuallyBeforeEnd interval body present active beforeEnd =>
      have selected := node_normal (.unmarked (.eventually interval body)) present
      simp only [Occurrence.InStrictNormalForm, Formula.InStrictNormalForm] at selected
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.inStrictNormalForm_replace node_normal
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        subst occurrence
        simpa [Occurrence.InStrictNormalForm] using selected
      · apply Node.inStrictNormalForm_replace node_normal
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        subst occurrence
        simpa [Occurrence.InStrictNormalForm, Formula.InStrictNormalForm] using selected
  | eventuallyAtEnd interval body present atEnd =>
      have selected := node_normal (.unmarked (.eventually interval body)) present
      simp only [Occurrence.InStrictNormalForm, Formula.InStrictNormalForm] at selected
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.inStrictNormalForm_replace node_normal
      intro occurrence mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      subst occurrence
      simpa [Occurrence.InStrictNormalForm] using selected
  | alwaysBeforeEnd interval body present active beforeEnd =>
      have selected := node_normal (.unmarked (.always interval body)) present
      simp only [Occurrence.InStrictNormalForm, Formula.InStrictNormalForm] at selected
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.inStrictNormalForm_replace node_normal
      intro occurrence mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · simpa [Occurrence.InStrictNormalForm, Formula.InStrictNormalForm] using selected
      · simpa [Occurrence.InStrictNormalForm] using selected
  | alwaysAtEnd interval body present atEnd =>
      have selected := node_normal (.unmarked (.always interval body)) present
      simp only [Occurrence.InStrictNormalForm, Formula.InStrictNormalForm] at selected
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.inStrictNormalForm_replace node_normal
      intro occurrence mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      subst occurrence
      simpa [Occurrence.InStrictNormalForm] using selected
  | strictUntilBeforeEnd interval invariant target present active beforeEnd =>
      have selected := node_normal (.unmarked (.strictUntil interval invariant target)) present
      simp only [Occurrence.InStrictNormalForm, Formula.InStrictNormalForm] at selected
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.inStrictNormalForm_replace node_normal
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        subst occurrence
        simpa [Occurrence.InStrictNormalForm] using selected.2
      · apply Node.inStrictNormalForm_replace node_normal
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl
        · simpa [Occurrence.InStrictNormalForm, Formula.InStrictNormalForm] using selected
        · simpa [Occurrence.InStrictNormalForm] using selected.1
  | strictUntilAtEnd interval invariant target present atEnd =>
      have selected := node_normal (.unmarked (.strictUntil interval invariant target)) present
      simp only [Occurrence.InStrictNormalForm, Formula.InStrictNormalForm] at selected
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.inStrictNormalForm_replace node_normal
      intro occurrence mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      subst occurrence
      simpa [Occurrence.InStrictNormalForm] using selected.2
  | strictReleaseBeforeEnd interval target invariant present active beforeEnd =>
      have selected := node_normal (.unmarked (.strictRelease interval target invariant)) present
      simp only [Occurrence.InStrictNormalForm, Formula.InStrictNormalForm] at selected
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.inStrictNormalForm_replace node_normal
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl
        · simpa [Occurrence.InStrictNormalForm] using selected.1
        · simpa [Occurrence.InStrictNormalForm] using selected.2
      · apply Node.inStrictNormalForm_replace node_normal
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl
        · simpa [Occurrence.InStrictNormalForm, Formula.InStrictNormalForm] using selected
        · simpa [Occurrence.InStrictNormalForm] using selected.2
  | strictReleaseAtEnd interval target invariant present atEnd =>
      have selected := node_normal (.unmarked (.strictRelease interval target invariant)) present
      simp only [Occurrence.InStrictNormalForm, Formula.InStrictNormalForm] at selected
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.inStrictNormalForm_replace node_normal
      intro occurrence mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      subst occurrence
      simpa [Occurrence.InStrictNormalForm] using selected.2

end Expansion

namespace BasicRule

variable {Atom : Type u} [DecidableEq Atom] {semantics : AtomicSemantics Atom}

theorem child_inStrictNormalForm {node child : Node Atom} {children : List (Node Atom)}
    (rule : BasicRule semantics node children) (node_normal : node.InStrictNormalForm)
    (child_mem : child ∈ children) : child.InStrictNormalForm := by
  cases rule with
  | expand notRejected expansion =>
      exact expansion.child_inStrictNormalForm node_normal child_mem
  | step notRejected poised hasTemporal =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      exact Node.step_inStrictNormalForm node_normal

theorem child_timely {node child : Node Atom} {children : List (Node Atom)}
    (rule : BasicRule semantics node children) (node_timely : node.Timely)
    (child_mem : child ∈ children) : child.Timely := by
  cases rule with
  | expand notRejected expansion => exact expansion.child_timely node_timely child_mem
  | step notRejected poised hasTemporal =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      exact Node.step_timely node_timely poised

theorem hasModel_parent_of_child {node child : Node Atom} {children : List (Node Atom)}
    (rule : BasicRule semantics node children) (node_timely : node.Timely)
    (node_normal : node.InStrictNormalForm) (child_mem : child ∈ children)
    (child_model : child.HasModel semantics) : node.HasModel semantics := by
  cases rule with
  | expand notRejected expansion =>
      rcases child_model with ⟨⟨signal, child_satisfied⟩⟩
      exact ⟨⟨signal, expansion.satisfiedBy_parent child_mem child_satisfied⟩⟩
  | step notRejected poised hasTemporal =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      exact Node.hasModel_of_step notRejected poised node_timely node_normal child_model

end BasicRule

namespace TableauTree

variable {Atom : Type u} [DecidableEq Atom] {semantics : AtomicSemantics Atom}

theorem root_hasModel_of_acceptingLeaf (tree : TableauTree Atom)
    (wellFormed : tree.WellFormed semantics)
    (accepting : tree.HasAcceptingLeaf semantics)
    (timely : tree.root.Timely) (normal : tree.root.InStrictNormalForm) :
    tree.root.HasModel semantics := by
  induction tree with
  | leaf node =>
      exact Node.hasModel_of_accepting accepting timely normal
  | unary node child ih =>
      rcases wellFormed with ⟨rule, child_wellFormed⟩
      have child_mem : child.root ∈ [child.root] := by simp
      have child_timely := rule.child_timely timely child_mem
      have child_normal := rule.child_inStrictNormalForm normal child_mem
      have child_model := ih child_wellFormed accepting child_timely child_normal
      exact rule.hasModel_parent_of_child timely normal child_mem child_model
  | binary node satisfy postpone ihSatisfy ihPostpone =>
      rcases wellFormed with ⟨rule, satisfy_wellFormed, postpone_wellFormed⟩
      rcases accepting with satisfy_accepting | postpone_accepting
      · have child_mem : satisfy.root ∈ [satisfy.root, postpone.root] := by simp
        have child_timely := rule.child_timely timely child_mem
        have child_normal := rule.child_inStrictNormalForm normal child_mem
        have child_model := ihSatisfy satisfy_wellFormed satisfy_accepting child_timely child_normal
        exact rule.hasModel_parent_of_child timely normal child_mem child_model
      · have child_mem : postpone.root ∈ [satisfy.root, postpone.root] := by simp
        have child_timely := rule.child_timely timely child_mem
        have child_normal := rule.child_inStrictNormalForm normal child_mem
        have child_model :=
          ihPostpone postpone_wellFormed postpone_accepting child_timely child_normal
        exact rule.hasModel_parent_of_child timely normal child_mem child_model

end TableauTree

namespace Formula

variable {Atom : Type u}

/-- A semantic model of a formula is a model of its singleton initial node. -/
abbrev Model (formula : Formula Atom) (semantics : AtomicSemantics Atom)
    [DecidableEq Atom] :=
  (Node.initial formula).Model semantics

/-- A formula has a semantic model. -/
def HasModel (formula : Formula Atom) (semantics : AtomicSemantics Atom)
    [DecidableEq Atom] : Prop :=
  Nonempty (formula.Model semantics)

@[simp]
theorem satisfiesFrom_zero (formula : Formula Atom) (semantics : AtomicSemantics Atom)
    (signal : Signal semantics) :
    formula.SatisfiesFrom semantics signal 0 ↔ formula.Satisfies semantics signal 0 := by
  simpa using satisfiesFrom_temporalExpansion formula semantics signal 0

theorem satisfiable_iff_hasModel (formula : Formula Atom) (semantics : AtomicSemantics Atom)
    [DecidableEq Atom] :
    formula.Satisfiable semantics ↔ formula.HasModel semantics := by
  constructor
  · rintro ⟨signal, satisfies⟩
    refine ⟨⟨signal, ?_⟩⟩
    intro occurrence occurrence_mem
    simp only [Node.initial, Finset.mem_singleton] at occurrence_mem
    subst occurrence
    simp only [Occurrence.SatisfiedBy]
    exact (satisfiesFrom_zero formula semantics signal).mpr satisfies
  · rintro ⟨⟨signal, realizes⟩⟩
    refine ⟨signal, ?_⟩
    have root := realizes (.unmarked formula) (by simp [Node.initial])
    simp only [Occurrence.SatisfiedBy] at root
    exact (satisfiesFrom_zero formula semantics signal).mp root

end Formula

namespace BasicTableau

variable {Atom : Type u} [DecidableEq Atom] {semantics : AtomicSemantics Atom}
  {formula : Formula Atom}

/-- An accepting basic-tableau branch reconstructs a model of the input formula. -/
theorem hasModel_of_acceptingBranch (tableau : BasicTableau semantics formula)
    (accepted : tableau.HasAcceptingBranch) : formula.HasModel semantics := by
  have root_timely : tableau.tree.root.Timely := by
    rw [tableau.rooted_at]
    exact Node.initial_timely formula
  have root_normal : tableau.tree.root.InStrictNormalForm := by
    rw [tableau.rooted_at]
    intro occurrence occurrence_mem
    simp only [Node.initial, Finset.mem_singleton] at occurrence_mem
    subst occurrence
    simpa [Occurrence.InStrictNormalForm] using tableau.root_normal
  have root_model := TableauTree.root_hasModel_of_acceptingLeaf tableau.tree
    tableau.wellFormed accepted root_timely root_normal
  rw [tableau.rooted_at] at root_model
  exact root_model

/-- Soundness of the basic tableau: every accepted input formula is satisfiable. -/
theorem soundness (tableau : BasicTableau semantics formula)
    (accepted : tableau.HasAcceptingBranch) : formula.Satisfiable semantics :=
  (Formula.satisfiable_iff_hasModel formula semantics).mpr
    (tableau.hasModel_of_acceptingBranch accepted)

end BasicTableau
end Stlsat
