/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Semantics
import Stlsat.Tableau.Timing

/-!
# Semantic obligation models

This file gives the common semantic interpretation of the unannotated
obligation projection used by both tableau configurations.

The paper presents a model as a finite sequence of formula sets closed under
the tableau expansion laws. Taken literally, its clauses do not constrain
temporal formulas in the last set: choosing a sequence of length zero would,
for example, make `F_[1,1] ¬⊤` a model. Its stated local-consistency condition
also omits time zero. We instead give the corrected proof obligations a
semantic representation. `Formula.SatisfiesFrom` interprets an absolute-time
formula in a tableau label from the node's current time, and `ObligationSet.Model`
contains one signal realizing every occurrence in the label. Marked
occurrences are the residual temporal obligation starting at the next
instant. This retains the paper's proof structure while allowing both rule
configurations to share the semantic layer.

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

namespace ObligationSet

variable {Atom : Type u} [DecidableEq Atom]

/-- One signal realizes every proof obligation in the node label. -/
def SatisfiedBy (node : ObligationSet Atom) (semantics : AtomicSemantics Atom)
    (signal : Signal semantics) : Prop :=
  ∀ occurrence ∈ node.label, occurrence.SatisfiedBy semantics signal node.time

/-- A semantic model of all the proof obligations stored in a tableau node. -/
structure Model (node : ObligationSet Atom) (semantics : AtomicSemantics Atom) where
  /-- The signal reconstructed from the branch suffix rooted at this node. -/
  signal : Signal semantics
  /-- Every marked or unmarked occurrence in the node is realized by `signal`. -/
  satisfies : node.SatisfiedBy semantics signal

/-- A tableau node has a semantic model. -/
def HasModel (node : ObligationSet Atom) (semantics : AtomicSemantics Atom) : Prop :=
  Nonempty (node.Model semantics)

/-- Every formula occurrence in a node is in strict normal form. -/
def InStrictNormalForm (node : ObligationSet Atom) : Prop :=
  ∀ occurrence ∈ node.label, occurrence.InStrictNormalForm

theorem inStrictNormalForm_replace {node : ObligationSet Atom} {selected : Occurrence Atom}
    {replacement : List (Occurrence Atom)} (node_normal : node.InStrictNormalForm)
    (replacement_normal : ∀ occurrence ∈ replacement, occurrence.InStrictNormalForm) :
    (node.replace selected replacement).InStrictNormalForm := by
  intro occurrence occurrence_mem
  change occurrence ∈ node.label.erase selected ∪ replacement.toFinset at occurrence_mem
  rw [Finset.mem_union] at occurrence_mem
  rcases occurrence_mem with old_mem | replacement_mem
  · exact node_normal occurrence (Finset.mem_of_mem_erase old_mem)
  · exact replacement_normal occurrence (by simpa using replacement_mem)

theorem step_inStrictNormalForm {node : ObligationSet Atom} (normal : node.InStrictNormalForm) :
    node.step.InStrictNormalForm := by
  intro occurrence occurrence_mem
  change occurrence ∈ node.stepLabel at occurrence_mem
  simp only [stepLabel, Finset.mem_union] at occurrence_mem
  rcases occurrence_mem with unmarked_mem | marked_mem
  · exact normal occurrence (Finset.mem_filter.mp unmarked_mem).1
  · rcases Finset.mem_image.mp marked_mem with ⟨source, source_mem, rfl⟩
    exact (Occurrence.inStrictNormalForm_unmark source).mpr
      (normal source (Finset.mem_filter.mp source_mem).1)

theorem satisfiedBy_of_replace {node : ObligationSet Atom} {selected : Occurrence Atom}
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

theorem hasModel_of_step {node : ObligationSet Atom} {semantics : AtomicSemantics Atom}
    (notRejected : ¬node.Rejected semantics) (ready : node.Ready)
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
          simpa [ObligationSet.Ready] using
            ready (.unmarked (.and left right)) occurrence_mem
      | or left right =>
          exfalso
          simpa [ObligationSet.Ready] using
            ready (.unmarked (.or left right)) occurrence_mem
      | eventually interval body =>
          have beforeLower : node.time < interval.lower := by
            simpa [ObligationSet.Ready] using
              ready (.unmarked (.eventually interval body)) occurrence_mem
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
            simpa [ObligationSet.Ready] using
              ready (.unmarked (.always interval body)) occurrence_mem
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
            simpa [ObligationSet.Ready] using
              ready (.unmarked (.strictUntil interval invariant target)) occurrence_mem
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
            simpa [ObligationSet.Ready] using
              ready (.unmarked (.strictRelease interval target invariant)) occurrence_mem
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

end ObligationSet
namespace Formula

variable {Atom : Type u}

/-- A semantic model of a formula is a model of its singleton initial node. -/
abbrev Model (formula : Formula Atom) (semantics : AtomicSemantics Atom)
    [DecidableEq Atom] :=
  (ObligationSet.initial formula).Model semantics

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
    simp only [ObligationSet.initial, Finset.mem_singleton] at occurrence_mem
    subst occurrence
    simp only [Occurrence.SatisfiedBy]
    exact (satisfiesFrom_zero formula semantics signal).mpr satisfies
  · rintro ⟨⟨signal, realizes⟩⟩
    refine ⟨signal, ?_⟩
    have root := realizes (.unmarked formula) (by simp [ObligationSet.initial])
    simp only [Occurrence.SatisfiedBy] at root
    exact (satisfiesFrom_zero formula semantics signal).mp root

end Formula

end Stlsat
