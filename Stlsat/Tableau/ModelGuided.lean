/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Tableau.SemanticsBase

/-!
# Model-guided ordinary tableau steps

This file proves the semantic decompositions used to guide ordinary expansion
and one-instant `STEP` choices in both tableau configurations.

The proof follows the model-guided descent argument from the paper. We reuse the
semantic node models introduced for soundness instead of the paper's finite
formula-set models: each expansion chooses a child realized by the same signal,
and `STEP` advances the model on that signal. The basic completeness theorem
uses these facts directly; JUMP completeness adds its target-splicing case.

The timeliness invariant is needed at `STEP`: a poised unmarked temporal
obligation must still be before its lower endpoint, and therefore persists to
the next instant. Strict release uses the Background section's dual semantics;
at its upper endpoint only its invariant is required.
-/

namespace Stlsat

universe u

namespace Formula

variable {Atom : Type u}

/-- At an active instant, a satisfied eventuality either holds now or remains satisfied next. -/
theorem eventually_now_or_later {interval : Interval} {body : Formula Atom}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics} {time : ℕ}
    (_active : interval.lower ≤ time)
    (holds : (eventually interval body).SatisfiesFrom semantics signal time) :
    body.Satisfies semantics signal time ∨
      (eventually interval body).SatisfiesFrom semantics signal (time + 1) := by
  simp only [SatisfiesFrom] at holds ⊢
  rcases holds with ⟨offset, contained, bodyHolds⟩
  rcases offset with _ | offset
  · left
    simpa using bodyHolds
  · right
    refine ⟨offset, ?_, ?_⟩
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using contained
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bodyHolds

/-- Before its lower endpoint, a satisfied eventuality remains satisfied at the next instant. -/
theorem eventually_later_of_beforeLower {interval : Interval} {body : Formula Atom}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics} {time : ℕ}
    (beforeLower : time < interval.lower)
    (holds : (eventually interval body).SatisfiesFrom semantics signal time) :
    (eventually interval body).SatisfiesFrom semantics signal (time + 1) := by
  simp only [SatisfiesFrom] at holds ⊢
  rcases holds with ⟨offset, contained, bodyHolds⟩
  rcases offset with _ | offset
  · simp [Interval.Contains] at contained
    omega
  · refine ⟨offset, ?_, ?_⟩
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using contained
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bodyHolds

/-- An active invariant holds now and remains an invariant at the next instant. -/
theorem always_now_and_later {interval : Interval} {body : Formula Atom}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics} {time : ℕ}
    (active : interval.lower ≤ time) (beforeEnd : time < interval.upper)
    (holds : (always interval body).SatisfiesFrom semantics signal time) :
    body.Satisfies semantics signal time ∧
      (always interval body).SatisfiesFrom semantics signal (time + 1) := by
  simp only [SatisfiesFrom] at holds ⊢
  constructor
  · simpa using holds 0 (by simp [Interval.Contains]; omega)
  · intro offset contained
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      holds (offset + 1) (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using contained)

/-- Before its lower endpoint, an always obligation remains satisfied at the next instant. -/
theorem always_later_of_beforeLower {interval : Interval} {body : Formula Atom}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics} {time : ℕ}
    (_beforeLower : time < interval.lower)
    (holds : (always interval body).SatisfiesFrom semantics signal time) :
    (always interval body).SatisfiesFrom semantics signal (time + 1) := by
  simp only [SatisfiesFrom] at holds ⊢
  intro offset contained
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    holds (offset + 1) (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using contained)

/--
An active strict-until obligation either reaches its target now or postpones
with its invariant.
-/
theorem strictUntil_now_or_later {interval : Interval} {invariant target : Formula Atom}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics} {time : ℕ}
    (active : interval.lower ≤ time)
    (holds : (strictUntil interval invariant target).SatisfiesFrom semantics signal time) :
    target.Satisfies semantics signal time ∨
      (invariant.Satisfies semantics signal time ∧
        (strictUntil interval invariant target).SatisfiesFrom semantics signal (time + 1)) := by
  simp only [SatisfiesFrom] at holds ⊢
  rcases holds with ⟨targetOffset, contained, targetHolds, invariantHolds⟩
  rcases targetOffset with _ | targetOffset
  · exact Or.inl (by simpa using targetHolds)
  · right
    constructor
    · simpa using invariantHolds 0 (by omega) (by omega)
    · refine ⟨targetOffset, ?_, ?_, ?_⟩
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using contained
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using targetHolds
      · intro invariantOffset lower ltTarget
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          invariantHolds (invariantOffset + 1)
            (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lower)
            (by omega)

/-- Before its lower endpoint, a strict-until obligation remains satisfied at the next instant. -/
theorem strictUntil_later_of_beforeLower {interval : Interval}
    {invariant target : Formula Atom} {semantics : AtomicSemantics Atom}
    {signal : Signal semantics} {time : ℕ}
    (beforeLower : time < interval.lower)
    (holds : (strictUntil interval invariant target).SatisfiesFrom semantics signal time) :
    (strictUntil interval invariant target).SatisfiesFrom semantics signal (time + 1) := by
  simp only [SatisfiesFrom] at holds ⊢
  rcases holds with ⟨targetOffset, contained, targetHolds, invariantHolds⟩
  rcases targetOffset with _ | targetOffset
  · simp [Interval.Contains] at contained
    omega
  · refine ⟨targetOffset, ?_, ?_, ?_⟩
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using contained
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using targetHolds
    · intro invariantOffset lower ltTarget
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        invariantHolds (invariantOffset + 1)
          (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lower)
          (by omega)

/--
An active strict-release obligation either releases now while preserving its invariant,
or preserves the invariant and remains satisfied at the next instant.
-/
theorem strictRelease_now_or_later {interval : Interval} {target invariant : Formula Atom}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics} {time : ℕ}
    (active : interval.lower ≤ time) (beforeEnd : time < interval.upper)
    (holds : (strictRelease interval target invariant).SatisfiesFrom semantics signal time) :
    (target.Satisfies semantics signal time ∧ invariant.Satisfies semantics signal time) ∨
      (invariant.Satisfies semantics signal time ∧
        (strictRelease interval target invariant).SatisfiesFrom semantics signal (time + 1)) := by
  classical
  simp only [SatisfiesFrom] at holds
  have invariantNow : invariant.Satisfies semantics signal time := by
    by_contra invariantFails
    apply holds
    refine ⟨0, ?_, ?_, ?_⟩
    · simp [Interval.Contains]
      omega
    · simpa using invariantFails
    · intro targetOffset _ impossible
      omega
  by_cases targetNow : target.Satisfies semantics signal time
  · exact Or.inl ⟨targetNow, invariantNow⟩
  · right
    refine ⟨invariantNow, ?_⟩
    simp only [SatisfiesFrom]
    rintro ⟨violatingOffset, contained, invariantFails, targetsFail⟩
    apply holds
    refine ⟨violatingOffset + 1, ?_, ?_, ?_⟩
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using contained
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using invariantFails
    · intro targetOffset lower ltViolating
      rcases targetOffset with _ | targetOffset
      · simpa using targetNow
      · exact (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            targetsFail targetOffset
              (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lower)
              (by omega))

/-- Before its lower endpoint, a strict-release obligation remains satisfied at the next instant. -/
theorem strictRelease_later_of_beforeLower {interval : Interval}
    {target invariant : Formula Atom} {semantics : AtomicSemantics Atom}
    {signal : Signal semantics} {time : ℕ}
    (beforeLower : time < interval.lower)
    (holds : (strictRelease interval target invariant).SatisfiesFrom semantics signal time) :
    (strictRelease interval target invariant).SatisfiesFrom semantics signal (time + 1) := by
  simp only [SatisfiesFrom] at holds ⊢
  rintro ⟨violatingOffset, contained, invariantFails, targetsFail⟩
  apply holds
  refine ⟨violatingOffset + 1, ?_, ?_, ?_⟩
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using contained
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using invariantFails
  · intro targetOffset lower ltViolating
    rcases targetOffset with _ | targetOffset
    · omega
    · exact (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          targetsFail targetOffset
            (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lower)
            (by omega))

/-- At its upper endpoint, an eventuality is equivalent to its body at the current instant. -/
theorem eventually_atEnd_iff {interval : Interval} {body : Formula Atom}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics} {time : ℕ}
    (atEnd : time = interval.upper) :
    (eventually interval body).SatisfiesFrom semantics signal time ↔
      body.Satisfies semantics signal time := by
  constructor
  · simp only [SatisfiesFrom]
    rintro ⟨offset, contained, bodyHolds⟩
    have : offset = 0 := by
      simp [Interval.Contains] at contained
      omega
    subst offset
    simpa using bodyHolds
  · exact eventually_atEnd atEnd

/-- At its upper endpoint, an always obligation is equivalent to its body now. -/
theorem always_atEnd_iff {interval : Interval} {body : Formula Atom}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics} {time : ℕ}
    (atEnd : time = interval.upper) :
    (always interval body).SatisfiesFrom semantics signal time ↔
      body.Satisfies semantics signal time := by
  constructor
  · intro holds
    simp only [SatisfiesFrom] at holds
    simpa using holds 0 (by simp [Interval.Contains]; have := interval.lower_le_upper; omega)
  · exact always_atEnd atEnd

/-- At its upper endpoint, strict until is equivalent to its target now. -/
theorem strictUntil_atEnd_iff {interval : Interval} {invariant target : Formula Atom}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics} {time : ℕ}
    (atEnd : time = interval.upper) :
    (strictUntil interval invariant target).SatisfiesFrom semantics signal time ↔
      target.Satisfies semantics signal time := by
  constructor
  · simp only [SatisfiesFrom]
    rintro ⟨offset, contained, targetHolds, invariantHolds⟩
    have : offset = 0 := by
      simp [Interval.Contains] at contained
      omega
    subst offset
    simpa using targetHolds
  · exact strictUntil_atEnd atEnd

/-- At its upper endpoint, strict release is equivalent to its invariant now. -/
theorem strictRelease_atEnd_iff {interval : Interval} {target invariant : Formula Atom}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics} {time : ℕ}
    (atEnd : time = interval.upper) :
    (strictRelease interval target invariant).SatisfiesFrom semantics signal time ↔
      invariant.Satisfies semantics signal time := by
  constructor
  · intro holds
    simp only [SatisfiesFrom] at holds
    by_contra invariantFails
    apply holds
    refine ⟨0, ?_, ?_, ?_⟩
    · simp [Interval.Contains]
      have := interval.lower_le_upper
      omega
    · simpa using invariantFails
    · omega
  · exact strictRelease_atEnd atEnd

end Formula

namespace ObligationSet

variable {Atom : Type u} [DecidableEq Atom]

/-- Replacing an occurrence by obligations true on the same signal preserves node satisfaction. -/
theorem satisfiedBy_replace_of {node : ObligationSet Atom} {selected : Occurrence Atom}
    {replacement : List (Occurrence Atom)} {semantics : AtomicSemantics Atom}
    {signal : Signal semantics} (parent : node.SatisfiedBy semantics signal)
    (replacementHolds : ∀ occurrence ∈ replacement,
      occurrence.SatisfiedBy semantics signal node.time) :
    (node.replace selected replacement).SatisfiedBy semantics signal := by
  intro occurrence occurrence_mem
  change occurrence ∈ node.label.erase selected ∪ replacement.toFinset at occurrence_mem
  rw [Finset.mem_union] at occurrence_mem
  rcases occurrence_mem with old_mem | replacement_mem
  · exact parent occurrence (Finset.mem_of_mem_erase old_mem)
  · exact replacementHolds occurrence (by simpa using replacement_mem)

omit [DecidableEq Atom] in
/-- A semantic model rules out both rejection conditions at its node. -/
theorem notRejected_of_model {node : ObligationSet Atom} {semantics : AtomicSemantics Atom}
    (model : node.Model semantics) : ¬node.Rejected semantics := by
  rintro (falsePresent | inconsistent)
  · have impossible := model.satisfies (.unmarked (.neg .truth)) falsePresent
    simp only [Occurrence.SatisfiedBy, Formula.SatisfiesFrom] at impossible
    exact impossible trivial
  · apply inconsistent
    refine ⟨model.signal node.time, ?_⟩
    intro occurrence occurrence_mem
    cases occurrence with
    | unmarked formula =>
        cases formula with
        | atom proposition =>
            simpa [Occurrence.LiteralSatisfied, Occurrence.SatisfiedBy,
              Formula.SatisfiesFrom] using model.satisfies _ occurrence_mem
        | neg body =>
            cases body with
            | atom proposition =>
                simpa [Occurrence.LiteralSatisfied, Occurrence.SatisfiedBy,
                  Formula.SatisfiesFrom] using model.satisfies _ occurrence_mem
            | _ => simp [Occurrence.LiteralSatisfied]
        | _ => simp [Occurrence.LiteralSatisfied]
    | _ => simp [Occurrence.LiteralSatisfied]

omit [DecidableEq Atom] in
/-- A node possessing a semantic model cannot be rejected. -/
theorem notRejected_of_hasModel {node : ObligationSet Atom} {semantics : AtomicSemantics Atom}
    (model : node.HasModel semantics) : ¬node.Rejected semantics := by
  rcases model with ⟨model⟩
  exact notRejected_of_model model

/-- Satisfaction advances through `STEP` on the same signal at a timely poised node. -/
theorem satisfiedBy_step_of_satisfiedBy {node : ObligationSet Atom}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics}
    (ready : node.Ready) (timely : node.Timely)
    (parent : node.SatisfiedBy semantics signal) :
    node.step.SatisfiedBy semantics signal := by
  intro occurrence occurrence_mem
  change occurrence ∈ node.stepLabel at occurrence_mem
  simp only [stepLabel, Finset.mem_union] at occurrence_mem
  rcases occurrence_mem with unmarked_mem | marked_mem
  · have source_mem := (Finset.mem_filter.mp unmarked_mem).1
    have temporal := (Finset.mem_filter.mp unmarked_mem).2
    have sourceHolds := parent occurrence source_mem
    have sourceTimely := timely occurrence source_mem
    cases occurrence with
    | unmarked formula =>
        cases formula with
        | truth => simp [Occurrence.isUnmarkedTemporal, Formula.isTemporal] at temporal
        | atom proposition => simp [Occurrence.isUnmarkedTemporal, Formula.isTemporal] at temporal
        | neg body => simp [Occurrence.isUnmarkedTemporal, Formula.isTemporal] at temporal
        | and left right => simp [Occurrence.isUnmarkedTemporal, Formula.isTemporal] at temporal
        | or left right => simp [Occurrence.isUnmarkedTemporal, Formula.isTemporal] at temporal
        | eventually interval body =>
            have beforeLower : node.time < interval.lower := by
              simpa [ObligationSet.Ready] using
                ready (.unmarked (.eventually interval body)) source_mem
            have later := Formula.eventually_later_of_beforeLower beforeLower sourceHolds
            simpa [Occurrence.SatisfiedBy, step] using later
        | always interval body =>
            have beforeLower : node.time < interval.lower := by
              simpa [ObligationSet.Ready] using
                ready (.unmarked (.always interval body)) source_mem
            have later := Formula.always_later_of_beforeLower beforeLower sourceHolds
            simpa [Occurrence.SatisfiedBy, step] using later
        | strictUntil interval invariant target =>
            have beforeLower : node.time < interval.lower := by
              simpa [ObligationSet.Ready] using
                ready (.unmarked (.strictUntil interval invariant target)) source_mem
            have later := Formula.strictUntil_later_of_beforeLower beforeLower sourceHolds
            simpa [Occurrence.SatisfiedBy, step] using later
        | strictRelease interval target invariant =>
            have beforeLower : node.time < interval.lower := by
              simpa [ObligationSet.Ready] using
                ready (.unmarked (.strictRelease interval target invariant)) source_mem
            have later := Formula.strictRelease_later_of_beforeLower beforeLower sourceHolds
            simpa [Occurrence.SatisfiedBy, step] using later
    | markedEventually interval body =>
        simp [Occurrence.isUnmarkedTemporal] at temporal
    | markedAlways interval body =>
        simp [Occurrence.isUnmarkedTemporal] at temporal
    | markedStrictUntil interval invariant target =>
        simp [Occurrence.isUnmarkedTemporal] at temporal
    | markedStrictRelease interval target invariant =>
        simp [Occurrence.isUnmarkedTemporal] at temporal
  · rcases Finset.mem_image.mp marked_mem with ⟨source, source_mem, rfl⟩
    have source_mem' := (Finset.mem_filter.mp source_mem).1
    have continues := (Finset.mem_filter.mp source_mem).2
    have sourceHolds := parent source source_mem'
    cases source with
    | unmarked formula => simp [Occurrence.markedContinuesAt] at continues
    | markedEventually interval body =>
        simpa [Occurrence.SatisfiedBy, Occurrence.unmark, step] using sourceHolds
    | markedAlways interval body =>
        simpa [Occurrence.SatisfiedBy, Occurrence.unmark, step] using sourceHolds
    | markedStrictUntil interval invariant target =>
        simpa [Occurrence.SatisfiedBy, Occurrence.unmark, step] using sourceHolds
    | markedStrictRelease interval target invariant =>
        simpa [Occurrence.SatisfiedBy, Occurrence.unmark, step] using sourceHolds

/-- Advance a semantic node model through `STEP` without changing its signal. -/
def model_step {node : ObligationSet Atom} {semantics : AtomicSemantics Atom}
    (ready : node.Ready) (timely : node.Timely) (model : node.Model semantics) :
    node.step.Model semantics :=
  ⟨model.signal, satisfiedBy_step_of_satisfiedBy ready timely model.satisfies⟩

end ObligationSet

end Stlsat
