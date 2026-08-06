/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Soundness

/-!
# Completeness of the basic STL tableau

This file proves that every satisfiable strict-normal-form input has an accepting
branch in any fully developed basic tableau. The `JUMP` rule is deliberately
outside this development.

The proof follows the model-guided descent argument from the paper. We reuse the
semantic node models introduced for soundness instead of the paper's finite
formula-set models: each expansion chooses a child realized by the same signal,
and `STEP` advances the model on that signal. A modeled node cannot be rejected,
so structural induction over the finite, frontier-terminal tableau tree reaches
an accepting leaf.

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

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

/-- Replacing an occurrence by obligations true on the same signal preserves node satisfaction. -/
theorem satisfiedBy_replace_of {node : Node Atom} {selected : Occurrence Atom}
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
theorem notRejected_of_model {node : Node Atom} {semantics : AtomicSemantics Atom}
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
theorem notRejected_of_hasModel {node : Node Atom} {semantics : AtomicSemantics Atom}
    (model : node.HasModel semantics) : ¬node.Rejected semantics := by
  rcases model with ⟨model⟩
  exact notRejected_of_model model

/-- Satisfaction advances through `STEP` on the same signal at a timely poised node. -/
theorem satisfiedBy_step_of_satisfiedBy {node : Node Atom}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics}
    (poised : node.Poised) (timely : node.Timely)
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
              by_contra notBefore
              have active : interval.lower ≤ node.time := by omega
              have upper : node.time ≤ interval.upper := by
                simpa [Occurrence.Timely, Formula.Timely] using sourceTimely
              apply poised
              by_cases beforeEnd : node.time < interval.upper
              · exact ⟨_, Expansion.eventuallyBeforeEnd interval body source_mem active beforeEnd⟩
              · exact ⟨_, Expansion.eventuallyAtEnd interval body source_mem (by omega)⟩
            have later := Formula.eventually_later_of_beforeLower beforeLower sourceHolds
            simpa [Occurrence.SatisfiedBy, step] using later
        | always interval body =>
            have beforeLower : node.time < interval.lower := by
              by_contra notBefore
              have active : interval.lower ≤ node.time := by omega
              have upper : node.time ≤ interval.upper := by
                simpa [Occurrence.Timely, Formula.Timely] using sourceTimely
              apply poised
              by_cases beforeEnd : node.time < interval.upper
              · exact ⟨_, Expansion.alwaysBeforeEnd interval body source_mem active beforeEnd⟩
              · exact ⟨_, Expansion.alwaysAtEnd interval body source_mem (by omega)⟩
            have later := Formula.always_later_of_beforeLower beforeLower sourceHolds
            simpa [Occurrence.SatisfiedBy, step] using later
        | strictUntil interval invariant target =>
            have beforeLower : node.time < interval.lower := by
              by_contra notBefore
              have active : interval.lower ≤ node.time := by omega
              have upper : node.time ≤ interval.upper := by
                simpa [Occurrence.Timely, Formula.Timely] using sourceTimely
              apply poised
              by_cases beforeEnd : node.time < interval.upper
              · exact ⟨_, Expansion.strictUntilBeforeEnd interval invariant target
                    source_mem active beforeEnd⟩
              · exact ⟨_, Expansion.strictUntilAtEnd interval invariant target
                    source_mem (by omega)⟩
            have later := Formula.strictUntil_later_of_beforeLower beforeLower sourceHolds
            simpa [Occurrence.SatisfiedBy, step] using later
        | strictRelease interval target invariant =>
            have beforeLower : node.time < interval.lower := by
              by_contra notBefore
              have active : interval.lower ≤ node.time := by omega
              have upper : node.time ≤ interval.upper := by
                simpa [Occurrence.Timely, Formula.Timely] using sourceTimely
              apply poised
              by_cases beforeEnd : node.time < interval.upper
              · exact ⟨_, Expansion.strictReleaseBeforeEnd interval target invariant
                    source_mem active beforeEnd⟩
              · exact ⟨_, Expansion.strictReleaseAtEnd interval target invariant
                    source_mem (by omega)⟩
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
def model_step {node : Node Atom} {semantics : AtomicSemantics Atom}
    (poised : node.Poised) (timely : node.Timely) (model : node.Model semantics) :
    node.step.Model semantics :=
  ⟨model.signal, satisfiedBy_step_of_satisfiedBy poised timely model.satisfies⟩

end Node

namespace Expansion

variable {Atom : Type u} [DecidableEq Atom]

/-- A satisfied expansion parent has a child satisfied by the same signal. -/
theorem exists_child_satisfiedBy {node : Node Atom} {children : List (Node Atom)}
    {semantics : AtomicSemantics Atom} {signal : Signal semantics}
    (expansion : Expansion node children) (parent : node.SatisfiedBy semantics signal) :
    ∃ child ∈ children, child.SatisfiedBy semantics signal := by
  cases expansion with
  | disjunction left right present =>
      have selected := parent (.unmarked (.or left right)) present
      simp only [Occurrence.SatisfiedBy, Formula.SatisfiesFrom] at selected
      rcases selected with leftHolds | rightHolds
      · refine ⟨node.replace (.unmarked (.or left right)) [.unmarked left], by simp, ?_⟩
        apply Node.satisfiedBy_replace_of parent
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        subst occurrence
        simpa [Occurrence.SatisfiedBy, Formula.SatisfiesFrom] using leftHolds
      · refine ⟨node.replace (.unmarked (.or left right)) [.unmarked right], by simp, ?_⟩
        apply Node.satisfiedBy_replace_of parent
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        subst occurrence
        simpa [Occurrence.SatisfiedBy, Formula.SatisfiesFrom] using rightHolds
  | conjunction left right present =>
      have selected := parent (.unmarked (.and left right)) present
      simp only [Occurrence.SatisfiedBy, Formula.SatisfiesFrom] at selected
      refine ⟨node.replace (.unmarked (.and left right))
        [.unmarked left, .unmarked right], by simp, ?_⟩
      apply Node.satisfiedBy_replace_of parent
      intro occurrence mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · simpa [Occurrence.SatisfiedBy, Formula.SatisfiesFrom] using selected.1
      · simpa [Occurrence.SatisfiedBy, Formula.SatisfiesFrom] using selected.2
  | eventuallyBeforeEnd interval body present active beforeEnd =>
      have selected := parent (.unmarked (.eventually interval body)) present
      simp only [Occurrence.SatisfiedBy] at selected
      rcases Formula.eventually_now_or_later active selected with now | later
      · refine ⟨node.replace (.unmarked (.eventually interval body))
          [.unmarked (body.temporalExpansion node.time)], by simp, ?_⟩
        apply Node.satisfiedBy_replace_of parent
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        subst occurrence
        simpa [Occurrence.SatisfiedBy] using now
      · refine ⟨node.replace (.unmarked (.eventually interval body))
          [.markedEventually interval body], by simp, ?_⟩
        apply Node.satisfiedBy_replace_of parent
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        subst occurrence
        simpa [Occurrence.SatisfiedBy] using later
  | eventuallyAtEnd interval body present atEnd =>
      have selected := parent (.unmarked (.eventually interval body)) present
      simp only [Occurrence.SatisfiedBy] at selected
      have now := (Formula.eventually_atEnd_iff atEnd).mp selected
      refine ⟨node.replace (.unmarked (.eventually interval body))
        [.unmarked (body.temporalExpansion node.time)], by simp, ?_⟩
      apply Node.satisfiedBy_replace_of parent
      intro occurrence mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      subst occurrence
      simpa [Occurrence.SatisfiedBy] using now
  | alwaysBeforeEnd interval body present active beforeEnd =>
      have selected := parent (.unmarked (.always interval body)) present
      simp only [Occurrence.SatisfiedBy] at selected
      rcases Formula.always_now_and_later active beforeEnd selected with ⟨now, later⟩
      refine ⟨node.replace (.unmarked (.always interval body))
        [.markedAlways interval body, .unmarked (body.temporalExpansion node.time)],
        by simp, ?_⟩
      apply Node.satisfiedBy_replace_of parent
      intro occurrence mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · simpa [Occurrence.SatisfiedBy] using later
      · simpa [Occurrence.SatisfiedBy] using now
  | alwaysAtEnd interval body present atEnd =>
      have selected := parent (.unmarked (.always interval body)) present
      simp only [Occurrence.SatisfiedBy] at selected
      have now := (Formula.always_atEnd_iff atEnd).mp selected
      refine ⟨node.replace (.unmarked (.always interval body))
        [.unmarked (body.temporalExpansion node.time)], by simp, ?_⟩
      apply Node.satisfiedBy_replace_of parent
      intro occurrence mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      subst occurrence
      simpa [Occurrence.SatisfiedBy] using now
  | strictUntilBeforeEnd interval invariant target present active beforeEnd =>
      have selected := parent (.unmarked (.strictUntil interval invariant target)) present
      simp only [Occurrence.SatisfiedBy] at selected
      rcases Formula.strictUntil_now_or_later active selected with now | ⟨invariantNow, later⟩
      · refine ⟨node.replace (.unmarked (.strictUntil interval invariant target))
          [.unmarked (target.temporalExpansion node.time)], by simp, ?_⟩
        apply Node.satisfiedBy_replace_of parent
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        subst occurrence
        simpa [Occurrence.SatisfiedBy] using now
      · refine ⟨node.replace (.unmarked (.strictUntil interval invariant target))
          [.markedStrictUntil interval invariant target,
            .unmarked (invariant.temporalExpansion node.time)], by simp, ?_⟩
        apply Node.satisfiedBy_replace_of parent
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl
        · simpa [Occurrence.SatisfiedBy] using later
        · simpa [Occurrence.SatisfiedBy] using invariantNow
  | strictUntilAtEnd interval invariant target present atEnd =>
      have selected := parent (.unmarked (.strictUntil interval invariant target)) present
      simp only [Occurrence.SatisfiedBy] at selected
      have now := (Formula.strictUntil_atEnd_iff atEnd).mp selected
      refine ⟨node.replace (.unmarked (.strictUntil interval invariant target))
        [.unmarked (target.temporalExpansion node.time)], by simp, ?_⟩
      apply Node.satisfiedBy_replace_of parent
      intro occurrence mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      subst occurrence
      simpa [Occurrence.SatisfiedBy] using now
  | strictReleaseBeforeEnd interval target invariant present active beforeEnd =>
      have selected := parent (.unmarked (.strictRelease interval target invariant)) present
      simp only [Occurrence.SatisfiedBy] at selected
      rcases Formula.strictRelease_now_or_later active beforeEnd selected with
        ⟨targetNow, invariantNow⟩ | ⟨invariantNow, later⟩
      · refine ⟨node.replace (.unmarked (.strictRelease interval target invariant))
          [.unmarked (target.temporalExpansion node.time),
            .unmarked (invariant.temporalExpansion node.time)], by simp, ?_⟩
        apply Node.satisfiedBy_replace_of parent
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl
        · simpa [Occurrence.SatisfiedBy] using targetNow
        · simpa [Occurrence.SatisfiedBy] using invariantNow
      · refine ⟨node.replace (.unmarked (.strictRelease interval target invariant))
          [.markedStrictRelease interval target invariant,
            .unmarked (invariant.temporalExpansion node.time)], by simp, ?_⟩
        apply Node.satisfiedBy_replace_of parent
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl
        · simpa [Occurrence.SatisfiedBy] using later
        · simpa [Occurrence.SatisfiedBy] using invariantNow
  | strictReleaseAtEnd interval target invariant present atEnd =>
      have selected := parent (.unmarked (.strictRelease interval target invariant)) present
      simp only [Occurrence.SatisfiedBy] at selected
      have now := (Formula.strictRelease_atEnd_iff atEnd).mp selected
      refine ⟨node.replace (.unmarked (.strictRelease interval target invariant))
        [.unmarked (invariant.temporalExpansion node.time)], by simp, ?_⟩
      apply Node.satisfiedBy_replace_of parent
      intro occurrence mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      subst occurrence
      simpa [Occurrence.SatisfiedBy] using now

/-- A modeled expansion parent has at least one modeled child. -/
theorem exists_child_hasModel {node : Node Atom} {children : List (Node Atom)}
    {semantics : AtomicSemantics Atom} (expansion : Expansion node children)
    (model : node.Model semantics) : ∃ child ∈ children, child.HasModel semantics := by
  rcases expansion.exists_child_satisfiedBy model.satisfies with
    ⟨child, child_mem, child_satisfied⟩
  exact ⟨child, child_mem, ⟨⟨model.signal, child_satisfied⟩⟩⟩

end Expansion

namespace BasicRule

variable {Atom : Type u} [DecidableEq Atom] {semantics : AtomicSemantics Atom}

/-- Every basic rule applied to a modeled timely node has a modeled child. -/
theorem exists_child_hasModel {node : Node Atom} {children : List (Node Atom)}
    (rule : BasicRule semantics node children) (timely : node.Timely)
    (_normal : node.InStrictNormalForm) (model : node.HasModel semantics) :
    ∃ child ∈ children, child.HasModel semantics := by
  rcases model with ⟨model⟩
  cases rule with
  | expand notRejected expansion =>
      exact expansion.exists_child_hasModel model
  | step notRejected poised hasTemporal =>
      exact ⟨node.step, by simp, ⟨node.model_step poised timely model⟩⟩

end BasicRule

namespace TableauTree

variable {Atom : Type u} [DecidableEq Atom] {semantics : AtomicSemantics Atom}

/-- A finite fully developed tableau tree with a modeled root contains an accepting leaf. -/
theorem hasAcceptingLeaf_of_root_hasModel (tree : TableauTree Atom)
    (wellFormed : tree.WellFormed semantics)
    (frontierTerminal : tree.FrontierTerminal semantics)
    (timely : tree.root.Timely) (normal : tree.root.InStrictNormalForm)
    (model : tree.root.HasModel semantics) : tree.HasAcceptingLeaf semantics := by
  induction tree with
  | leaf node =>
      simp only [HasAcceptingLeaf]
      simp only [FrontierTerminal] at frontierTerminal
      rcases frontierTerminal with rejected | accepting
      · exact False.elim ((Node.notRejected_of_hasModel model) rejected)
      · exact accepting
  | unary node child ih =>
      rcases wellFormed with ⟨rule, child_wellFormed⟩
      have child_mem : child.root ∈ [child.root] := by simp
      obtain ⟨modeled, modeled_mem, child_model⟩ :=
        rule.exists_child_hasModel timely normal model
      simp only [List.mem_singleton] at modeled_mem
      subst modeled
      have child_timely := rule.child_timely timely child_mem
      have child_normal := rule.child_inStrictNormalForm normal child_mem
      exact ih child_wellFormed frontierTerminal child_timely child_normal child_model
  | binary node satisfy postpone ihSatisfy ihPostpone =>
      rcases wellFormed with ⟨rule, satisfy_wellFormed, postpone_wellFormed⟩
      rcases frontierTerminal with ⟨satisfy_terminal, postpone_terminal⟩
      rcases rule.exists_child_hasModel timely normal model with
        ⟨child, child_mem, child_model⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · have child_mem : satisfy.root ∈ [satisfy.root, postpone.root] := by simp
        have child_timely := rule.child_timely timely child_mem
        have child_normal := rule.child_inStrictNormalForm normal child_mem
        exact Or.inl
          (ihSatisfy satisfy_wellFormed satisfy_terminal child_timely child_normal child_model)
      · have child_mem : postpone.root ∈ [satisfy.root, postpone.root] := by simp
        have child_timely := rule.child_timely timely child_mem
        have child_normal := rule.child_inStrictNormalForm normal child_mem
        exact Or.inr
          (ihPostpone postpone_wellFormed postpone_terminal child_timely child_normal child_model)

end TableauTree

namespace BasicTableau

variable {Atom : Type u} [DecidableEq Atom] {semantics : AtomicSemantics Atom}
  {formula : Formula Atom}

/-- A model of the input formula selects an accepting branch in its basic tableau. -/
theorem hasAcceptingBranch_of_hasModel (tableau : BasicTableau semantics formula)
    (model : formula.HasModel semantics) : tableau.HasAcceptingBranch := by
  have root_timely : tableau.tree.root.Timely := by
    rw [tableau.rooted_at]
    exact Node.initial_timely formula
  have root_normal : tableau.tree.root.InStrictNormalForm := by
    rw [tableau.rooted_at]
    intro occurrence occurrence_mem
    simp only [Node.initial, Finset.mem_singleton] at occurrence_mem
    subst occurrence
    simpa [Occurrence.InStrictNormalForm] using tableau.root_normal
  have root_model : tableau.tree.root.HasModel semantics := by
    rw [tableau.rooted_at]
    exact model
  exact TableauTree.hasAcceptingLeaf_of_root_hasModel tableau.tree tableau.wellFormed
    tableau.frontier_terminal root_timely root_normal root_model

/-- Completeness of the basic tableau: every satisfiable input has an accepting branch. -/
theorem completeness (tableau : BasicTableau semantics formula)
    (satisfiable : formula.Satisfiable semantics) : tableau.HasAcceptingBranch :=
  tableau.hasAcceptingBranch_of_hasModel
    ((Formula.satisfiable_iff_hasModel formula semantics).mp satisfiable)

end BasicTableau

end Stlsat
