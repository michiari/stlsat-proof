/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Tableau.ModelGuided
import Stlsat.Tableau.Semantics

/-!
# Model-guided completeness of ordinary tableau expansion

Ordinary propositional and temporal expansions are shared by the basic and
JUMP rule configurations.  This module proves once that a model of the parent
selects a modeled child.  It also records forward model preservation for the
ordinary one-instant `STEP`.
-/

namespace Stlsat.Tableau

universe u

namespace Expansion

variable {Atom : Type u} [DecidableEq Atom]

/-- The ordinary expansion rules retain their model-guided completeness law
with occurrence identifiers and parent annotations. -/
theorem exists_child_satisfiedBy {node : Node Atom} {children : List (Node Atom)}
    {semantics : Stlsat.AtomicSemantics Atom} {signal : Stlsat.Signal semantics}
    (expansion : Expansion node children)
    (parentHolds : node.SatisfiedBy semantics signal) :
    ∃ child ∈ children, child.SatisfiedBy semantics signal := by
  cases expansion with
  | disjunction selected left right shape present =>
      have selectedHolds := (Node.satisfiedBy_iff node semantics signal).1
        parentHolds selected present
      simp only [AnnotatedOccurrence.SatisfiedBy, shape,
        Stlsat.Occurrence.SatisfiedBy, Stlsat.Formula.SatisfiesFrom] at selectedHolds
      rcases selectedHolds with leftHolds | rightHolds
      · refine ⟨node.replace selected
          [selected.child 0 (.unmarked left) selected.parent], by simp, ?_⟩
        apply Node.satisfiedBy_replace_of parentHolds
        intro occurrence occurrenceMem
        simp only [List.mem_singleton] at occurrenceMem
        subst occurrence
        simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
          Stlsat.Occurrence.SatisfiedBy,
          Stlsat.Formula.SatisfiesFrom] using leftHolds
      · refine ⟨node.replace selected
          [selected.child 1 (.unmarked right) selected.parent], by simp, ?_⟩
        apply Node.satisfiedBy_replace_of parentHolds
        intro occurrence occurrenceMem
        simp only [List.mem_singleton] at occurrenceMem
        subst occurrence
        simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
          Stlsat.Occurrence.SatisfiedBy,
          Stlsat.Formula.SatisfiesFrom] using rightHolds
  | conjunction selected left right shape present =>
      have selectedHolds := (Node.satisfiedBy_iff node semantics signal).1
        parentHolds selected present
      simp only [AnnotatedOccurrence.SatisfiedBy, shape,
        Stlsat.Occurrence.SatisfiedBy, Stlsat.Formula.SatisfiesFrom] at selectedHolds
      refine ⟨node.replace selected
        [selected.child 0 (.unmarked left) selected.parent,
         selected.child 1 (.unmarked right) selected.parent], by simp, ?_⟩
      apply Node.satisfiedBy_replace_of parentHolds
      intro occurrence occurrenceMem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMem
      rcases occurrenceMem with rfl | rfl
      · simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
          Stlsat.Occurrence.SatisfiedBy,
          Stlsat.Formula.SatisfiesFrom] using selectedHolds.1
      · simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
          Stlsat.Occurrence.SatisfiedBy,
          Stlsat.Formula.SatisfiesFrom] using selectedHolds.2
  | eventuallyBeforeEnd selected interval body shape present active beforeEnd =>
      have selectedHolds := (Node.satisfiedBy_iff node semantics signal).1
        parentHolds selected present
      simp only [AnnotatedOccurrence.SatisfiedBy, shape,
        Stlsat.Occurrence.SatisfiedBy] at selectedHolds
      rcases Stlsat.Formula.eventually_now_or_later active selectedHolds with now | later
      · refine ⟨node.replace selected
          [selected.child 0 (.unmarked (body.temporalExpansion node.time)) none],
          by simp, ?_⟩
        apply Node.satisfiedBy_replace_of parentHolds
        intro occurrence occurrenceMem
        simp only [List.mem_singleton] at occurrenceMem
        subst occurrence
        simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
          Stlsat.Occurrence.SatisfiedBy] using now
      · refine ⟨node.replace selected
          [selected.relabel (.markedEventually interval body)], by simp, ?_⟩
        apply Node.satisfiedBy_replace_of parentHolds
        intro occurrence occurrenceMem
        simp only [List.mem_singleton] at occurrenceMem
        subst occurrence
        simpa [AnnotatedOccurrence.relabel, AnnotatedOccurrence.SatisfiedBy,
          Stlsat.Occurrence.SatisfiedBy] using later
  | eventuallyAtEnd selected interval body shape present atEnd =>
      have selectedHolds := (Node.satisfiedBy_iff node semantics signal).1
        parentHolds selected present
      simp only [AnnotatedOccurrence.SatisfiedBy, shape,
        Stlsat.Occurrence.SatisfiedBy] at selectedHolds
      have now := (Stlsat.Formula.eventually_atEnd_iff atEnd).mp selectedHolds
      refine ⟨node.replace selected
        [selected.child 0 (.unmarked (body.temporalExpansion node.time)) none],
        by simp, ?_⟩
      apply Node.satisfiedBy_replace_of parentHolds
      intro occurrence occurrenceMem
      simp only [List.mem_singleton] at occurrenceMem
      subst occurrence
      simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
        Stlsat.Occurrence.SatisfiedBy] using now
  | alwaysBeforeEnd selected interval body shape present active beforeEnd =>
      have selectedHolds := (Node.satisfiedBy_iff node semantics signal).1
        parentHolds selected present
      simp only [AnnotatedOccurrence.SatisfiedBy, shape,
        Stlsat.Occurrence.SatisfiedBy] at selectedHolds
      rcases Stlsat.Formula.always_now_and_later active beforeEnd selectedHolds with
        ⟨now, later⟩
      refine ⟨node.replace selected
        [selected.relabel (.markedAlways interval body),
         selected.child 0 (.unmarked (body.temporalExpansion node.time))
           (some selected.reference)], by simp, ?_⟩
      apply Node.satisfiedBy_replace_of parentHolds
      intro occurrence occurrenceMem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMem
      rcases occurrenceMem with rfl | rfl
      · simpa [AnnotatedOccurrence.relabel, AnnotatedOccurrence.SatisfiedBy,
          Stlsat.Occurrence.SatisfiedBy] using later
      · simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
          Stlsat.Occurrence.SatisfiedBy] using now
  | alwaysAtEnd selected interval body shape present atEnd =>
      have selectedHolds := (Node.satisfiedBy_iff node semantics signal).1
        parentHolds selected present
      simp only [AnnotatedOccurrence.SatisfiedBy, shape,
        Stlsat.Occurrence.SatisfiedBy] at selectedHolds
      have now := (Stlsat.Formula.always_atEnd_iff atEnd).mp selectedHolds
      refine ⟨node.replace selected
        [selected.child 0 (.unmarked (body.temporalExpansion node.time))
          (some selected.reference)], by simp, ?_⟩
      apply Node.satisfiedBy_replace_of parentHolds
      intro occurrence occurrenceMem
      simp only [List.mem_singleton] at occurrenceMem
      subst occurrence
      simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
        Stlsat.Occurrence.SatisfiedBy] using now
  | strictUntilBeforeEnd selected interval invariant target shape present active beforeEnd =>
      have selectedHolds := (Node.satisfiedBy_iff node semantics signal).1
        parentHolds selected present
      simp only [AnnotatedOccurrence.SatisfiedBy, shape,
        Stlsat.Occurrence.SatisfiedBy] at selectedHolds
      rcases Stlsat.Formula.strictUntil_now_or_later active selectedHolds with
        now | ⟨invariantNow, later⟩
      · refine ⟨node.replace selected
          [selected.child 1 (.unmarked (target.temporalExpansion node.time)) none],
          by simp, ?_⟩
        apply Node.satisfiedBy_replace_of parentHolds
        intro occurrence occurrenceMem
        simp only [List.mem_singleton] at occurrenceMem
        subst occurrence
        simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
          Stlsat.Occurrence.SatisfiedBy] using now
      · refine ⟨node.replace selected
          [selected.relabel (.markedStrictUntil interval invariant target),
           selected.child 0 (.unmarked (invariant.temporalExpansion node.time))
             (some selected.reference)], by simp, ?_⟩
        apply Node.satisfiedBy_replace_of parentHolds
        intro occurrence occurrenceMem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMem
        rcases occurrenceMem with rfl | rfl
        · simpa [AnnotatedOccurrence.relabel, AnnotatedOccurrence.SatisfiedBy,
            Stlsat.Occurrence.SatisfiedBy] using later
        · simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
            Stlsat.Occurrence.SatisfiedBy]
            using invariantNow
  | strictUntilAtEnd selected interval invariant target shape present atEnd =>
      have selectedHolds := (Node.satisfiedBy_iff node semantics signal).1
        parentHolds selected present
      simp only [AnnotatedOccurrence.SatisfiedBy, shape,
        Stlsat.Occurrence.SatisfiedBy] at selectedHolds
      have now := (Stlsat.Formula.strictUntil_atEnd_iff atEnd).mp selectedHolds
      refine ⟨node.replace selected
        [selected.child 1 (.unmarked (target.temporalExpansion node.time)) none],
        by simp, ?_⟩
      apply Node.satisfiedBy_replace_of parentHolds
      intro occurrence occurrenceMem
      simp only [List.mem_singleton] at occurrenceMem
      subst occurrence
      simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
        Stlsat.Occurrence.SatisfiedBy] using now
  | strictReleaseBeforeEnd selected interval target invariant shape present active beforeEnd =>
      have selectedHolds := (Node.satisfiedBy_iff node semantics signal).1
        parentHolds selected present
      simp only [AnnotatedOccurrence.SatisfiedBy, shape,
        Stlsat.Occurrence.SatisfiedBy] at selectedHolds
      rcases Stlsat.Formula.strictRelease_now_or_later active beforeEnd selectedHolds with
        ⟨targetNow, invariantNow⟩ | ⟨invariantNow, later⟩
      · refine ⟨node.replace selected
          [selected.child 0 (.unmarked (target.temporalExpansion node.time)) none,
           selected.child 1 (.unmarked (invariant.temporalExpansion node.time)) none],
          by simp, ?_⟩
        apply Node.satisfiedBy_replace_of parentHolds
        intro occurrence occurrenceMem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMem
        rcases occurrenceMem with rfl | rfl
        · simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
            Stlsat.Occurrence.SatisfiedBy]
            using targetNow
        · simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
            Stlsat.Occurrence.SatisfiedBy]
            using invariantNow
      · refine ⟨node.replace selected
          [selected.relabel (.markedStrictRelease interval target invariant),
           selected.child 1 (.unmarked (invariant.temporalExpansion node.time))
             (some selected.reference)], by simp, ?_⟩
        apply Node.satisfiedBy_replace_of parentHolds
        intro occurrence occurrenceMem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMem
        rcases occurrenceMem with rfl | rfl
        · simpa [AnnotatedOccurrence.relabel, AnnotatedOccurrence.SatisfiedBy,
            Stlsat.Occurrence.SatisfiedBy] using later
        · simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
            Stlsat.Occurrence.SatisfiedBy]
            using invariantNow
  | strictReleaseAtEnd selected interval target invariant shape present atEnd =>
      have selectedHolds := (Node.satisfiedBy_iff node semantics signal).1
        parentHolds selected present
      simp only [AnnotatedOccurrence.SatisfiedBy, shape,
        Stlsat.Occurrence.SatisfiedBy] at selectedHolds
      have now := (Stlsat.Formula.strictRelease_atEnd_iff atEnd).mp selectedHolds
      refine ⟨node.replace selected
        [selected.child 1 (.unmarked (invariant.temporalExpansion node.time))
          (some selected.reference)], by simp, ?_⟩
      apply Node.satisfiedBy_replace_of parentHolds
      intro occurrence occurrenceMem
      simp only [List.mem_singleton] at occurrenceMem
      subst occurrence
      simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
        Stlsat.Occurrence.SatisfiedBy] using now

theorem exists_child_hasModel {node : Node Atom} {children : List (Node Atom)}
    {semantics : Stlsat.AtomicSemantics Atom} (expansion : Expansion node children)
    (model : node.HasModel semantics) :
    ∃ child ∈ children, child.HasModel semantics := by
  rcases model with ⟨model⟩
  rcases expansion.exists_child_satisfiedBy model.satisfies with
    ⟨child, childMem, childHolds⟩
  exact ⟨child, childMem, ⟨⟨model.signal, childHolds⟩⟩⟩

end Expansion

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

/-- Forward model preservation for the ordinary one-instant `STEP`. -/
theorem hasModel_step_of_hasModel {node : Node Atom}
    {semantics : Stlsat.AtomicSemantics Atom}
    (poised : node.Poised) (timely : node.Timely)
    (model : node.HasModel semantics) : node.step.HasModel semantics := by
  rcases model with ⟨model⟩
  change node.step.erase.HasModel semantics
  rw [Node.erase_step]
  exact ⟨Stlsat.ObligationSet.model_step (Node.ready_erase poised timely) timely model⟩

end Node

end Stlsat.Tableau
