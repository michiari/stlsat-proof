/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Tableau.Timing
import Stlsat.Tableau.Semantics
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Shared termination measure for STL tableaux

Ordinary expansion and advancement use a lexicographic measure consisting of
the remaining global horizon and the expansion work at the current time.
Both rule configurations use these definitions and the expansion/`STEP`
decrease lemmas.  The JUMP extension separately proves that its positive
advance decreases the same measure.
-/

namespace Stlsat.Tableau

universe u

namespace AnnotatedOccurrence

variable {Atom : Type u}

/-- Absolute horizon of the payload, ignoring provenance metadata. -/
abbrev horizon (occurrence : AnnotatedOccurrence Atom) : Nat :=
  occurrence.payload.horizon

/-- Expansion work of the payload, counted once for each annotated occurrence. -/
abbrev expansionWeight (occurrence : AnnotatedOccurrence Atom) : Nat :=
  occurrence.payload.expansionWeight

@[simp]
theorem horizon_unmark (occurrence : AnnotatedOccurrence Atom) :
    occurrence.unmark.horizon = occurrence.horizon :=
  Stlsat.Occurrence.horizon_unmark occurrence.payload

end AnnotatedOccurrence

namespace Node

variable {Atom : Type u}

open scoped BigOperators

/-- Total same-time expansion work, retaining occurrence identities. -/
def expansionWeight (node : Node Atom) : Nat :=
  ∑ occurrence ∈ node.label, occurrence.expansionWeight

/-- Every annotated payload has absolute horizon at most `bound`. -/
def HorizonBounded (bound : Nat) (node : Node Atom) : Prop :=
  ∀ occurrence ∈ node.label, occurrence.horizon ≤ bound

@[simp]
theorem initial_horizonBounded (formula : Stlsat.Formula Atom) :
    (initial formula).HorizonBounded formula.horizon := by
  simp [HorizonBounded, initial, AnnotatedOccurrence.horizon,
    Stlsat.Occurrence.horizon]

private theorem sum_union_le [DecidableEq Atom]
    (left right : Finset (AnnotatedOccurrence Atom)) :
    ∑ occurrence ∈ left ∪ right, occurrence.expansionWeight ≤
      (∑ occurrence ∈ left, occurrence.expansionWeight) +
        ∑ occurrence ∈ right, occurrence.expansionWeight := by
  induction right using Finset.induction with
  | empty => simp
  | @insert occurrence right notMem ih =>
      by_cases inLeft : occurrence ∈ left
      · have inUnion : occurrence ∈ left ∪ right :=
          Finset.mem_union_left right inLeft
        rw [Finset.sum_insert notMem]
        simp only [Finset.union_insert]
        simp [inUnion]
        omega
      · have notInUnion : occurrence ∉ left ∪ right := by simp [inLeft, notMem]
        rw [Finset.sum_insert notMem]
        simp only [Finset.union_insert, Finset.sum_insert notInUnion]
        omega

private theorem sum_toFinset_le [DecidableEq Atom]
    (occurrences : List (AnnotatedOccurrence Atom)) :
    ∑ occurrence ∈ occurrences.toFinset, occurrence.expansionWeight ≤
      (occurrences.map AnnotatedOccurrence.expansionWeight).sum := by
  induction occurrences with
  | nil => simp
  | cons occurrence occurrences ih =>
      simp only [List.toFinset_cons, List.map_cons, List.sum_cons]
      by_cases present : occurrence ∈ occurrences
      · rw [Finset.insert_eq_of_mem (by simpa using present)]
        exact Nat.le_add_left_of_le ih
      · rw [Finset.sum_insert (by simpa using present)]
        exact Nat.add_le_add_left ih _

theorem expansionWeight_replace_lt [DecidableEq Atom]
    (node : Node Atom) (selected : AnnotatedOccurrence Atom)
    (replacement : List (AnnotatedOccurrence Atom)) (present : selected ∈ node.label)
    (replacementLt :
      (replacement.map AnnotatedOccurrence.expansionWeight).sum <
        selected.expansionWeight) :
    (node.replace selected replacement).expansionWeight < node.expansionWeight := by
  unfold expansionWeight Node.replace
  simp only
  have unionLe := sum_union_le (node.label.erase selected) replacement.toFinset
  have toFinsetLe := sum_toFinset_le replacement
  rw [← Finset.sum_erase_add node.label AnnotatedOccurrence.expansionWeight present]
  omega

theorem horizonBounded_replace [DecidableEq Atom] {bound : Nat} {node : Node Atom}
    {selected : AnnotatedOccurrence Atom}
    {replacement : List (AnnotatedOccurrence Atom)}
    (bounded : node.HorizonBounded bound)
    (replacementBounded : ∀ occurrence ∈ replacement, occurrence.horizon ≤ bound) :
    (node.replace selected replacement).HorizonBounded bound := by
  intro occurrence occurrenceMem
  change occurrence ∈ node.label.erase selected ∪ replacement.toFinset at occurrenceMem
  rcases Finset.mem_union.mp occurrenceMem with oldMem | replacementMem
  · exact bounded occurrence (Finset.mem_of_mem_erase oldMem)
  · exact replacementBounded occurrence (by simpa using replacementMem)

theorem horizonBounded_replace_of_le [DecidableEq Atom] {bound : Nat}
    {node : Node Atom} {selected : AnnotatedOccurrence Atom}
    {replacement : List (AnnotatedOccurrence Atom)}
    (bounded : node.HorizonBounded bound) (selectedMem : selected ∈ node.label)
    (replacementLe : ∀ occurrence ∈ replacement,
      occurrence.horizon ≤ selected.horizon) :
    (node.replace selected replacement).HorizonBounded bound := by
  apply horizonBounded_replace bounded
  intro occurrence occurrenceMem
  exact (replacementLe occurrence occurrenceMem).trans (bounded selected selectedMem)

end Node

namespace Expansion

variable {Atom : Type u} [DecidableEq Atom]

theorem child_time {node child : Node Atom} {children : List (Node Atom)}
    (expansion : Expansion node children) (childMem : child ∈ children) :
    child.time = node.time := by
  cases expansion <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem <;>
    rcases childMem with rfl | rfl <;> rfl

theorem child_expansionWeight_lt {node child : Node Atom}
    {children : List (Node Atom)} (expansion : Expansion node children)
    (childMem : child ∈ children) :
    child.expansionWeight < node.expansionWeight := by
  cases expansion with
  | disjunction selected left right shape present =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      rcases childMem with rfl | rfl
      · apply Node.expansionWeight_replace_lt _ _ _ present
        simp [AnnotatedOccurrence.expansionWeight, shape,
          AnnotatedOccurrence.child, Stlsat.Occurrence.expansionWeight,
          Stlsat.Formula.expansionWeight]
        omega
      · apply Node.expansionWeight_replace_lt _ _ _ present
        simp [AnnotatedOccurrence.expansionWeight, shape,
          AnnotatedOccurrence.child, Stlsat.Occurrence.expansionWeight,
          Stlsat.Formula.expansionWeight]
        omega
  | conjunction selected left right shape present =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.expansionWeight_replace_lt _ _ _ present
      simp [AnnotatedOccurrence.expansionWeight, shape,
        AnnotatedOccurrence.child, Stlsat.Occurrence.expansionWeight,
        Stlsat.Formula.expansionWeight]
  | eventuallyBeforeEnd selected interval body shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      rcases childMem with rfl | rfl
      · apply Node.expansionWeight_replace_lt _ _ _ present
        simp [AnnotatedOccurrence.expansionWeight, shape,
          AnnotatedOccurrence.child, Stlsat.Occurrence.expansionWeight,
          Stlsat.Formula.expansionWeight]
      · apply Node.expansionWeight_replace_lt _ _ _ present
        simp [AnnotatedOccurrence.expansionWeight, shape,
          AnnotatedOccurrence.relabel, Stlsat.Occurrence.expansionWeight,
          Stlsat.Formula.expansionWeight]
  | eventuallyAtEnd selected interval body shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.expansionWeight_replace_lt _ _ _ present
      simp [AnnotatedOccurrence.expansionWeight, shape,
        AnnotatedOccurrence.child, Stlsat.Occurrence.expansionWeight,
        Stlsat.Formula.expansionWeight]
  | alwaysBeforeEnd selected interval body shape present active beforeEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.expansionWeight_replace_lt _ _ _ present
      simp [AnnotatedOccurrence.expansionWeight, shape, AnnotatedOccurrence.relabel,
        AnnotatedOccurrence.child, Stlsat.Occurrence.expansionWeight,
        Stlsat.Formula.expansionWeight]
  | alwaysAtEnd selected interval body shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.expansionWeight_replace_lt _ _ _ present
      simp [AnnotatedOccurrence.expansionWeight, shape,
        AnnotatedOccurrence.child, Stlsat.Occurrence.expansionWeight,
        Stlsat.Formula.expansionWeight]
  | strictUntilBeforeEnd selected interval invariant target shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      rcases childMem with rfl | rfl
      · apply Node.expansionWeight_replace_lt _ _ _ present
        simp [AnnotatedOccurrence.expansionWeight, shape,
          AnnotatedOccurrence.child, Stlsat.Occurrence.expansionWeight,
          Stlsat.Formula.expansionWeight]
        omega
      · apply Node.expansionWeight_replace_lt _ _ _ present
        simp [AnnotatedOccurrence.expansionWeight, shape, AnnotatedOccurrence.relabel,
          AnnotatedOccurrence.child, Stlsat.Occurrence.expansionWeight,
          Stlsat.Formula.expansionWeight]
        omega
  | strictUntilAtEnd selected interval invariant target shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.expansionWeight_replace_lt _ _ _ present
      simp [AnnotatedOccurrence.expansionWeight, shape,
        AnnotatedOccurrence.child, Stlsat.Occurrence.expansionWeight,
        Stlsat.Formula.expansionWeight]
      omega
  | strictReleaseBeforeEnd selected interval target invariant shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      rcases childMem with rfl | rfl
      · apply Node.expansionWeight_replace_lt _ _ _ present
        simp [AnnotatedOccurrence.expansionWeight, shape,
          AnnotatedOccurrence.child, Stlsat.Occurrence.expansionWeight,
          Stlsat.Formula.expansionWeight]
      · apply Node.expansionWeight_replace_lt _ _ _ present
        simp [AnnotatedOccurrence.expansionWeight, shape, AnnotatedOccurrence.relabel,
          AnnotatedOccurrence.child, Stlsat.Occurrence.expansionWeight,
          Stlsat.Formula.expansionWeight]
        omega
  | strictReleaseAtEnd selected interval target invariant shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.expansionWeight_replace_lt _ _ _ present
      simp [AnnotatedOccurrence.expansionWeight, shape,
        AnnotatedOccurrence.child, Stlsat.Occurrence.expansionWeight,
        Stlsat.Formula.expansionWeight]
      omega

theorem child_horizonBounded {bound : Nat} {node child : Node Atom}
    {children : List (Node Atom)} (expansion : Expansion node children)
    (bounded : node.HorizonBounded bound) (childMem : child ∈ children) :
    child.HorizonBounded bound := by
  cases expansion with
  | disjunction selected left right shape present =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      rcases childMem with rfl | rfl
      · apply Node.horizonBounded_replace_of_le bounded present
        intro occurrence occurrenceMem
        simp only [List.mem_singleton] at occurrenceMem
        subst occurrence
        simp [AnnotatedOccurrence.horizon, AnnotatedOccurrence.child, shape,
          Stlsat.Occurrence.horizon, Stlsat.Formula.horizon]
      · apply Node.horizonBounded_replace_of_le bounded present
        intro occurrence occurrenceMem
        simp only [List.mem_singleton] at occurrenceMem
        subst occurrence
        simp [AnnotatedOccurrence.horizon, AnnotatedOccurrence.child, shape,
          Stlsat.Occurrence.horizon, Stlsat.Formula.horizon]
  | conjunction selected left right shape present =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.horizonBounded_replace_of_le bounded present
      intro occurrence occurrenceMem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMem
      rcases occurrenceMem with rfl | rfl
      · simp [AnnotatedOccurrence.horizon, AnnotatedOccurrence.child, shape,
          Stlsat.Occurrence.horizon, Stlsat.Formula.horizon]
      · simp [AnnotatedOccurrence.horizon, AnnotatedOccurrence.child, shape,
          Stlsat.Occurrence.horizon, Stlsat.Formula.horizon]
  | eventuallyBeforeEnd selected interval body shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      rcases childMem with rfl | rfl
      · apply Node.horizonBounded_replace_of_le bounded present
        intro occurrence occurrenceMem
        simp only [List.mem_singleton] at occurrenceMem
        subst occurrence
        simp only [AnnotatedOccurrence.horizon, AnnotatedOccurrence.child,
          shape, Stlsat.Occurrence.horizon, Stlsat.Formula.horizon]
        exact (Stlsat.Formula.horizon_temporalExpansion_le body node.time).trans
          (Nat.add_le_add_right (Nat.le_of_lt beforeEnd) _)
      · apply Node.horizonBounded_replace_of_le bounded present
        intro occurrence occurrenceMem
        simp only [List.mem_singleton] at occurrenceMem
        subst occurrence
        simp [AnnotatedOccurrence.horizon, AnnotatedOccurrence.relabel, shape,
          Stlsat.Occurrence.horizon, Stlsat.Formula.horizon]
  | eventuallyAtEnd selected interval body shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.horizonBounded_replace_of_le bounded present
      intro occurrence occurrenceMem
      simp only [List.mem_singleton] at occurrenceMem
      subst occurrence
      simp only [AnnotatedOccurrence.horizon, AnnotatedOccurrence.child,
        shape, Stlsat.Occurrence.horizon, Stlsat.Formula.horizon]
      simpa [atEnd] using Stlsat.Formula.horizon_temporalExpansion_le body node.time
  | alwaysBeforeEnd selected interval body shape present active beforeEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.horizonBounded_replace_of_le bounded present
      intro occurrence occurrenceMem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMem
      rcases occurrenceMem with rfl | rfl
      · simp [AnnotatedOccurrence.horizon, AnnotatedOccurrence.relabel, shape,
          Stlsat.Occurrence.horizon, Stlsat.Formula.horizon]
      · simp only [AnnotatedOccurrence.horizon, AnnotatedOccurrence.child,
          shape, Stlsat.Occurrence.horizon, Stlsat.Formula.horizon]
        exact (Stlsat.Formula.horizon_temporalExpansion_le body node.time).trans
          (Nat.add_le_add_right (Nat.le_of_lt beforeEnd) _)
  | alwaysAtEnd selected interval body shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.horizonBounded_replace_of_le bounded present
      intro occurrence occurrenceMem
      simp only [List.mem_singleton] at occurrenceMem
      subst occurrence
      simp only [AnnotatedOccurrence.horizon, AnnotatedOccurrence.child,
        shape, Stlsat.Occurrence.horizon, Stlsat.Formula.horizon]
      simpa [atEnd] using Stlsat.Formula.horizon_temporalExpansion_le body node.time
  | strictUntilBeforeEnd selected interval invariant target shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      rcases childMem with rfl | rfl
      · apply Node.horizonBounded_replace_of_le bounded present
        intro occurrence occurrenceMem
        simp only [List.mem_singleton] at occurrenceMem
        subst occurrence
        simp only [AnnotatedOccurrence.horizon, AnnotatedOccurrence.child,
          shape, Stlsat.Occurrence.horizon, Stlsat.Formula.horizon]
        exact (Stlsat.Formula.horizon_temporalExpansion_le target node.time).trans
          (Nat.add_le_add (Nat.le_of_lt beforeEnd) (Nat.le_max_right _ _))
      · apply Node.horizonBounded_replace_of_le bounded present
        intro occurrence occurrenceMem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMem
        rcases occurrenceMem with rfl | rfl
        · simp [AnnotatedOccurrence.horizon, AnnotatedOccurrence.relabel, shape,
            Stlsat.Occurrence.horizon, Stlsat.Formula.horizon]
        · simp only [AnnotatedOccurrence.horizon, AnnotatedOccurrence.child,
            shape, Stlsat.Occurrence.horizon, Stlsat.Formula.horizon]
          exact (Stlsat.Formula.horizon_temporalExpansion_le invariant node.time).trans
            (Nat.add_le_add (Nat.le_of_lt beforeEnd) (Nat.le_max_left _ _))
  | strictUntilAtEnd selected interval invariant target shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.horizonBounded_replace_of_le bounded present
      intro occurrence occurrenceMem
      simp only [List.mem_singleton] at occurrenceMem
      subst occurrence
      simp only [AnnotatedOccurrence.horizon, AnnotatedOccurrence.child,
        shape, Stlsat.Occurrence.horizon, Stlsat.Formula.horizon]
      exact (Stlsat.Formula.horizon_temporalExpansion_le target node.time).trans
        (Nat.add_le_add (Nat.le_of_eq atEnd) (Nat.le_max_right _ _))
  | strictReleaseBeforeEnd selected interval target invariant shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      rcases childMem with rfl | rfl
      · apply Node.horizonBounded_replace_of_le bounded present
        intro occurrence occurrenceMem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMem
        rcases occurrenceMem with rfl | rfl
        · simp only [AnnotatedOccurrence.horizon, AnnotatedOccurrence.child,
            shape, Stlsat.Occurrence.horizon, Stlsat.Formula.horizon]
          exact (Stlsat.Formula.horizon_temporalExpansion_le target node.time).trans
            (Nat.add_le_add (Nat.le_of_lt beforeEnd) (Nat.le_max_left _ _))
        · simp only [AnnotatedOccurrence.horizon, AnnotatedOccurrence.child,
            shape, Stlsat.Occurrence.horizon, Stlsat.Formula.horizon]
          exact (Stlsat.Formula.horizon_temporalExpansion_le invariant node.time).trans
            (Nat.add_le_add (Nat.le_of_lt beforeEnd) (Nat.le_max_right _ _))
      · apply Node.horizonBounded_replace_of_le bounded present
        intro occurrence occurrenceMem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMem
        rcases occurrenceMem with rfl | rfl
        · simp [AnnotatedOccurrence.horizon, AnnotatedOccurrence.relabel, shape,
            Stlsat.Occurrence.horizon, Stlsat.Formula.horizon]
        · simp only [AnnotatedOccurrence.horizon, AnnotatedOccurrence.child,
            shape, Stlsat.Occurrence.horizon, Stlsat.Formula.horizon]
          exact (Stlsat.Formula.horizon_temporalExpansion_le invariant node.time).trans
            (Nat.add_le_add (Nat.le_of_lt beforeEnd) (Nat.le_max_right _ _))
  | strictReleaseAtEnd selected interval target invariant shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.horizonBounded_replace_of_le bounded present
      intro occurrence occurrenceMem
      simp only [List.mem_singleton] at occurrenceMem
      subst occurrence
      simp only [AnnotatedOccurrence.horizon, AnnotatedOccurrence.child,
        shape, Stlsat.Occurrence.horizon, Stlsat.Formula.horizon]
      exact (Stlsat.Formula.horizon_temporalExpansion_le invariant node.time).trans
        (Nat.add_le_add (Nat.le_of_eq atEnd) (Nat.le_max_right _ _))

end Expansion

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

theorem step_horizonBounded {bound : Nat} {node : Node Atom}
    (bounded : node.HorizonBounded bound) : node.step.HorizonBounded bound := by
  intro occurrence occurrenceMem
  change occurrence ∈ node.stepLabel at occurrenceMem
  rcases Finset.mem_union.mp occurrenceMem with unmarkedMem | markedMem
  · exact bounded occurrence (Finset.mem_filter.mp unmarkedMem).1
  · rcases Finset.mem_image.mp markedMem with ⟨source, sourceMem, rfl⟩
    rw [AnnotatedOccurrence.horizon_unmark]
    exact bounded source (Finset.mem_filter.mp sourceMem).1


theorem time_le_of_horizonBounded_of_timely_of_containsTemporal {bound : Nat}
    {node : Node Atom} (bounded : node.HorizonBounded bound)
    (timely : node.Timely) (containsTemporal : node.ContainsTemporal) :
    node.time ≤ bound := by
  rcases containsTemporal with ⟨occurrence, occurrenceMem, temporal⟩
  have occurrenceTimely := (Node.timely_iff node).mp timely occurrence occurrenceMem
  exact (Stlsat.Occurrence.time_le_horizon_of_timely_of_temporal
    occurrenceTimely temporal).trans (bounded occurrence occurrenceMem)

/-- Remaining bounded time is primary; same-time annotated expansion work is
secondary. -/
def terminationMeasure (bound : Nat) (node : Node Atom) : Nat × Nat :=
  (bound + 1 - node.time, node.expansionWeight)

end Node

end Stlsat.Tableau
