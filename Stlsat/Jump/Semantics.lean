/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Basic.Soundness
import Stlsat.Jump.Tableau

/-!
# Semantic foundations for the JUMP tableau

This file lifts the semantic node models used by the basic-tableau soundness
proof to parent-annotated JUMP nodes.  Parent annotations and occurrence paths
do not change the proof obligation denoted by an occurrence, so the semantic
interpretation is inherited from its basic payload.

The ordinary expansion and `STEP` cases are established here, together with
normality and timeliness preservation used by soundness, completeness, and
termination.  The interval-specific JUMP argument is developed in the later
technical modules and assembled in `Stlsat.Jump.Soundness`.
-/

namespace Stlsat.Jump

universe u

namespace AnnotatedOccurrence

variable {Atom : Type u}

/-- Parent annotations do not alter the semantic obligation of an occurrence. -/
abbrev SatisfiedBy (occurrence : AnnotatedOccurrence Atom)
    (semantics : Stlsat.AtomicSemantics Atom) (signal : Stlsat.Signal semantics)
    (time : Nat) : Prop :=
  occurrence.payload.SatisfiedBy semantics signal time

/-- Normality is a property of the payload, independently of its provenance. -/
abbrev InStrictNormalForm (occurrence : AnnotatedOccurrence Atom) : Prop :=
  occurrence.payload.InStrictNormalForm

/-- Timeliness is likewise inherited from the payload. -/
abbrev Timely (time : Nat) (occurrence : AnnotatedOccurrence Atom) : Prop :=
  occurrence.payload.Timely time

@[simp]
theorem satisfiedBy_child (occurrence : AnnotatedOccurrence Atom) (edge : Nat)
    (payload : Stlsat.Occurrence Atom) (parent : Option (OccurrenceRef Atom))
    (semantics : Stlsat.AtomicSemantics Atom) (signal : Stlsat.Signal semantics)
    (time : Nat) :
    (occurrence.child edge payload parent).SatisfiedBy semantics signal time ↔
      payload.SatisfiedBy semantics signal time :=
  Iff.rfl

@[simp]
theorem satisfiedBy_relabel (occurrence : AnnotatedOccurrence Atom)
    (payload : Stlsat.Occurrence Atom) (parent : Option (OccurrenceRef Atom))
    (semantics : Stlsat.AtomicSemantics Atom) (signal : Stlsat.Signal semantics)
    (time : Nat) :
    (occurrence.relabel payload parent).SatisfiedBy semantics signal time ↔
      payload.SatisfiedBy semantics signal time :=
  Iff.rfl

@[simp]
theorem normal_child (occurrence : AnnotatedOccurrence Atom) (edge : Nat)
    (payload : Stlsat.Occurrence Atom) (parent : Option (OccurrenceRef Atom)) :
    (occurrence.child edge payload parent).InStrictNormalForm ↔
      payload.InStrictNormalForm :=
  Iff.rfl

@[simp]
theorem normal_relabel (occurrence : AnnotatedOccurrence Atom)
    (payload : Stlsat.Occurrence Atom) (parent : Option (OccurrenceRef Atom)) :
    (occurrence.relabel payload parent).InStrictNormalForm ↔
      payload.InStrictNormalForm :=
  Iff.rfl

@[simp]
theorem normal_unmark (occurrence : AnnotatedOccurrence Atom) :
    occurrence.unmark.InStrictNormalForm ↔ occurrence.InStrictNormalForm := by
  exact Stlsat.Occurrence.inStrictNormalForm_unmark occurrence.payload

@[simp]
theorem timely_child (occurrence : AnnotatedOccurrence Atom) (edge : Nat)
    (payload : Stlsat.Occurrence Atom) (parent : Option (OccurrenceRef Atom))
    (time : Nat) :
    (occurrence.child edge payload parent).Timely time ↔ payload.Timely time :=
  Iff.rfl

@[simp]
theorem timely_relabel (occurrence : AnnotatedOccurrence Atom)
    (payload : Stlsat.Occurrence Atom) (parent : Option (OccurrenceRef Atom))
    (time : Nat) :
    (occurrence.relabel payload parent).Timely time ↔ payload.Timely time :=
  Iff.rfl

end AnnotatedOccurrence

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

/-- A JUMP node is satisfied exactly when its erased basic node is satisfied. -/
abbrev SatisfiedBy (node : Node Atom) (semantics : Stlsat.AtomicSemantics Atom)
    (signal : Stlsat.Signal semantics) : Prop :=
  node.erase.SatisfiedBy semantics signal

/-- Semantic models are reused from the erased basic node. -/
abbrev Model (node : Node Atom) (semantics : Stlsat.AtomicSemantics Atom) :=
  node.erase.Model semantics

/-- Existence of a semantic model for all obligations in a JUMP node. -/
abbrev HasModel (node : Node Atom) (semantics : Stlsat.AtomicSemantics Atom) : Prop :=
  node.erase.HasModel semantics

/-- All annotated payloads in a node are in strict normal form. -/
abbrev InStrictNormalForm (node : Node Atom) : Prop :=
  node.erase.InStrictNormalForm

/-- All annotated payloads are timely at the node counter. -/
abbrev Timely (node : Node Atom) : Prop :=
  node.erase.Timely

theorem satisfiedBy_iff (node : Node Atom) (semantics : Stlsat.AtomicSemantics Atom)
    (signal : Stlsat.Signal semantics) :
    node.SatisfiedBy semantics signal ↔
      ∀ occurrence ∈ node.label,
        occurrence.SatisfiedBy semantics signal node.time := by
  constructor
  · intro satisfied occurrence present
    apply satisfied occurrence.payload
    exact Finset.mem_image.mpr ⟨occurrence, present, rfl⟩
  · intro satisfied payload present
    rcases Finset.mem_image.mp present with ⟨occurrence, occurrence_mem, rfl⟩
    exact satisfied occurrence occurrence_mem

theorem normal_iff (node : Node Atom) :
    node.InStrictNormalForm ↔
      ∀ occurrence ∈ node.label, occurrence.InStrictNormalForm := by
  constructor
  · intro normal occurrence present
    apply normal occurrence.payload
    exact Finset.mem_image.mpr ⟨occurrence, present, rfl⟩
  · intro normal payload present
    rcases Finset.mem_image.mp present with ⟨occurrence, occurrence_mem, rfl⟩
    exact normal occurrence occurrence_mem

theorem timely_iff (node : Node Atom) :
    node.Timely ↔ ∀ occurrence ∈ node.label, occurrence.Timely node.time := by
  constructor
  · intro timely occurrence present
    apply timely occurrence.payload
    exact Finset.mem_image.mpr ⟨occurrence, present, rfl⟩
  · intro timely payload present
    rcases Finset.mem_image.mp present with ⟨occurrence, occurrence_mem, rfl⟩
    exact timely occurrence occurrence_mem

@[simp]
theorem erase_initial (formula : Stlsat.Formula Atom) :
    (Node.initial formula).erase = Stlsat.Node.initial formula := by
  simp [Node.initial, Node.erase, Stlsat.Node.initial]

@[simp]
theorem initial_timely (formula : Stlsat.Formula Atom) :
    (Node.initial formula).Timely := by
  change (Node.initial formula).erase.Timely
  rw [erase_initial]
  exact Stlsat.Node.initial_timely formula

theorem initial_normal {formula : Stlsat.Formula Atom}
    (normal : formula.InStrictNormalForm) :
    (Node.initial formula).InStrictNormalForm := by
  change (Node.initial formula).erase.InStrictNormalForm
  rw [erase_initial]
  intro occurrence present
  simp only [Stlsat.Node.initial, Finset.mem_singleton] at present
  subst occurrence
  simpa [Stlsat.Occurrence.InStrictNormalForm] using normal

/-- Semantic replacement lemma for parent-annotated labels. -/
theorem satisfiedBy_of_replace {node : Node Atom}
    {selected : AnnotatedOccurrence Atom}
    {replacement : List (AnnotatedOccurrence Atom)}
    {semantics : Stlsat.AtomicSemantics Atom} {signal : Stlsat.Signal semantics}
    (child : (node.replace selected replacement).SatisfiedBy semantics signal)
    (replacement_entails :
      (∀ occurrence ∈ replacement,
          occurrence.SatisfiedBy semantics signal node.time) →
        selected.SatisfiedBy semantics signal node.time) :
    node.SatisfiedBy semantics signal := by
  rw [satisfiedBy_iff] at child ⊢
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

/-- Replacing an occurrence by normal annotated obligations preserves normality. -/
theorem normal_replace {node : Node Atom} {selected : AnnotatedOccurrence Atom}
    {replacement : List (AnnotatedOccurrence Atom)} (node_normal : node.InStrictNormalForm)
    (replacement_normal : ∀ occurrence ∈ replacement,
      occurrence.InStrictNormalForm) :
    (node.replace selected replacement).InStrictNormalForm := by
  rw [normal_iff] at node_normal ⊢
  intro occurrence occurrence_mem
  change occurrence ∈ node.label.erase selected ∪ replacement.toFinset at occurrence_mem
  rw [Finset.mem_union] at occurrence_mem
  rcases occurrence_mem with old_mem | replacement_mem
  · exact node_normal occurrence (Finset.mem_of_mem_erase old_mem)
  · exact replacement_normal occurrence (by simpa using replacement_mem)

/-- Replacing an occurrence by timely annotated obligations preserves timeliness. -/
theorem timely_replace {node : Node Atom} {selected : AnnotatedOccurrence Atom}
    {replacement : List (AnnotatedOccurrence Atom)} (node_timely : node.Timely)
    (replacement_timely : ∀ occurrence ∈ replacement,
      occurrence.Timely node.time) :
    (node.replace selected replacement).Timely := by
  rw [timely_iff] at node_timely ⊢
  intro occurrence occurrence_mem
  change occurrence ∈ node.label.erase selected ∪ replacement.toFinset at occurrence_mem
  rw [Finset.mem_union] at occurrence_mem
  rcases occurrence_mem with old_mem | replacement_mem
  · exact node_timely occurrence (Finset.mem_of_mem_erase old_mem)
  · exact replacement_timely occurrence (by simpa using replacement_mem)

end Node

namespace Expansion

variable {Atom : Type u} [DecidableEq Atom]

/-- Each parent-aware expansion has the same backwards semantic law as its basic payload rule. -/
theorem satisfiedBy_parent {node child : Node Atom} {children : List (Node Atom)}
    {semantics : Stlsat.AtomicSemantics Atom} {signal : Stlsat.Signal semantics}
    (expansion : Expansion node children) (child_mem : child ∈ children)
    (child_satisfied : child.SatisfiedBy semantics signal) :
    node.SatisfiedBy semantics signal := by
  cases expansion with
  | disjunction selected left right shape present =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.satisfiedBy_of_replace child_satisfied
        intro replacements
        have leftHolds := replacements
          (selected.child 0 (.unmarked left) selected.parent) (by simp)
        simp only [AnnotatedOccurrence.satisfiedBy_child,
          Stlsat.Occurrence.SatisfiedBy] at leftHolds
        simp only [AnnotatedOccurrence.SatisfiedBy, shape,
          Stlsat.Occurrence.SatisfiedBy, Stlsat.Formula.SatisfiesFrom]
        exact Or.inl leftHolds
      · apply Node.satisfiedBy_of_replace child_satisfied
        intro replacements
        have rightHolds := replacements
          (selected.child 1 (.unmarked right) selected.parent) (by simp)
        simp only [AnnotatedOccurrence.satisfiedBy_child,
          Stlsat.Occurrence.SatisfiedBy] at rightHolds
        simp only [AnnotatedOccurrence.SatisfiedBy, shape,
          Stlsat.Occurrence.SatisfiedBy, Stlsat.Formula.SatisfiesFrom]
        exact Or.inr rightHolds
  | conjunction selected left right shape present =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.satisfiedBy_of_replace child_satisfied
      intro replacements
      have leftHolds := replacements
        (selected.child 0 (.unmarked left) selected.parent) (by simp)
      have rightHolds := replacements
        (selected.child 1 (.unmarked right) selected.parent) (by simp)
      simp only [AnnotatedOccurrence.satisfiedBy_child,
        Stlsat.Occurrence.SatisfiedBy] at leftHolds rightHolds
      simp only [AnnotatedOccurrence.SatisfiedBy, shape,
        Stlsat.Occurrence.SatisfiedBy, Stlsat.Formula.SatisfiesFrom]
      exact ⟨leftHolds, rightHolds⟩
  | eventuallyBeforeEnd selected interval body shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.satisfiedBy_of_replace child_satisfied
        intro replacements
        have bodyHolds := replacements
          (selected.child 0 (.unmarked (body.temporalExpansion node.time)) none) (by simp)
        have bodyHolds' : body.Satisfies semantics signal node.time := by
          simpa [Stlsat.Occurrence.SatisfiedBy] using bodyHolds
        simp only [AnnotatedOccurrence.SatisfiedBy, shape, Stlsat.Occurrence.SatisfiedBy]
        exact Stlsat.Formula.eventually_now active beforeEnd bodyHolds'
      · apply Node.satisfiedBy_of_replace child_satisfied
        intro replacements
        have later := replacements
          (selected.relabel (.markedEventually interval body)) (by simp)
        simp only [AnnotatedOccurrence.satisfiedBy_relabel,
          Stlsat.Occurrence.SatisfiedBy] at later
        simp only [AnnotatedOccurrence.SatisfiedBy, shape, Stlsat.Occurrence.SatisfiedBy]
        exact Stlsat.Formula.eventually_later later
  | eventuallyAtEnd selected interval body shape present atEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.satisfiedBy_of_replace child_satisfied
      intro replacements
      have bodyHolds := replacements
        (selected.child 0 (.unmarked (body.temporalExpansion node.time)) none) (by simp)
      have bodyHolds' : body.Satisfies semantics signal node.time := by
        simpa [Stlsat.Occurrence.SatisfiedBy] using bodyHolds
      simp only [AnnotatedOccurrence.SatisfiedBy, shape, Stlsat.Occurrence.SatisfiedBy]
      exact Stlsat.Formula.eventually_atEnd atEnd bodyHolds'
  | alwaysBeforeEnd selected interval body shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.satisfiedBy_of_replace child_satisfied
      intro replacements
      have later := replacements (selected.relabel (.markedAlways interval body)) (by simp)
      have bodyHolds := replacements
        (selected.child 0 (.unmarked (body.temporalExpansion node.time))
          (some selected.reference)) (by simp)
      have bodyHolds' : body.Satisfies semantics signal node.time := by
        simpa [Stlsat.Occurrence.SatisfiedBy] using bodyHolds
      simp only [AnnotatedOccurrence.satisfiedBy_relabel,
        Stlsat.Occurrence.SatisfiedBy] at later
      simp only [AnnotatedOccurrence.SatisfiedBy, shape, Stlsat.Occurrence.SatisfiedBy]
      exact Stlsat.Formula.always_now_later active bodyHolds' later
  | alwaysAtEnd selected interval body shape present atEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.satisfiedBy_of_replace child_satisfied
      intro replacements
      have bodyHolds := replacements
        (selected.child 0 (.unmarked (body.temporalExpansion node.time))
          (some selected.reference)) (by simp)
      have bodyHolds' : body.Satisfies semantics signal node.time := by
        simpa [Stlsat.Occurrence.SatisfiedBy] using bodyHolds
      simp only [AnnotatedOccurrence.SatisfiedBy, shape, Stlsat.Occurrence.SatisfiedBy]
      exact Stlsat.Formula.always_atEnd atEnd bodyHolds'
  | strictUntilBeforeEnd selected interval invariant target shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.satisfiedBy_of_replace child_satisfied
        intro replacements
        have targetHolds := replacements
          (selected.child 1 (.unmarked (target.temporalExpansion node.time)) none) (by simp)
        have targetHolds' : target.Satisfies semantics signal node.time := by
          simpa [Stlsat.Occurrence.SatisfiedBy] using targetHolds
        simp only [AnnotatedOccurrence.SatisfiedBy, shape, Stlsat.Occurrence.SatisfiedBy]
        exact Stlsat.Formula.strictUntil_now active beforeEnd targetHolds'
      · apply Node.satisfiedBy_of_replace child_satisfied
        intro replacements
        have later := replacements
          (selected.relabel (.markedStrictUntil interval invariant target)) (by simp)
        have invariantHolds := replacements
          (selected.child 0 (.unmarked (invariant.temporalExpansion node.time))
            (some selected.reference)) (by simp)
        have invariantHolds' : invariant.Satisfies semantics signal node.time := by
          simpa [Stlsat.Occurrence.SatisfiedBy] using invariantHolds
        simp only [AnnotatedOccurrence.satisfiedBy_relabel,
          Stlsat.Occurrence.SatisfiedBy] at later
        simp only [AnnotatedOccurrence.SatisfiedBy, shape, Stlsat.Occurrence.SatisfiedBy]
        exact Stlsat.Formula.strictUntil_later active invariantHolds' later
  | strictUntilAtEnd selected interval invariant target shape present atEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.satisfiedBy_of_replace child_satisfied
      intro replacements
      have targetHolds := replacements
        (selected.child 1 (.unmarked (target.temporalExpansion node.time)) none) (by simp)
      have targetHolds' : target.Satisfies semantics signal node.time := by
        simpa [Stlsat.Occurrence.SatisfiedBy] using targetHolds
      simp only [AnnotatedOccurrence.SatisfiedBy, shape, Stlsat.Occurrence.SatisfiedBy]
      exact Stlsat.Formula.strictUntil_atEnd atEnd targetHolds'
  | strictReleaseBeforeEnd selected interval target invariant shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.satisfiedBy_of_replace child_satisfied
        intro replacements
        have targetHolds := replacements
          (selected.child 0 (.unmarked (target.temporalExpansion node.time)) none) (by simp)
        have invariantHolds := replacements
          (selected.child 1 (.unmarked (invariant.temporalExpansion node.time)) none) (by simp)
        have targetHolds' : target.Satisfies semantics signal node.time := by
          simpa [Stlsat.Occurrence.SatisfiedBy] using targetHolds
        have invariantHolds' : invariant.Satisfies semantics signal node.time := by
          simpa [Stlsat.Occurrence.SatisfiedBy] using invariantHolds
        simp only [AnnotatedOccurrence.SatisfiedBy, shape, Stlsat.Occurrence.SatisfiedBy]
        exact Stlsat.Formula.strictRelease_now active beforeEnd targetHolds' invariantHolds'
      · apply Node.satisfiedBy_of_replace child_satisfied
        intro replacements
        have later := replacements
          (selected.relabel (.markedStrictRelease interval target invariant)) (by simp)
        have invariantHolds := replacements
          (selected.child 1 (.unmarked (invariant.temporalExpansion node.time))
            (some selected.reference)) (by simp)
        have invariantHolds' : invariant.Satisfies semantics signal node.time := by
          simpa [Stlsat.Occurrence.SatisfiedBy] using invariantHolds
        simp only [AnnotatedOccurrence.satisfiedBy_relabel,
          Stlsat.Occurrence.SatisfiedBy] at later
        simp only [AnnotatedOccurrence.SatisfiedBy, shape, Stlsat.Occurrence.SatisfiedBy]
        exact Stlsat.Formula.strictRelease_later invariantHolds' later
  | strictReleaseAtEnd selected interval target invariant shape present atEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.satisfiedBy_of_replace child_satisfied
      intro replacements
      have invariantHolds := replacements
        (selected.child 1 (.unmarked (invariant.temporalExpansion node.time))
          (some selected.reference)) (by simp)
      have invariantHolds' : invariant.Satisfies semantics signal node.time := by
        simpa [Stlsat.Occurrence.SatisfiedBy] using invariantHolds
      simp only [AnnotatedOccurrence.SatisfiedBy, shape, Stlsat.Occurrence.SatisfiedBy]
      exact Stlsat.Formula.strictRelease_atEnd atEnd invariantHolds'

/-- Expansion preserves strict normal form of every annotated payload. -/
theorem child_normal {node child : Node Atom} {children : List (Node Atom)}
    (expansion : Expansion node children) (node_normal : node.InStrictNormalForm)
    (child_mem : child ∈ children) : child.InStrictNormalForm := by
  cases expansion with
  | disjunction selected left right shape present =>
      have selected_normal := (Node.normal_iff node).mp node_normal selected present
      simp only [AnnotatedOccurrence.InStrictNormalForm, shape,
        Stlsat.Occurrence.InStrictNormalForm, Stlsat.Formula.InStrictNormalForm]
        at selected_normal
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.normal_replace node_normal
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        subst occurrence
        simpa [Stlsat.Occurrence.InStrictNormalForm] using selected_normal.1
      · apply Node.normal_replace node_normal
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        subst occurrence
        simpa [Stlsat.Occurrence.InStrictNormalForm] using selected_normal.2
  | conjunction selected left right shape present =>
      have selected_normal := (Node.normal_iff node).mp node_normal selected present
      simp only [AnnotatedOccurrence.InStrictNormalForm, shape,
        Stlsat.Occurrence.InStrictNormalForm, Stlsat.Formula.InStrictNormalForm]
        at selected_normal
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.normal_replace node_normal
      intro occurrence mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · simpa [Stlsat.Occurrence.InStrictNormalForm] using selected_normal.1
      · simpa [Stlsat.Occurrence.InStrictNormalForm] using selected_normal.2
  | eventuallyBeforeEnd selected interval body shape present active beforeEnd =>
      have selected_normal := (Node.normal_iff node).mp node_normal selected present
      simp only [AnnotatedOccurrence.InStrictNormalForm, shape,
        Stlsat.Occurrence.InStrictNormalForm, Stlsat.Formula.InStrictNormalForm]
        at selected_normal
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.normal_replace node_normal
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        subst occurrence
        simpa [Stlsat.Occurrence.InStrictNormalForm] using selected_normal
      · apply Node.normal_replace node_normal
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        subst occurrence
        simpa [Stlsat.Occurrence.InStrictNormalForm,
          Stlsat.Formula.InStrictNormalForm] using selected_normal
  | eventuallyAtEnd selected interval body shape present atEnd =>
      have selected_normal := (Node.normal_iff node).mp node_normal selected present
      simp only [AnnotatedOccurrence.InStrictNormalForm, shape,
        Stlsat.Occurrence.InStrictNormalForm, Stlsat.Formula.InStrictNormalForm]
        at selected_normal
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.normal_replace node_normal
      intro occurrence mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      subst occurrence
      simpa [Stlsat.Occurrence.InStrictNormalForm] using selected_normal
  | alwaysBeforeEnd selected interval body shape present active beforeEnd =>
      have selected_normal := (Node.normal_iff node).mp node_normal selected present
      simp only [AnnotatedOccurrence.InStrictNormalForm, shape,
        Stlsat.Occurrence.InStrictNormalForm, Stlsat.Formula.InStrictNormalForm]
        at selected_normal
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.normal_replace node_normal
      intro occurrence mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · simpa [Stlsat.Occurrence.InStrictNormalForm,
          Stlsat.Formula.InStrictNormalForm] using selected_normal
      · simpa [Stlsat.Occurrence.InStrictNormalForm] using selected_normal
  | alwaysAtEnd selected interval body shape present atEnd =>
      have selected_normal := (Node.normal_iff node).mp node_normal selected present
      simp only [AnnotatedOccurrence.InStrictNormalForm, shape,
        Stlsat.Occurrence.InStrictNormalForm, Stlsat.Formula.InStrictNormalForm]
        at selected_normal
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.normal_replace node_normal
      intro occurrence mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      subst occurrence
      simpa [Stlsat.Occurrence.InStrictNormalForm] using selected_normal
  | strictUntilBeforeEnd selected interval invariant target shape present active beforeEnd =>
      have selected_normal := (Node.normal_iff node).mp node_normal selected present
      simp only [AnnotatedOccurrence.InStrictNormalForm, shape,
        Stlsat.Occurrence.InStrictNormalForm, Stlsat.Formula.InStrictNormalForm]
        at selected_normal
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.normal_replace node_normal
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        subst occurrence
        simpa [Stlsat.Occurrence.InStrictNormalForm] using selected_normal.2
      · apply Node.normal_replace node_normal
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl
        · simpa [Stlsat.Occurrence.InStrictNormalForm,
            Stlsat.Formula.InStrictNormalForm] using selected_normal
        · simpa [Stlsat.Occurrence.InStrictNormalForm] using selected_normal.1
  | strictUntilAtEnd selected interval invariant target shape present atEnd =>
      have selected_normal := (Node.normal_iff node).mp node_normal selected present
      simp only [AnnotatedOccurrence.InStrictNormalForm, shape,
        Stlsat.Occurrence.InStrictNormalForm, Stlsat.Formula.InStrictNormalForm]
        at selected_normal
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.normal_replace node_normal
      intro occurrence mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      subst occurrence
      simpa [Stlsat.Occurrence.InStrictNormalForm] using selected_normal.2
  | strictReleaseBeforeEnd selected interval target invariant shape present active beforeEnd =>
      have selected_normal := (Node.normal_iff node).mp node_normal selected present
      simp only [AnnotatedOccurrence.InStrictNormalForm, shape,
        Stlsat.Occurrence.InStrictNormalForm, Stlsat.Formula.InStrictNormalForm]
        at selected_normal
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.normal_replace node_normal
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl
        · simpa [Stlsat.Occurrence.InStrictNormalForm] using selected_normal.1
        · simpa [Stlsat.Occurrence.InStrictNormalForm] using selected_normal.2
      · apply Node.normal_replace node_normal
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl
        · simpa [Stlsat.Occurrence.InStrictNormalForm,
            Stlsat.Formula.InStrictNormalForm] using selected_normal
        · simpa [Stlsat.Occurrence.InStrictNormalForm] using selected_normal.2
  | strictReleaseAtEnd selected interval target invariant shape present atEnd =>
      have selected_normal := (Node.normal_iff node).mp node_normal selected present
      simp only [AnnotatedOccurrence.InStrictNormalForm, shape,
        Stlsat.Occurrence.InStrictNormalForm, Stlsat.Formula.InStrictNormalForm]
        at selected_normal
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.normal_replace node_normal
      intro occurrence mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      subst occurrence
      simpa [Stlsat.Occurrence.InStrictNormalForm] using selected_normal.2

/-- Expansion preserves timeliness of every annotated payload. -/
theorem child_timely {node child : Node Atom} {children : List (Node Atom)}
    (expansion : Expansion node children) (node_timely : node.Timely)
    (child_mem : child ∈ children) : child.Timely := by
  cases expansion with
  | disjunction selected left right shape present =>
      have selected_timely := (Node.timely_iff node).mp node_timely selected present
      simp only [AnnotatedOccurrence.Timely, shape, Stlsat.Occurrence.Timely,
        Stlsat.Formula.Timely] at selected_timely
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.timely_replace node_timely
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        subst occurrence
        simpa [Stlsat.Occurrence.Timely] using selected_timely.1
      · apply Node.timely_replace node_timely
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        subst occurrence
        simpa [Stlsat.Occurrence.Timely] using selected_timely.2
  | conjunction selected left right shape present =>
      have selected_timely := (Node.timely_iff node).mp node_timely selected present
      simp only [AnnotatedOccurrence.Timely, shape, Stlsat.Occurrence.Timely,
        Stlsat.Formula.Timely] at selected_timely
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.timely_replace node_timely
      intro occurrence mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · simpa [Stlsat.Occurrence.Timely] using selected_timely.1
      · simpa [Stlsat.Occurrence.Timely] using selected_timely.2
  | eventuallyBeforeEnd selected interval body shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.timely_replace node_timely
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        subst occurrence
        simp [Stlsat.Occurrence.Timely]
      · apply Node.timely_replace node_timely
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        subst occurrence
        exact beforeEnd
  | eventuallyAtEnd selected interval body shape present atEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.timely_replace node_timely
      intro occurrence mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      subst occurrence
      simp [Stlsat.Occurrence.Timely]
  | alwaysBeforeEnd selected interval body shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.timely_replace node_timely
      intro occurrence mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · exact beforeEnd
      · simp [Stlsat.Occurrence.Timely]
  | alwaysAtEnd selected interval body shape present atEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.timely_replace node_timely
      intro occurrence mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      subst occurrence
      simp [Stlsat.Occurrence.Timely]
  | strictUntilBeforeEnd selected interval invariant target shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.timely_replace node_timely
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        subst occurrence
        simp [Stlsat.Occurrence.Timely]
      · apply Node.timely_replace node_timely
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl
        · exact beforeEnd
        · simp [Stlsat.Occurrence.Timely]
  | strictUntilAtEnd selected interval invariant target shape present atEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.timely_replace node_timely
      intro occurrence mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      subst occurrence
      simp [Stlsat.Occurrence.Timely]
  | strictReleaseBeforeEnd selected interval target invariant shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.timely_replace node_timely
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl
        · simp [Stlsat.Occurrence.Timely]
        · simp [Stlsat.Occurrence.Timely]
      · apply Node.timely_replace node_timely
        intro occurrence mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl
        · exact beforeEnd
        · simp [Stlsat.Occurrence.Timely]
  | strictReleaseAtEnd selected interval target invariant shape present atEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.timely_replace node_timely
      intro occurrence mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      subst occurrence
      simp [Stlsat.Occurrence.Timely]

end Expansion

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

/-- Erasing provenance commutes with the one-instant `STEP` label. -/
theorem erase_stepLabel (node : Node Atom) :
    node.stepLabel.image AnnotatedOccurrence.payload = node.erase.stepLabel := by
  classical
  ext occurrence
  constructor
  · intro member
    rcases Finset.mem_image.mp member with ⟨annotated, annotated_mem, rfl⟩
    rw [Node.stepLabel, Finset.mem_union] at annotated_mem
    rw [Stlsat.Node.stepLabel, Finset.mem_union]
    rcases annotated_mem with unmarked | marked
    · left
      rcases Finset.mem_filter.mp unmarked with ⟨present, temporal⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_image.mpr ⟨annotated, present, rfl⟩, temporal⟩
    · right
      rcases Finset.mem_image.mp marked with ⟨source, source_mem, rfl⟩
      rcases Finset.mem_filter.mp source_mem with ⟨present, continues⟩
      apply Finset.mem_image.mpr
      refine ⟨source.payload, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_image.mpr ⟨source, present, rfl⟩, continues⟩
  · intro member
    rw [Stlsat.Node.stepLabel, Finset.mem_union] at member
    apply Finset.mem_image.mpr
    rcases member with unmarked | marked
    · rcases Finset.mem_filter.mp unmarked with ⟨payload_mem, temporal⟩
      rcases Finset.mem_image.mp payload_mem with ⟨annotated, present, payload_eq⟩
      refine ⟨annotated, ?_, payload_eq⟩
      rw [Node.stepLabel, Finset.mem_union]
      exact Or.inl (Finset.mem_filter.mpr ⟨present, by
        simpa [AnnotatedOccurrence.isUnmarkedTemporal, payload_eq] using temporal⟩)
    · rcases Finset.mem_image.mp marked with ⟨payload, payload_mem, output_eq⟩
      rcases Finset.mem_filter.mp payload_mem with ⟨payload_present, continues⟩
      rcases Finset.mem_image.mp payload_present with ⟨annotated, present, payload_eq⟩
      refine ⟨annotated.unmark, ?_, ?_⟩
      · rw [Node.stepLabel, Finset.mem_union]
        apply Or.inr
        apply Finset.mem_image.mpr
        refine ⟨annotated, Finset.mem_filter.mpr ⟨present, ?_⟩, rfl⟩
        simpa [AnnotatedOccurrence.markedContinuesAt, Node.erase, payload_eq] using continues
      · simpa [AnnotatedOccurrence.unmark, AnnotatedOccurrence.relabel, payload_eq]
          using output_eq

@[simp]
theorem erase_step (node : Node Atom) : node.step.erase = node.erase.step := by
  apply congrArg (fun label => Stlsat.Node.mk (node.time + 1) label) (node.erase_stepLabel)

/-- A poised annotated node erases to a poised basic node. -/
theorem poised_erase {node : Node Atom} (poised : node.Poised) : node.erase.Poised := by
  rintro ⟨children, expansion⟩
  apply poised
  cases expansion with
  | disjunction left right present =>
      rcases Finset.mem_image.mp present with ⟨selected, selected_mem, shape⟩
      exact ⟨_, Expansion.disjunction selected left right shape selected_mem⟩
  | conjunction left right present =>
      rcases Finset.mem_image.mp present with ⟨selected, selected_mem, shape⟩
      exact ⟨_, Expansion.conjunction selected left right shape selected_mem⟩
  | eventuallyBeforeEnd interval body present active beforeEnd =>
      rcases Finset.mem_image.mp present with ⟨selected, selected_mem, shape⟩
      exact ⟨_, Expansion.eventuallyBeforeEnd selected interval body shape selected_mem
        active beforeEnd⟩
  | eventuallyAtEnd interval body present atEnd =>
      rcases Finset.mem_image.mp present with ⟨selected, selected_mem, shape⟩
      exact ⟨_, Expansion.eventuallyAtEnd selected interval body shape selected_mem atEnd⟩
  | alwaysBeforeEnd interval body present active beforeEnd =>
      rcases Finset.mem_image.mp present with ⟨selected, selected_mem, shape⟩
      exact ⟨_, Expansion.alwaysBeforeEnd selected interval body shape selected_mem
        active beforeEnd⟩
  | alwaysAtEnd interval body present atEnd =>
      rcases Finset.mem_image.mp present with ⟨selected, selected_mem, shape⟩
      exact ⟨_, Expansion.alwaysAtEnd selected interval body shape selected_mem atEnd⟩
  | strictUntilBeforeEnd interval invariant target present active beforeEnd =>
      rcases Finset.mem_image.mp present with ⟨selected, selected_mem, shape⟩
      exact ⟨_, Expansion.strictUntilBeforeEnd selected interval invariant target shape
        selected_mem active beforeEnd⟩
  | strictUntilAtEnd interval invariant target present atEnd =>
      rcases Finset.mem_image.mp present with ⟨selected, selected_mem, shape⟩
      exact ⟨_, Expansion.strictUntilAtEnd selected interval invariant target shape
        selected_mem atEnd⟩
  | strictReleaseBeforeEnd interval target invariant present active beforeEnd =>
      rcases Finset.mem_image.mp present with ⟨selected, selected_mem, shape⟩
      exact ⟨_, Expansion.strictReleaseBeforeEnd selected interval target invariant shape
        selected_mem active beforeEnd⟩
  | strictReleaseAtEnd interval target invariant present atEnd =>
      rcases Finset.mem_image.mp present with ⟨selected, selected_mem, shape⟩
      exact ⟨_, Expansion.strictReleaseAtEnd selected interval target invariant shape
        selected_mem atEnd⟩

omit [DecidableEq Atom] in
/-- An eventuality modeled at a later tableau time is modeled at every earlier
tableau time as well. -/
theorem eventually_satisfiedFrom_earlier {interval : Stlsat.Interval}
    {body : Stlsat.Formula Atom} {semantics : Stlsat.AtomicSemantics Atom}
    {signal : Stlsat.Signal semantics} {start finish : Nat}
    (leFinish : start ≤ finish)
    (holds : (Stlsat.Formula.eventually interval body).SatisfiesFrom
      semantics signal finish) :
    (Stlsat.Formula.eventually interval body).SatisfiesFrom semantics signal start := by
  induction finish, leFinish using Nat.le_induction with
  | base => exact holds
  | succ finish _ ih => exact ih (Stlsat.Formula.eventually_later holds)

omit [DecidableEq Atom] in
/-- An always obligation can be transported backwards while its lower endpoint
has not been passed. -/
theorem always_satisfiedFrom_earlier_beforeLower {interval : Stlsat.Interval}
    {body : Stlsat.Formula Atom} {semantics : Stlsat.AtomicSemantics Atom}
    {signal : Stlsat.Signal semantics} {start finish : Nat}
    (leFinish : start ≤ finish) (finishLe : finish ≤ interval.lower)
    (holds : (Stlsat.Formula.always interval body).SatisfiesFrom
      semantics signal finish) :
    (Stlsat.Formula.always interval body).SatisfiesFrom semantics signal start := by
  induction finish, leFinish using Nat.le_induction with
  | base => exact holds
  | succ finish _ ih =>
      exact ih (by omega) (Stlsat.Formula.always_beforeLower (by omega) holds)

omit [DecidableEq Atom] in
/-- A strict-until obligation can be transported backwards while its lower
endpoint has not been passed. -/
theorem strictUntil_satisfiedFrom_earlier_beforeLower {interval : Stlsat.Interval}
    {invariant target : Stlsat.Formula Atom}
    {semantics : Stlsat.AtomicSemantics Atom} {signal : Stlsat.Signal semantics}
    {start finish : Nat} (leFinish : start ≤ finish)
    (finishLe : finish ≤ interval.lower)
    (holds : (Stlsat.Formula.strictUntil interval invariant target).SatisfiesFrom
      semantics signal finish) :
    (Stlsat.Formula.strictUntil interval invariant target).SatisfiesFrom
      semantics signal start := by
  induction finish, leFinish using Nat.le_induction with
  | base => exact holds
  | succ finish _ ih =>
      exact ih (by omega) (Stlsat.Formula.strictUntil_beforeLower (by omega) holds)

omit [DecidableEq Atom] in
/-- A strict-release obligation can be transported backwards while its lower
endpoint has not been passed. -/
theorem strictRelease_satisfiedFrom_earlier_beforeLower {interval : Stlsat.Interval}
    {target invariant : Stlsat.Formula Atom}
    {semantics : Stlsat.AtomicSemantics Atom} {signal : Stlsat.Signal semantics}
    {start finish : Nat} (leFinish : start ≤ finish)
    (finishLe : finish ≤ interval.lower)
    (holds : (Stlsat.Formula.strictRelease interval target invariant).SatisfiesFrom
      semantics signal finish) :
    (Stlsat.Formula.strictRelease interval target invariant).SatisfiesFrom
      semantics signal start := by
  induction finish, leFinish using Nat.le_induction with
  | base => exact holds
  | succ finish _ ih =>
      exact ih (by omega) (Stlsat.Formula.strictRelease_beforeLower (by omega) holds)

omit [DecidableEq Atom] in
/-- Transport an always obligation backwards, supplying its body at precisely
the active instants skipped by the transport. -/
theorem always_satisfiedFrom_earlier {interval : Stlsat.Interval}
    {body : Stlsat.Formula Atom} {semantics : Stlsat.AtomicSemantics Atom}
    {signal : Stlsat.Signal semantics} {start finish : Nat}
    (leFinish : start ≤ finish)
    (bodyHolds : ∀ instant, start ≤ instant → instant < finish →
      body.Satisfies semantics signal instant)
    (holds : (Stlsat.Formula.always interval body).SatisfiesFrom
      semantics signal finish) :
    (Stlsat.Formula.always interval body).SatisfiesFrom semantics signal start := by
  induction finish, leFinish using Nat.le_induction with
  | base => exact holds
  | succ finish startLe ih =>
      apply ih
      · intro instant instantLe instantLt
        exact bodyHolds instant instantLe (by omega)
      · by_cases beforeLower : finish < interval.lower
        · exact Stlsat.Formula.always_beforeLower beforeLower holds
        · exact Stlsat.Formula.always_now_later (by omega)
            (bodyHolds finish startLe (by omega)) holds

omit [DecidableEq Atom] in
/-- Transport strict until backwards, supplying its invariant at the active
instants skipped by the transport. -/
theorem strictUntil_satisfiedFrom_earlier {interval : Stlsat.Interval}
    {invariant target : Stlsat.Formula Atom}
    {semantics : Stlsat.AtomicSemantics Atom} {signal : Stlsat.Signal semantics}
    {start finish : Nat} (leFinish : start ≤ finish)
    (invariantHolds : ∀ instant, start ≤ instant → instant < finish →
      invariant.Satisfies semantics signal instant)
    (holds : (Stlsat.Formula.strictUntil interval invariant target).SatisfiesFrom
      semantics signal finish) :
    (Stlsat.Formula.strictUntil interval invariant target).SatisfiesFrom
      semantics signal start := by
  induction finish, leFinish using Nat.le_induction with
  | base => exact holds
  | succ finish startLe ih =>
      apply ih
      · intro instant instantLe instantLt
        exact invariantHolds instant instantLe (by omega)
      · by_cases beforeLower : finish < interval.lower
        · exact Stlsat.Formula.strictUntil_beforeLower beforeLower holds
        · exact Stlsat.Formula.strictUntil_later (by omega)
            (invariantHolds finish startLe (by omega)) holds

omit [DecidableEq Atom] in
/-- Transport strict release backwards, supplying its invariant at the active
instants skipped by the transport. -/
theorem strictRelease_satisfiedFrom_earlier {interval : Stlsat.Interval}
    {target invariant : Stlsat.Formula Atom}
    {semantics : Stlsat.AtomicSemantics Atom} {signal : Stlsat.Signal semantics}
    {start finish : Nat} (leFinish : start ≤ finish)
    (invariantHolds : ∀ instant, start ≤ instant → instant < finish →
      invariant.Satisfies semantics signal instant)
    (holds : (Stlsat.Formula.strictRelease interval target invariant).SatisfiesFrom
      semantics signal finish) :
    (Stlsat.Formula.strictRelease interval target invariant).SatisfiesFrom
      semantics signal start := by
  induction finish, leFinish using Nat.le_induction with
  | base => exact holds
  | succ finish startLe ih =>
      apply ih
      · intro instant instantLe instantLt
        exact invariantHolds instant instantLe (by omega)
      · by_cases beforeLower : finish < interval.lower
        · exact Stlsat.Formula.strictRelease_beforeLower beforeLower holds
        · exact Stlsat.Formula.strictRelease_later
            (invariantHolds finish startLe (by omega)) holds

/-- At a timely poised node, every unmarked temporal operator is still before
its lower endpoint. -/
theorem beforeLower_of_unmarked_temporal {node : Node Atom}
    (poised : node.Poised) (timely : node.Timely)
    (occurrence : AnnotatedOccurrence Atom) (present : occurrence ∈ node.label)
    (interval : Stlsat.Interval) (formula : Stlsat.Formula Atom)
    (shape : occurrence.payload = .unmarked formula)
    (temporalShape : occurrence.interval? = some interval) :
    node.time < interval.lower := by
  have occurrenceTimely := (timely_iff node).mp timely occurrence present
  by_contra notBefore
  have active : interval.lower ≤ node.time := by omega
  apply poised
  cases occurrence with
  | mk id payload parent =>
      simp only at shape
      subst payload
      cases formula with
      | truth => simp [AnnotatedOccurrence.interval?] at temporalShape
      | atom proposition => simp [AnnotatedOccurrence.interval?] at temporalShape
      | neg body => simp [AnnotatedOccurrence.interval?] at temporalShape
      | and left right => simp [AnnotatedOccurrence.interval?] at temporalShape
      | or left right => simp [AnnotatedOccurrence.interval?] at temporalShape
      | eventually bounds body =>
          simp only [AnnotatedOccurrence.interval?, Option.some.injEq] at temporalShape
          subst bounds
          have upper : node.time ≤ interval.upper := by
            simpa [AnnotatedOccurrence.Timely, Stlsat.Occurrence.Timely,
              Stlsat.Formula.Timely] using occurrenceTimely
          by_cases beforeEnd : node.time < interval.upper
          · exact ⟨_, Expansion.eventuallyBeforeEnd _ interval body rfl present active beforeEnd⟩
          · exact ⟨_, Expansion.eventuallyAtEnd _ interval body rfl present (by omega)⟩
      | always bounds body =>
          simp only [AnnotatedOccurrence.interval?, Option.some.injEq] at temporalShape
          subst bounds
          have upper : node.time ≤ interval.upper := by
            simpa [AnnotatedOccurrence.Timely, Stlsat.Occurrence.Timely,
              Stlsat.Formula.Timely] using occurrenceTimely
          by_cases beforeEnd : node.time < interval.upper
          · exact ⟨_, Expansion.alwaysBeforeEnd _ interval body rfl present active beforeEnd⟩
          · exact ⟨_, Expansion.alwaysAtEnd _ interval body rfl present (by omega)⟩
      | strictUntil bounds invariant target =>
          simp only [AnnotatedOccurrence.interval?, Option.some.injEq] at temporalShape
          subst bounds
          have upper : node.time ≤ interval.upper := by
            simpa [AnnotatedOccurrence.Timely, Stlsat.Occurrence.Timely,
              Stlsat.Formula.Timely] using occurrenceTimely
          by_cases beforeEnd : node.time < interval.upper
          · exact ⟨_, Expansion.strictUntilBeforeEnd _ interval invariant target rfl
              present active beforeEnd⟩
          · exact ⟨_, Expansion.strictUntilAtEnd _ interval invariant target rfl present
              (by omega)⟩
      | strictRelease bounds target invariant =>
          simp only [AnnotatedOccurrence.interval?, Option.some.injEq] at temporalShape
          subst bounds
          have upper : node.time ≤ interval.upper := by
            simpa [AnnotatedOccurrence.Timely, Stlsat.Occurrence.Timely,
              Stlsat.Formula.Timely] using occurrenceTimely
          by_cases beforeEnd : node.time < interval.upper
          · exact ⟨_, Expansion.strictReleaseBeforeEnd _ interval target invariant rfl
              present active beforeEnd⟩
          · exact ⟨_, Expansion.strictReleaseAtEnd _ interval target invariant rfl present
              (by omega)⟩

/-- With all live endpoints in `K(u)`, no temporal occurrence of a timely
poised node is discarded by a computed JUMP. -/
theorem temporal_survives_computed_jump {node : Node Atom} {size : Nat}
    (poised : node.Poised) (timely : node.Timely)
    (computed : node.jumpSize? = some size)
    (occurrence : AnnotatedOccurrence Atom) (present : occurrence ∈ node.label)
    (temporal : occurrence.isTemporal = true) :
    Node.survivesJump (node.time + size) occurrence = true := by
  cases occurrence with
  | mk id payload parent =>
      cases payload with
      | unmarked formula =>
          cases formula with
          | truth => simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal,
              Stlsat.Formula.isTemporal] at temporal
          | atom proposition => simp [AnnotatedOccurrence.isTemporal,
              Stlsat.Occurrence.isTemporal, Stlsat.Formula.isTemporal] at temporal
          | neg body => simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal,
              Stlsat.Formula.isTemporal] at temporal
          | and left right => simp [AnnotatedOccurrence.isTemporal,
              Stlsat.Occurrence.isTemporal, Stlsat.Formula.isTemporal] at temporal
          | or left right => simp [AnnotatedOccurrence.isTemporal,
              Stlsat.Occurrence.isTemporal, Stlsat.Formula.isTemporal] at temporal
          | eventually interval body =>
              have beforeLower := beforeLower_of_unmarked_temporal poised timely
                { id := id, payload := .unmarked (.eventually interval body), parent := parent }
                present interval (.eventually interval body) rfl rfl
              have destination := node.jump_destination_le_lower _ interval present rfl computed
                beforeLower
              simpa [Node.survivesJump, AnnotatedOccurrence.interval?] using
                destination.trans interval.lower_le_upper
          | always interval body =>
              have beforeLower := beforeLower_of_unmarked_temporal poised timely
                { id := id, payload := .unmarked (.always interval body), parent := parent }
                present interval (.always interval body) rfl rfl
              have destination := node.jump_destination_le_lower _ interval present rfl computed
                beforeLower
              simpa [Node.survivesJump, AnnotatedOccurrence.interval?] using
                destination.trans interval.lower_le_upper
          | strictUntil interval invariant target =>
              have beforeLower := beforeLower_of_unmarked_temporal poised timely
                { id := id,
                  payload := .unmarked (.strictUntil interval invariant target),
                  parent := parent }
                present interval (.strictUntil interval invariant target) rfl rfl
              have destination := node.jump_destination_le_lower _ interval present rfl computed
                beforeLower
              simpa [Node.survivesJump, AnnotatedOccurrence.interval?] using
                destination.trans interval.lower_le_upper
          | strictRelease interval target invariant =>
              have beforeLower := beforeLower_of_unmarked_temporal poised timely
                { id := id,
                  payload := .unmarked (.strictRelease interval target invariant),
                  parent := parent }
                present interval (.strictRelease interval target invariant) rfl rfl
              have destination := node.jump_destination_le_lower _ interval present rfl computed
                beforeLower
              simpa [Node.survivesJump, AnnotatedOccurrence.interval?] using
                destination.trans interval.lower_le_upper
      | markedEventually interval body =>
          have future : node.time < interval.upper := by
            exact (timely_iff node).mp timely _ present
          have destination := node.jump_destination_le_upper _ interval present rfl computed future
          simpa [Node.survivesJump, AnnotatedOccurrence.interval?] using destination
      | markedAlways interval body =>
          have future : node.time < interval.upper := by
            exact (timely_iff node).mp timely _ present
          have destination := node.jump_destination_le_upper _ interval present rfl computed future
          simpa [Node.survivesJump, AnnotatedOccurrence.interval?] using destination
      | markedStrictUntil interval invariant target =>
          have future : node.time < interval.upper := by
            exact (timely_iff node).mp timely _ present
          have destination := node.jump_destination_le_upper _ interval present rfl computed future
          simpa [Node.survivesJump, AnnotatedOccurrence.interval?] using destination
      | markedStrictRelease interval target invariant =>
          have future : node.time < interval.upper := by
            exact (timely_iff node).mp timely _ present
          have destination := node.jump_destination_le_upper _ interval present rfl computed future
          simpa [Node.survivesJump, AnnotatedOccurrence.interval?] using destination

/-- `STEP` preserves normality, via exact erasure to the basic step. -/
theorem step_normal {node : Node Atom} (normal : node.InStrictNormalForm) :
    node.step.InStrictNormalForm := by
  change node.step.erase.InStrictNormalForm
  rw [erase_step]
  exact Stlsat.Node.step_inStrictNormalForm normal

/-- `STEP` preserves timeliness at a poised annotated node. -/
theorem step_timely {node : Node Atom} (timely : node.Timely) (poised : node.Poised) :
    node.step.Timely := by
  change node.step.erase.Timely
  rw [erase_step]
  exact Stlsat.Node.step_timely timely (poised_erase poised)

/-- Dropping local constraints and unmarking survivors preserves normality. -/
theorem jump_normal (node : Node Atom) (size : Nat) (normal : node.InStrictNormalForm) :
    (node.jump size).InStrictNormalForm := by
  rw [normal_iff] at normal ⊢
  intro occurrence occurrence_mem
  change occurrence ∈ node.jumpLabel size at occurrence_mem
  rcases Finset.mem_image.mp occurrence_mem with ⟨source, source_mem, rfl⟩
  have source_present := (Finset.mem_filter.mp source_mem).1
  exact (AnnotatedOccurrence.normal_unmark source).mpr (normal source source_present)

/-- Every retained temporal occurrence is timely at the jump destination. -/
theorem jump_timely (node : Node Atom) (size : Nat) : (node.jump size).Timely := by
  rw [timely_iff]
  intro occurrence occurrence_mem
  change occurrence ∈ node.jumpLabel size at occurrence_mem
  rcases Finset.mem_image.mp occurrence_mem with ⟨source, source_mem, rfl⟩
  have survives := (Finset.mem_filter.mp source_mem).2
  change source.unmark.Timely (node.time + size)
  cases source with
  | mk id payload parent =>
      cases payload with
      | unmarked formula =>
          cases formula <;>
            simp_all [Node.jumpLabel, Node.survivesJump,
              AnnotatedOccurrence.interval?, AnnotatedOccurrence.unmark,
              AnnotatedOccurrence.relabel, AnnotatedOccurrence.Timely,
              Stlsat.Occurrence.unmark, Stlsat.Occurrence.Timely,
              Stlsat.Formula.Timely]
      | markedEventually interval body =>
          simp_all [Node.jumpLabel, Node.survivesJump,
            AnnotatedOccurrence.interval?, AnnotatedOccurrence.unmark,
            AnnotatedOccurrence.relabel, AnnotatedOccurrence.Timely,
            Stlsat.Occurrence.unmark, Stlsat.Occurrence.Timely,
            Stlsat.Formula.Timely]
      | markedAlways interval body =>
          simp_all [Node.jumpLabel, Node.survivesJump,
            AnnotatedOccurrence.interval?, AnnotatedOccurrence.unmark,
            AnnotatedOccurrence.relabel, AnnotatedOccurrence.Timely,
            Stlsat.Occurrence.unmark, Stlsat.Occurrence.Timely,
            Stlsat.Formula.Timely]
      | markedStrictUntil interval invariant target =>
          simp_all [Node.jumpLabel, Node.survivesJump,
            AnnotatedOccurrence.interval?, AnnotatedOccurrence.unmark,
            AnnotatedOccurrence.relabel, AnnotatedOccurrence.Timely,
            Stlsat.Occurrence.unmark, Stlsat.Occurrence.Timely,
            Stlsat.Formula.Timely]
      | markedStrictRelease interval target invariant =>
          simp_all [Node.jumpLabel, Node.survivesJump,
            AnnotatedOccurrence.interval?, AnnotatedOccurrence.unmark,
            AnnotatedOccurrence.relabel, AnnotatedOccurrence.Timely,
            Stlsat.Occurrence.unmark, Stlsat.Occurrence.Timely,
            Stlsat.Formula.Timely]

/-- Reconstruct a parent model across the ordinary one-instant `STEP`. -/
theorem hasModel_of_step {node : Node Atom} {semantics : Stlsat.AtomicSemantics Atom}
    (notRejected : ¬node.Rejected semantics) (poised : node.Poised)
    (timely : node.Timely) (normal : node.InStrictNormalForm)
    (child_model : node.step.HasModel semantics) : node.HasModel semantics := by
  change node.erase.HasModel semantics
  apply Stlsat.Node.hasModel_of_step notRejected (poised_erase poised) timely normal
  change node.step.erase.HasModel semantics at child_model
  simpa using child_model

/-- An accepting annotated node has the same basic semantic model as its erasure. -/
theorem hasModel_of_accepting {node : Node Atom}
    {semantics : Stlsat.AtomicSemantics Atom} (accepting : node.Accepting semantics)
    (timely : node.Timely) (normal : node.InStrictNormalForm) :
    node.HasModel semantics := by
  rcases accepting with ⟨poised, notRejected, empty⟩
  apply node.hasModel_of_step notRejected poised timely normal
  let defaultSignal : Stlsat.Signal semantics := fun _ => Classical.choice semantics.nonempty
  refine ⟨⟨defaultSignal, ?_⟩⟩
  intro occurrence occurrence_mem
  change occurrence ∈ node.stepLabel.image AnnotatedOccurrence.payload at occurrence_mem
  rw [empty] at occurrence_mem
  simp at occurrence_mem

end Node

namespace Rule

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom}

/-- Every child of a JUMP-tableau rule preserves strict normal form. -/
theorem child_normal {node child : Node Atom} {children : List (Node Atom)}
    (rule : Rule semantics node children) (normal : node.InStrictNormalForm)
    (child_mem : child ∈ children) : child.InStrictNormalForm := by
  cases rule with
  | expand notRejected expansion => exact expansion.child_normal normal child_mem
  | step notRejected poised hasTemporal jumpDisabled =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      exact Node.step_normal normal
  | jump notRejected poised hasTemporal sound complete size computed =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      exact Node.jump_normal node size normal

/-- Every child of a JUMP-tableau rule is timely when its parent is timely. -/
theorem child_timely {node child : Node Atom} {children : List (Node Atom)}
    (rule : Rule semantics node children) (timely : node.Timely)
    (child_mem : child ∈ children) : child.Timely := by
  cases rule with
  | expand notRejected expansion => exact expansion.child_timely timely child_mem
  | step notRejected poised hasTemporal jumpDisabled =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      exact Node.step_timely timely poised
  | jump notRejected poised hasTemporal sound complete size computed =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      exact Node.jump_timely node size

end Rule

end Stlsat.Jump
