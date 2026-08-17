/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.Provenance

/-!
# Expansion frontiers at a JUMP node

Between two time-advancing rules, formula expansion records a concrete choice
for every disjunction and every temporal satisfy/postpone branch.  The
relation below remembers those choices without retaining the deleted internal
formula occurrences.  It is used for the invariant instance emitted by each
marked temporal occurrence.
-/

namespace Stlsat.Jump
universe u

/-- `ExpansionFrontier node id parent formula` says that expanding the virtual
unmarked occurrence `(id, formula, parent)` at `node.time`, along the choices
already made on the branch, has exactly the indicated live frontier in
`node.label`.

The temporal constructors mirror `Expansion`.  A postponed temporal formula
also records its marked residual; `always`, strict until, and strict release
record the invariant instance emitted at the current instant. -/
inductive ExpansionFrontier {Atom : Type u} [DecidableEq Atom]
    (node : Node Atom) : OccurrenceId → Option (OccurrenceRef Atom) →
      Stlsat.Formula Atom → Prop where
  | live (id parent formula)
      (present : AnnotatedOccurrence.mk id (.unmarked formula) parent ∈ node.label) :
      ExpansionFrontier node id parent formula
  | disjunctionLeft (id parent left right)
      (frontier : ExpansionFrontier node (id ++ [0]) parent left) :
      ExpansionFrontier node id parent (.or left right)
  | disjunctionRight (id parent left right)
      (frontier : ExpansionFrontier node (id ++ [1]) parent right) :
      ExpansionFrontier node id parent (.or left right)
  | conjunction (id parent left right)
      (leftFrontier : ExpansionFrontier node (id ++ [0]) parent left)
      (rightFrontier : ExpansionFrontier node (id ++ [1]) parent right) :
      ExpansionFrontier node id parent (.and left right)
  | eventuallyNow (id parent interval body)
      (active : interval.lower ≤ node.time) (notAfter : node.time ≤ interval.upper)
      (bodyFrontier : ExpansionFrontier node (id ++ [0]) none
        (body.temporalExpansion node.time)) :
      ExpansionFrontier node id parent (.eventually interval body)
  | eventuallyPostpone (id parent interval body)
      (active : interval.lower ≤ node.time) (beforeEnd : node.time < interval.upper)
      (marked : (AnnotatedOccurrence.mk id (.markedEventually interval body) parent) ∈ node.label) :
      ExpansionFrontier node id parent (.eventually interval body)
  | alwaysPostpone (id parent interval body)
      (active : interval.lower ≤ node.time) (beforeEnd : node.time < interval.upper)
      (marked : (AnnotatedOccurrence.mk id (.markedAlways interval body) parent) ∈ node.label)
      (bodyFrontier : ExpansionFrontier node (id ++ [0])
        (some (.mk id (.always interval body) parent))
        (body.temporalExpansion node.time)) :
      ExpansionFrontier node id parent (.always interval body)
  | alwaysAtEnd (id parent interval body)
      (atEnd : node.time = interval.upper)
      (bodyFrontier : ExpansionFrontier node (id ++ [0])
        (some (.mk id (.always interval body) parent))
        (body.temporalExpansion node.time)) :
      ExpansionFrontier node id parent (.always interval body)
  | strictUntilNow (id parent interval invariant target)
      (active : interval.lower ≤ node.time) (notAfter : node.time ≤ interval.upper)
      (targetFrontier : ExpansionFrontier node (id ++ [1]) none
        (target.temporalExpansion node.time)) :
      ExpansionFrontier node id parent (.strictUntil interval invariant target)
  | strictUntilPostpone (id parent interval invariant target)
      (active : interval.lower ≤ node.time) (beforeEnd : node.time < interval.upper)
      (marked : AnnotatedOccurrence.mk id
        (.markedStrictUntil interval invariant target) parent ∈ node.label)
      (invariantFrontier : ExpansionFrontier node (id ++ [0])
        (some (.mk id (.strictUntil interval invariant target) parent))
        (invariant.temporalExpansion node.time)) :
      ExpansionFrontier node id parent (.strictUntil interval invariant target)
  | strictReleaseNow (id parent interval target invariant)
      (active : interval.lower ≤ node.time) (beforeEnd : node.time < interval.upper)
      (targetFrontier : ExpansionFrontier node (id ++ [0]) none
        (target.temporalExpansion node.time))
      (invariantFrontier : ExpansionFrontier node (id ++ [1]) none
        (invariant.temporalExpansion node.time)) :
      ExpansionFrontier node id parent (.strictRelease interval target invariant)
  | strictReleasePostpone (id parent interval target invariant)
      (active : interval.lower ≤ node.time) (beforeEnd : node.time < interval.upper)
      (marked : AnnotatedOccurrence.mk id
        (.markedStrictRelease interval target invariant) parent ∈ node.label)
      (invariantFrontier : ExpansionFrontier node (id ++ [1])
        (some (.mk id (.strictRelease interval target invariant) parent))
        (invariant.temporalExpansion node.time)) :
      ExpansionFrontier node id parent (.strictRelease interval target invariant)
  | strictReleaseAtEnd (id parent interval target invariant)
      (atEnd : node.time = interval.upper)
      (invariantFrontier : ExpansionFrontier node (id ++ [1])
        (some (.mk id (.strictRelease interval target invariant) parent))
        (invariant.temporalExpansion node.time)) :
      ExpansionFrontier node id parent (.strictRelease interval target invariant)

namespace ExpansionFrontier

variable {Atom : Type u} [DecidableEq Atom]

/-- A frontier can be transported when every live unmarked leaf and every
live marked residual occurring in it is transported. -/
theorem map {source target : Node Atom}
    (sameTime : target.time = source.time)
    (live : ∀ id parent formula,
      (AnnotatedOccurrence.mk id (.unmarked formula) parent) ∈ source.label →
        ExpansionFrontier target id parent formula)
    (markedEventually : ∀ id parent interval body,
      AnnotatedOccurrence.mk id (.markedEventually interval body) parent ∈ source.label →
        AnnotatedOccurrence.mk id (.markedEventually interval body) parent ∈ target.label)
    (markedAlways : ∀ id parent interval body,
      AnnotatedOccurrence.mk id (.markedAlways interval body) parent ∈ source.label →
        AnnotatedOccurrence.mk id (.markedAlways interval body) parent ∈ target.label)
    (markedUntil : ∀ id parent interval invariant goal,
      AnnotatedOccurrence.mk id (.markedStrictUntil interval invariant goal) parent ∈
          source.label →
        AnnotatedOccurrence.mk id (.markedStrictUntil interval invariant goal) parent ∈
          target.label)
    (markedRelease : ∀ id parent interval goal invariant,
      AnnotatedOccurrence.mk id (.markedStrictRelease interval goal invariant) parent ∈
          source.label →
        AnnotatedOccurrence.mk id (.markedStrictRelease interval goal invariant) parent ∈
          target.label) :
    ∀ {id parent formula}, ExpansionFrontier source id parent formula →
      ExpansionFrontier target id parent formula := by
  intro id parent formula frontier
  induction frontier with
  | live id parent formula present => exact live id parent formula present
  | disjunctionLeft id parent left right frontier ih => exact .disjunctionLeft _ _ _ _ ih
  | disjunctionRight id parent left right frontier ih => exact .disjunctionRight _ _ _ _ ih
  | conjunction id parent left right leftFrontier rightFrontier ihLeft ihRight =>
      exact .conjunction _ _ _ _ ihLeft ihRight
  | eventuallyNow id parent interval body active notAfter bodyFrontier ih =>
      exact .eventuallyNow _ _ _ _ (by simpa [sameTime] using active)
        (by simpa [sameTime] using notAfter) (by simpa [sameTime] using ih)
  | eventuallyPostpone id parent interval body active beforeEnd marked =>
      exact .eventuallyPostpone _ _ _ _ (by simpa [sameTime] using active)
        (by simpa [sameTime] using beforeEnd) (markedEventually _ _ _ _ marked)
  | alwaysPostpone id parent interval body active beforeEnd marked bodyFrontier ih =>
      exact .alwaysPostpone _ _ _ _ (by simpa [sameTime] using active)
        (by simpa [sameTime] using beforeEnd) (markedAlways _ _ _ _ marked)
        (by simpa [sameTime] using ih)
  | alwaysAtEnd id parent interval body atEnd bodyFrontier ih =>
      exact .alwaysAtEnd _ _ _ _ (by simpa [sameTime] using atEnd)
        (by simpa [sameTime] using ih)
  | strictUntilNow id parent interval invariant goal active notAfter targetFrontier ih =>
      exact .strictUntilNow _ _ _ _ _ (by simpa [sameTime] using active)
        (by simpa [sameTime] using notAfter) (by simpa [sameTime] using ih)
  | strictUntilPostpone id parent interval invariant goal active beforeEnd marked
      invariantFrontier ih =>
      exact .strictUntilPostpone _ _ _ _ _ (by simpa [sameTime] using active)
        (by simpa [sameTime] using beforeEnd) (markedUntil _ _ _ _ _ marked)
        (by simpa [sameTime] using ih)
  | strictReleaseNow id parent interval goal invariant active beforeEnd targetFrontier
      invariantFrontier ihTarget ihInvariant =>
      exact .strictReleaseNow _ _ _ _ _ (by simpa [sameTime] using active)
        (by simpa [sameTime] using beforeEnd) (by simpa [sameTime] using ihTarget)
        (by simpa [sameTime] using ihInvariant)
  | strictReleasePostpone id parent interval goal invariant active beforeEnd marked
      invariantFrontier ih =>
      exact .strictReleasePostpone _ _ _ _ _ (by simpa [sameTime] using active)
        (by simpa [sameTime] using beforeEnd) (markedRelease _ _ _ _ _ marked)
        (by simpa [sameTime] using ih)
  | strictReleaseAtEnd id parent interval goal invariant atEnd invariantFrontier ih =>
      exact .strictReleaseAtEnd _ _ _ _ _ (by simpa [sameTime] using atEnd)
        (by simpa [sameTime] using ih)

end ExpansionFrontier

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

/-- Every currently marked invariant has a recorded expansion frontier for
the instance emitted at the current node. -/
def EmissionsPlanned (node : Node Atom) : Prop :=
  ∀ source ∈ node.label, ∀ edge invariant,
    source.postponedInvariant? = some (edge, invariant) →
      ExpansionFrontier node (source.id ++ [edge]) (some source.reference)
        (invariant.temporalExpansion node.time)

theorem initial_emissionsPlanned (formula : Stlsat.Formula Atom) :
    (Node.initial formula).EmissionsPlanned := by
  intro source present edge invariant shape
  simp only [Node.initial, Finset.mem_singleton] at present
  subst source
  simp [AnnotatedOccurrence.postponedInvariant?] at shape

end Node

namespace ExpansionFrontier

variable {Atom : Type u} [DecidableEq Atom]

private theorem mem_replace_of_ne {node : Node Atom}
    {selected occurrence : AnnotatedOccurrence Atom}
    {replacement : List (AnnotatedOccurrence Atom)}
    (different : occurrence ≠ selected) (present : occurrence ∈ node.label) :
    occurrence ∈ (node.replace selected replacement).label := by
  change occurrence ∈ node.label.erase selected ∪ replacement.toFinset
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr ⟨different, present⟩))

/-- Replace one live unmarked frontier leaf by a frontier for its expansion;
all other live leaves and marked residuals are inherited. -/
theorem replace {node : Node Atom} {selected : AnnotatedOccurrence Atom}
    {replacement : List (AnnotatedOccurrence Atom)} {selectedFormula : Stlsat.Formula Atom}
    (shape : selected.payload = .unmarked selectedFormula)
    (selectedFrontier : ExpansionFrontier (node.replace selected replacement)
      selected.id selected.parent selectedFormula) :
    ∀ {id parent formula}, ExpansionFrontier node id parent formula →
      ExpansionFrontier (node.replace selected replacement) id parent formula := by
  apply ExpansionFrontier.map (source := node)
    (target := node.replace selected replacement) (sameTime := rfl)
  · intro id parent formula present
    let occurrence : AnnotatedOccurrence Atom := .mk id (.unmarked formula) parent
    by_cases equal : occurrence = selected
    · have idEqual := congrArg AnnotatedOccurrence.id equal
      have parentEqual := congrArg AnnotatedOccurrence.parent equal
      have payloadEqual := congrArg AnnotatedOccurrence.payload equal
      simp only [occurrence] at idEqual parentEqual payloadEqual
      rw [shape] at payloadEqual
      have formulaEqual : formula = selectedFormula := by injection payloadEqual
      simpa [idEqual, parentEqual, formulaEqual] using selectedFrontier
    · exact .live _ _ _ (mem_replace_of_ne equal present)
  · intro id parent interval body present
    apply mem_replace_of_ne (present := present)
    intro equal
    have payloadEqual := congrArg AnnotatedOccurrence.payload equal
    simp [shape] at payloadEqual
  · intro id parent interval body present
    apply mem_replace_of_ne (present := present)
    intro equal
    have payloadEqual := congrArg AnnotatedOccurrence.payload equal
    simp [shape] at payloadEqual
  · intro id parent interval invariant goal present
    apply mem_replace_of_ne (present := present)
    intro equal
    have payloadEqual := congrArg AnnotatedOccurrence.payload equal
    simp [shape] at payloadEqual
  · intro id parent interval goal invariant present
    apply mem_replace_of_ne (present := present)
    intro equal
    have payloadEqual := congrArg AnnotatedOccurrence.payload equal
    simp [shape] at payloadEqual

end ExpansionFrontier

namespace Expansion

variable {Atom : Type u} [DecidableEq Atom]

/-- Every formula expansion transports all previously recorded expansion
frontiers to either selected child. -/
theorem child_expansionFrontier {node child : Node Atom}
    {children : List (Node Atom)} (expansion : Expansion node children)
    (childMem : child ∈ children) {id parent formula}
    (frontier : ExpansionFrontier node id parent formula) :
    ExpansionFrontier child id parent formula := by
  cases expansion with
  | disjunction selected left right shape present =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      rcases childMem with rfl | rfl
      · apply ExpansionFrontier.replace shape
          (.disjunctionLeft selected.id selected.parent left right
            (.live _ _ _ (by
              change selected.child 0 (.unmarked left) selected.parent ∈
                (node.replace selected
                  [selected.child 0 (.unmarked left) selected.parent]).label
              simp [Node.replace]))) frontier
      · apply ExpansionFrontier.replace shape
          (.disjunctionRight selected.id selected.parent left right
            (.live _ _ _ (by
              change selected.child 1 (.unmarked right) selected.parent ∈
                (node.replace selected
                  [selected.child 1 (.unmarked right) selected.parent]).label
              simp [Node.replace]))) frontier
  | conjunction selected left right shape present =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply ExpansionFrontier.replace shape
        (.conjunction selected.id selected.parent left right
          (.live _ _ _ (by simp [Node.replace, AnnotatedOccurrence.child]))
          (.live _ _ _ (by simp [Node.replace, AnnotatedOccurrence.child]))) frontier
  | eventuallyBeforeEnd selected interval body shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      rcases childMem with rfl | rfl
      · apply ExpansionFrontier.replace shape
          (.eventuallyNow selected.id selected.parent interval body active
            (Nat.le_of_lt beforeEnd)
            (.live _ _ _ (by simp [Node.replace, AnnotatedOccurrence.child]))) frontier
      · apply ExpansionFrontier.replace shape
          (.eventuallyPostpone selected.id selected.parent interval body active beforeEnd
            (by simp [Node.replace, AnnotatedOccurrence.relabel])) frontier
  | eventuallyAtEnd selected interval body shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply ExpansionFrontier.replace shape
        (.eventuallyNow selected.id selected.parent interval body
          (by simpa [Node.replace, atEnd] using interval.lower_le_upper)
          (by simp [Node.replace, atEnd])
          (.live _ _ _ (by simp [Node.replace, AnnotatedOccurrence.child]))) frontier
  | alwaysBeforeEnd selected interval body shape present active beforeEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply ExpansionFrontier.replace shape
        (.alwaysPostpone selected.id selected.parent interval body active beforeEnd
          (by simp [Node.replace, AnnotatedOccurrence.relabel])
          (.live _ _ _ (by
            simp [Node.replace, AnnotatedOccurrence.child,
              AnnotatedOccurrence.reference, AnnotatedOccurrence.formula, shape]))) frontier
  | alwaysAtEnd selected interval body shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply ExpansionFrontier.replace shape
        (.alwaysAtEnd selected.id selected.parent interval body atEnd
          (.live _ _ _ (by
            simp [Node.replace, AnnotatedOccurrence.child,
              AnnotatedOccurrence.reference, AnnotatedOccurrence.formula, shape]))) frontier
  | strictUntilBeforeEnd selected interval invariant target shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      rcases childMem with rfl | rfl
      · apply ExpansionFrontier.replace shape
          (.strictUntilNow selected.id selected.parent interval invariant target active
            (Nat.le_of_lt beforeEnd)
            (.live _ _ _ (by simp [Node.replace, AnnotatedOccurrence.child]))) frontier
      · apply ExpansionFrontier.replace shape
          (.strictUntilPostpone selected.id selected.parent interval invariant target active
            beforeEnd (by simp [Node.replace, AnnotatedOccurrence.relabel])
            (.live _ _ _ (by
              simp [Node.replace, AnnotatedOccurrence.child,
                AnnotatedOccurrence.reference, AnnotatedOccurrence.formula, shape]))) frontier
  | strictUntilAtEnd selected interval invariant target shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply ExpansionFrontier.replace shape
        (.strictUntilNow selected.id selected.parent interval invariant target
          (by simpa [Node.replace, atEnd] using interval.lower_le_upper)
          (by simp [Node.replace, atEnd])
          (.live _ _ _ (by simp [Node.replace, AnnotatedOccurrence.child]))) frontier
  | strictReleaseBeforeEnd selected interval target invariant shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      rcases childMem with rfl | rfl
      · apply ExpansionFrontier.replace shape
          (.strictReleaseNow selected.id selected.parent interval target invariant active beforeEnd
            (.live _ _ _ (by simp [Node.replace, AnnotatedOccurrence.child]))
            (.live _ _ _ (by simp [Node.replace, AnnotatedOccurrence.child]))) frontier
      · apply ExpansionFrontier.replace shape
          (.strictReleasePostpone selected.id selected.parent interval target invariant active
            beforeEnd (by simp [Node.replace, AnnotatedOccurrence.relabel])
            (.live _ _ _ (by
              simp [Node.replace, AnnotatedOccurrence.child,
                AnnotatedOccurrence.reference, AnnotatedOccurrence.formula, shape]))) frontier
  | strictReleaseAtEnd selected interval target invariant shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply ExpansionFrontier.replace shape
        (.strictReleaseAtEnd selected.id selected.parent interval target invariant atEnd
          (.live _ _ _ (by
            simp [Node.replace, AnnotatedOccurrence.child,
              AnnotatedOccurrence.reference, AnnotatedOccurrence.formula, shape]))) frontier

end Expansion

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

private theorem emissionsPlanned_replace {node : Node Atom}
    {selected : AnnotatedOccurrence Atom}
    {replacement : List (AnnotatedOccurrence Atom)}
    (planned : node.EmissionsPlanned)
    (transport : ∀ {id parent formula}, ExpansionFrontier node id parent formula →
      ExpansionFrontier (node.replace selected replacement) id parent formula)
    (fresh : ∀ source ∈ replacement, ∀ edge invariant,
      source.postponedInvariant? = some (edge, invariant) →
        ExpansionFrontier (node.replace selected replacement) (source.id ++ [edge])
          (some source.reference) (invariant.temporalExpansion node.time)) :
    (node.replace selected replacement).EmissionsPlanned := by
  intro source sourceMem edge invariant shape
  change source ∈ node.label.erase selected ∪ replacement.toFinset at sourceMem
  rcases Finset.mem_union.mp sourceMem with old | new
  · exact transport (planned source (Finset.mem_of_mem_erase old) edge invariant shape)
  · exact fresh source (by simpa using new) edge invariant shape

end Node


namespace Expansion

variable {Atom : Type u} [DecidableEq Atom]

/-- Formula expansion preserves the recorded plans and creates the plan for
the invariant emitted by a newly postponed temporal occurrence. -/
theorem child_emissionsPlanned {node child : Node Atom}
    {children : List (Node Atom)} (expansion : Expansion node children)
    (planned : node.EmissionsPlanned) (childMem : child ∈ children) :
    child.EmissionsPlanned := by
  cases expansion with
  | disjunction selected left right shape present =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      rcases childMem with rfl | rfl
      · apply Node.emissionsPlanned_replace planned
          (fun frontier => Expansion.child_expansionFrontier
            (.disjunction selected left right shape present) (by simp) frontier)
        intro source sourceMem edge invariant sourceShape
        simp only [List.mem_singleton] at sourceMem
        subst source
        simp [AnnotatedOccurrence.child, AnnotatedOccurrence.postponedInvariant?]
          at sourceShape
      · apply Node.emissionsPlanned_replace planned
          (fun frontier => Expansion.child_expansionFrontier
            (.disjunction selected left right shape present) (by simp) frontier)
        intro source sourceMem edge invariant sourceShape
        simp only [List.mem_singleton] at sourceMem
        subst source
        simp [AnnotatedOccurrence.child, AnnotatedOccurrence.postponedInvariant?]
          at sourceShape
  | conjunction selected left right shape present =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.emissionsPlanned_replace planned
        (fun frontier => Expansion.child_expansionFrontier
          (.conjunction selected left right shape present) (by simp) frontier)
      intro source sourceMem edge invariant sourceShape
      simp only [List.mem_cons, List.not_mem_nil, or_false] at sourceMem
      rcases sourceMem with rfl | rfl <;>
        simp [AnnotatedOccurrence.child, AnnotatedOccurrence.postponedInvariant?]
          at sourceShape
  | eventuallyBeforeEnd selected interval body shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      rcases childMem with rfl | rfl
      · apply Node.emissionsPlanned_replace planned
          (fun frontier => Expansion.child_expansionFrontier
            (.eventuallyBeforeEnd selected interval body shape present active beforeEnd)
              (by simp) frontier)
        intro source sourceMem edge invariant sourceShape
        simp only [List.mem_singleton] at sourceMem
        subst source
        simp [AnnotatedOccurrence.child, AnnotatedOccurrence.postponedInvariant?]
          at sourceShape
      · apply Node.emissionsPlanned_replace planned
          (fun frontier => Expansion.child_expansionFrontier
            (.eventuallyBeforeEnd selected interval body shape present active beforeEnd)
              (by simp) frontier)
        intro source sourceMem edge invariant sourceShape
        simp only [List.mem_singleton] at sourceMem
        subst source
        simp [AnnotatedOccurrence.relabel, AnnotatedOccurrence.postponedInvariant?]
          at sourceShape
  | eventuallyAtEnd selected interval body shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.emissionsPlanned_replace planned
        (fun frontier => Expansion.child_expansionFrontier
          (.eventuallyAtEnd selected interval body shape present atEnd) (by simp) frontier)
      intro source sourceMem edge invariant sourceShape
      simp only [List.mem_singleton] at sourceMem
      subst source
      simp [AnnotatedOccurrence.child, AnnotatedOccurrence.postponedInvariant?]
        at sourceShape
  | alwaysBeforeEnd selected interval body shape present active beforeEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.emissionsPlanned_replace planned
        (fun frontier => Expansion.child_expansionFrontier
          (.alwaysBeforeEnd selected interval body shape present active beforeEnd)
            (by simp) frontier)
      intro source sourceMem edge invariant sourceShape
      simp only [List.mem_cons, List.not_mem_nil, or_false] at sourceMem
      rcases sourceMem with rfl | rfl
      · simp only [AnnotatedOccurrence.relabel, AnnotatedOccurrence.postponedInvariant?,
          Option.some.injEq, Prod.mk.injEq] at sourceShape
        rcases sourceShape with ⟨rfl, rfl⟩
        exact .live _ _ _ (by
          simp [Node.replace, AnnotatedOccurrence.relabel, AnnotatedOccurrence.child,
            AnnotatedOccurrence.reference, AnnotatedOccurrence.formula, shape])
      · simp [AnnotatedOccurrence.child, AnnotatedOccurrence.postponedInvariant?]
          at sourceShape
  | alwaysAtEnd selected interval body shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.emissionsPlanned_replace planned
        (fun frontier => Expansion.child_expansionFrontier
          (.alwaysAtEnd selected interval body shape present atEnd) (by simp) frontier)
      intro source sourceMem edge invariant sourceShape
      simp only [List.mem_singleton] at sourceMem
      subst source
      simp [AnnotatedOccurrence.child, AnnotatedOccurrence.postponedInvariant?]
        at sourceShape
  | strictUntilBeforeEnd selected interval invariant target shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      rcases childMem with rfl | rfl
      · apply Node.emissionsPlanned_replace planned
          (fun frontier => Expansion.child_expansionFrontier
            (.strictUntilBeforeEnd selected interval invariant target shape present active
              beforeEnd)
              (by simp) frontier)
        intro source sourceMem edge formula sourceShape
        simp only [List.mem_singleton] at sourceMem
        subst source
        simp [AnnotatedOccurrence.child, AnnotatedOccurrence.postponedInvariant?]
          at sourceShape
      · apply Node.emissionsPlanned_replace planned
          (fun frontier => Expansion.child_expansionFrontier
            (.strictUntilBeforeEnd selected interval invariant target shape present active
              beforeEnd)
              (by simp) frontier)
        intro source sourceMem edge formula sourceShape
        simp only [List.mem_cons, List.not_mem_nil, or_false] at sourceMem
        rcases sourceMem with rfl | rfl
        · simp only [AnnotatedOccurrence.relabel, AnnotatedOccurrence.postponedInvariant?,
            Option.some.injEq, Prod.mk.injEq] at sourceShape
          rcases sourceShape with ⟨rfl, rfl⟩
          exact .live _ _ _ (by
            simp [Node.replace, AnnotatedOccurrence.relabel, AnnotatedOccurrence.child,
              AnnotatedOccurrence.reference, AnnotatedOccurrence.formula, shape])
        · simp [AnnotatedOccurrence.child, AnnotatedOccurrence.postponedInvariant?]
            at sourceShape
  | strictUntilAtEnd selected interval invariant target shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.emissionsPlanned_replace planned
        (fun frontier => Expansion.child_expansionFrontier
          (.strictUntilAtEnd selected interval invariant target shape present atEnd)
            (by simp) frontier)
      intro source sourceMem edge formula sourceShape
      simp only [List.mem_singleton] at sourceMem
      subst source
      simp [AnnotatedOccurrence.child, AnnotatedOccurrence.postponedInvariant?]
        at sourceShape
  | strictReleaseBeforeEnd selected interval target invariant shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      rcases childMem with rfl | rfl
      · apply Node.emissionsPlanned_replace planned
          (fun frontier => Expansion.child_expansionFrontier
            (.strictReleaseBeforeEnd selected interval target invariant shape present active
              beforeEnd)
              (by simp) frontier)
        intro source sourceMem edge formula sourceShape
        simp only [List.mem_cons, List.not_mem_nil, or_false] at sourceMem
        rcases sourceMem with rfl | rfl <;>
          simp [AnnotatedOccurrence.child, AnnotatedOccurrence.postponedInvariant?]
            at sourceShape
      · apply Node.emissionsPlanned_replace planned
          (fun frontier => Expansion.child_expansionFrontier
            (.strictReleaseBeforeEnd selected interval target invariant shape present active
              beforeEnd)
              (by simp) frontier)
        intro source sourceMem edge formula sourceShape
        simp only [List.mem_cons, List.not_mem_nil, or_false] at sourceMem
        rcases sourceMem with rfl | rfl
        · simp only [AnnotatedOccurrence.relabel, AnnotatedOccurrence.postponedInvariant?,
            Option.some.injEq, Prod.mk.injEq] at sourceShape
          rcases sourceShape with ⟨rfl, rfl⟩
          exact .live _ _ _ (by
            simp [Node.replace, AnnotatedOccurrence.relabel, AnnotatedOccurrence.child,
              AnnotatedOccurrence.reference, AnnotatedOccurrence.formula, shape])
        · simp [AnnotatedOccurrence.child, AnnotatedOccurrence.postponedInvariant?]
            at sourceShape
  | strictReleaseAtEnd selected interval target invariant shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.emissionsPlanned_replace planned
        (fun frontier => Expansion.child_expansionFrontier
          (.strictReleaseAtEnd selected interval target invariant shape present atEnd)
            (by simp) frontier)
      intro source sourceMem edge formula sourceShape
      simp only [List.mem_singleton] at sourceMem
      subst source
      simp [AnnotatedOccurrence.child, AnnotatedOccurrence.postponedInvariant?]
        at sourceShape

end Expansion

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

/-- A time advance unmarks every retained temporal occurrence, so no emitted
current-time invariant plan remains pending immediately after `STEP`. -/
theorem step_emissionsPlanned (node : Node Atom) : node.step.EmissionsPlanned := by
  intro source sourceMem edge invariant shape
  change source ∈ node.stepLabel at sourceMem
  rcases Finset.mem_union.mp sourceMem with unchanged | continued
  · rcases Finset.mem_filter.mp unchanged with ⟨_, unmarked⟩
    cases source with
    | mk id payload parent =>
        cases payload <;>
          simp_all [AnnotatedOccurrence.isUnmarkedTemporal,
            Stlsat.Occurrence.isUnmarkedTemporal,
            AnnotatedOccurrence.postponedInvariant?]
  · rcases Finset.mem_image.mp continued with ⟨old, _, rfl⟩
    cases old with
    | mk id payload parent =>
        cases payload <;>
          simp_all [AnnotatedOccurrence.unmark, AnnotatedOccurrence.relabel,
            Stlsat.Occurrence.unmark,
            AnnotatedOccurrence.postponedInvariant?]

/-- A JUMP also unmarks every surviving temporal occurrence. -/
theorem jump_emissionsPlanned (node : Node Atom) (size : Nat) :
    (node.jump size).EmissionsPlanned := by
  intro source sourceMem edge invariant shape
  change source ∈ node.jumpLabel size at sourceMem
  rcases Finset.mem_image.mp sourceMem with ⟨old, _, rfl⟩
  cases old with
  | mk id payload parent =>
      cases payload <;>
        simp_all [AnnotatedOccurrence.unmark, AnnotatedOccurrence.relabel,
          Stlsat.Occurrence.unmark,
          AnnotatedOccurrence.postponedInvariant?]

/-- The complete syntactic invariant carried from the initial node to a
derived JUMP node. -/
def SoundnessDerivationValid (node : Node Atom) : Prop :=
  node.DerivationValid ∧ node.EmissionsPlanned

theorem initial_soundnessDerivationValid (formula : Stlsat.Formula Atom) :
    (Node.initial formula).SoundnessDerivationValid :=
  ⟨Node.initial_derivationValid formula, Node.initial_emissionsPlanned formula⟩

end Node

namespace Rule

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom}

theorem child_emissionsPlanned {node child : Node Atom}
    {children : List (Node Atom)} (rule : Rule semantics node children)
    (planned : node.EmissionsPlanned) (childMem : child ∈ children) :
    child.EmissionsPlanned := by
  cases rule with
  | expand notRejected expansion => exact expansion.child_emissionsPlanned planned childMem
  | step notRejected poised hasTemporal jumpDisabled =>
      simp only [List.mem_singleton] at childMem
      subst child
      exact node.step_emissionsPlanned
  | jump notRejected poised hasTemporal sound complete size computed =>
      simp only [List.mem_singleton] at childMem
      subst child
      exact node.jump_emissionsPlanned size

theorem child_soundnessDerivationValid {node child : Node Atom}
    {children : List (Node Atom)} (rule : Rule semantics node children)
    (valid : node.SoundnessDerivationValid) (childMem : child ∈ children) :
    child.SoundnessDerivationValid :=
  ⟨rule.child_derivationValid valid.1 childMem,
    rule.child_emissionsPlanned valid.2 childMem⟩

end Rule

end Stlsat.Jump
