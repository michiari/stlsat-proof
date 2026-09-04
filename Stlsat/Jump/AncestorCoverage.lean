/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.Provenance

/-!
# Coverage through parent-active provenance

Validity windows of parent-active occurrences are lifted through stored parent
references until a live independent temporal ancestor is reached.  This
supplies the parent-active coverage case for the JUMP soundness guard.
-/

namespace Stlsat.Tableau
universe u

namespace OccurrenceRef

variable {Atom : Type u}

/-- Length of the finite provenance chain. -/
def depth : OccurrenceRef Atom → Nat
  | .mk _ _ none => 0
  | .mk _ _ (some parent) => parent.depth + 1

end OccurrenceRef

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

/-- Reachability supplies the lower endpoint of a marked interval, while
timeliness supplies its strict upper endpoint. -/
theorem postponedInvariant_active (node : Node Atom)
    (derivation : node.DerivationValid) (timely : node.Timely)
    (source : AnnotatedOccurrence Atom) (sourceMem : source ∈ node.label)
    {edge : Nat} {invariant : Stlsat.Formula Atom}
    (shape : source.postponedInvariant? = some (edge, invariant)) :
    match source.interval? with
    | some interval => interval.lower ≤ node.time ∧ node.time < interval.upper
    | none => False := by
  have lower := derivation.2 source sourceMem
  have upper := (Node.timely_iff node).mp timely source sourceMem
  cases source with
  | mk id payload parent =>
      cases payload <;>
        simp_all [AnnotatedOccurrence.postponedInvariant?,
          AnnotatedOccurrence.interval?,
          AnnotatedOccurrence.Timely, Stlsat.Occurrence.Timely]

omit [DecidableEq Atom] in
/-- Before considering parent activity, a skipped invariant leaf is covered by
a validity occurrence of the complete marked source formula. -/
theorem postponedInvariant_covered_by_source_of_admissible
    (node : Node Atom) {size offset : Nat}
    (admissible : node.JumpSizeAdmissible size) (strictlySkipped : offset < size)
    (source : AnnotatedOccurrence Atom) (sourceMem : source ∈ node.label)
    (edge : Nat) (invariant : Stlsat.Formula Atom)
    (sourceShape : source.postponedInvariant? = some (edge, invariant))
    (validity : ValidityOccurrence)
    (validityMem : validity ∈ FormulaValidity.validityOccurrences invariant)
    (active : match source.interval? with
      | some interval => interval.lower ≤ node.time ∧ node.time < interval.upper
      | none => False) :
    ∃ sourceValidity ∈ FormulaValidity.validityOccurrences source.formula,
      source.id ++ sourceValidity.path = source.id ++ [edge] ++ validity.path ∧
      sourceValidity.window.lower ≤ node.time + offset + validity.window.lower ∧
      node.time + offset + validity.window.upper ≤ sourceValidity.window.upper := by
  cases source with
  | mk id payload parent =>
      cases payload with
      | unmarked formula => simp [AnnotatedOccurrence.postponedInvariant?] at sourceShape
      | markedEventually interval body =>
          simp [AnnotatedOccurrence.postponedInvariant?] at sourceShape
      | markedAlways interval body =>
          simp only [AnnotatedOccurrence.postponedInvariant?, Option.some.injEq,
            Prod.mk.injEq] at sourceShape
          rcases sourceShape with ⟨rfl, rfl⟩
          simp only [AnnotatedOccurrence.interval?] at active
          let sourceValidity := ValidityOccurrence.prefixPath 0 (validity.through interval)
          refine ⟨sourceValidity, ?_, ?_, ?_, ?_⟩
          · exact List.mem_map.mpr ⟨validity, validityMem, rfl⟩
          · simp [sourceValidity, ValidityOccurrence.prefixPath,
              ValidityOccurrence.through, List.append_assoc]
          · simp [sourceValidity, ValidityOccurrence.prefixPath,
              ValidityOccurrence.through]
            omega
          · have destination := node.jump_destination_le_upper_of_admissible
                { id := id, payload := .markedAlways interval body, parent := parent }
                interval sourceMem rfl admissible active.2
            simp [sourceValidity, ValidityOccurrence.prefixPath,
              ValidityOccurrence.through]
            omega
      | markedStrictUntil interval left right =>
          simp only [AnnotatedOccurrence.postponedInvariant?, Option.some.injEq,
            Prod.mk.injEq] at sourceShape
          rcases sourceShape with ⟨rfl, rfl⟩
          simp only [AnnotatedOccurrence.interval?] at active
          have nontrivial : interval.lower < interval.upper := by omega
          let sourceValidity :=
            ValidityOccurrence.prefixPath 0 (validity.beforeTarget interval nontrivial)
          refine ⟨sourceValidity, ?_, ?_, ?_, ?_⟩
          · change sourceValidity ∈ FormulaValidity.validityOccurrences
              (.strictUntil interval left right)
            simp only [sourceValidity, FormulaValidity.validityOccurrences,
              dif_pos nontrivial, List.mem_append]
            exact Or.inl (List.mem_map.mpr ⟨validity, validityMem, rfl⟩)
          · simp [sourceValidity, ValidityOccurrence.prefixPath,
              ValidityOccurrence.beforeTarget, List.append_assoc]
          · simp [sourceValidity, ValidityOccurrence.prefixPath,
              ValidityOccurrence.beforeTarget]
            omega
          · have destination := node.jump_destination_le_upper_of_admissible
                { id := id, payload := .markedStrictUntil interval left right, parent := parent }
                interval sourceMem rfl admissible active.2
            simp [sourceValidity, ValidityOccurrence.prefixPath,
              ValidityOccurrence.beforeTarget]
            omega
      | markedStrictRelease interval left right =>
          simp only [AnnotatedOccurrence.postponedInvariant?, Option.some.injEq,
            Prod.mk.injEq] at sourceShape
          rcases sourceShape with ⟨rfl, rfl⟩
          simp only [AnnotatedOccurrence.interval?] at active
          let sourceValidity := ValidityOccurrence.prefixPath 1 (validity.through interval)
          refine ⟨sourceValidity, ?_, ?_, ?_, ?_⟩
          · change sourceValidity ∈ FormulaValidity.validityOccurrences
              (.strictRelease interval left right)
            simp only [sourceValidity, FormulaValidity.validityOccurrences,
              List.mem_append]
            exact Or.inr (List.mem_map.mpr ⟨validity, validityMem, rfl⟩)
          · simp [sourceValidity, ValidityOccurrence.prefixPath,
              ValidityOccurrence.through, List.append_assoc]
          · simp [sourceValidity, ValidityOccurrence.prefixPath,
              ValidityOccurrence.through]
            omega
          · have destination := node.jump_destination_le_upper_of_admissible
                { id := id, payload := .markedStrictRelease interval left right, parent := parent }
                interval sourceMem rfl admissible active.2
            simp [sourceValidity, ValidityOccurrence.prefixPath,
              ValidityOccurrence.through]
            omega

omit [DecidableEq Atom] in
/-- Compatibility wrapper for the conservative JUMP calculation. -/
theorem postponedInvariant_covered_by_source (node : Node Atom) {size offset : Nat}
    (computed : node.jumpSize? = some size) (strictlySkipped : offset < size)
    (source : AnnotatedOccurrence Atom) (sourceMem : source ∈ node.label)
    (edge : Nat) (invariant : Stlsat.Formula Atom)
    (sourceShape : source.postponedInvariant? = some (edge, invariant))
    (validity : ValidityOccurrence)
    (validityMem : validity ∈ FormulaValidity.validityOccurrences invariant)
    (active : match source.interval? with
      | some interval => interval.lower ≤ node.time ∧ node.time < interval.upper
      | none => False) :
    ∃ sourceValidity ∈ FormulaValidity.validityOccurrences source.formula,
      source.id ++ sourceValidity.path = source.id ++ [edge] ++ validity.path ∧
      sourceValidity.window.lower ≤ node.time + offset + validity.window.lower ∧
      node.time + offset + validity.window.upper ≤ sourceValidity.window.upper :=
  node.postponedInvariant_covered_by_source_of_admissible
    (node.jumpSizeAdmissible_of_computed computed) strictlySkipped source sourceMem edge
    invariant sourceShape validity validityMem active

omit [DecidableEq Atom] in
/-- Every validity occurrence of a live temporal formula is covered by an
`O(u)` window of its first live independent ancestor. -/
theorem validity_covered_by_independent_ancestor (node : Node Atom)
    (provenance : node.ProvenanceValid)
    (source : AnnotatedOccurrence Atom) (sourceMem : source ∈ node.label)
    (sourceTemporal : source.isTemporal = true)
    (validity : ValidityOccurrence)
    (validityMem : validity ∈ FormulaValidity.validityOccurrences source.formula) :
    ∃ window ∈ node.independentWindows,
      window.id = source.id ++ validity.path ∧
      window.window.lower ≤ validity.window.lower ∧
      validity.window.upper ≤ window.window.upper := by
  by_cases independent : ¬node.ParentActive source
  · let window := WindowOccurrence.ofValidity source.id validity
    refine ⟨window, node.independentWindow_mem source sourceMem sourceTemporal independent
      validity validityMem, ?_, le_rfl, le_rfl⟩
    rfl
  · have parentActive : node.ParentActive source := Classical.not_not.mp independent
    rcases parentActive with ⟨_, activeParent⟩
    cases parentEq : source.parent with
    | none => simp [parentEq] at activeParent
    | some parentRef =>
        rw [parentEq] at activeParent
        rcases activeParent with ⟨parent, parentMem, parentReference⟩
        cases parentRef with
        | mk parentId parentFormula parentParent =>
            have sourceLink := provenance source sourceMem
            simp only [AnnotatedOccurrence.ParentLinkValid, parentEq] at sourceLink
            rcases sourceLink with ⟨parentTemporalFormula, covered⟩
            have validityFromMem : validity ∈
                FormulaValidity.validityFrom node.time source.formula := by
              rw [FormulaValidity.validityFrom_temporal node.time _
                ((AnnotatedOccurrence.formula_isTemporal source).trans sourceTemporal)]
              exact validityMem
            rcases covered validity validityFromMem with
              ⟨parentValidity, parentValidityMem, canonicalId, lower, upper⟩
            have parentData : parent.id = parentId ∧
                parent.formula = parentFormula ∧ parent.parent = parentParent := by
              cases parent with
              | mk id payload parent =>
                  simp only [AnnotatedOccurrence.reference, OccurrenceRef.mk.injEq]
                    at parentReference
                  simpa using parentReference
            have parentTemporal : parent.isTemporal = true := by
              rw [← AnnotatedOccurrence.formula_isTemporal, parentData.2.1]
              exact parentTemporalFormula
            have parentValidityMem' : parentValidity ∈
                FormulaValidity.validityOccurrences parent.formula := by
              simpa [parentData.2.1] using parentValidityMem
            rcases node.validity_covered_by_independent_ancestor provenance parent parentMem
                parentTemporal parentValidity parentValidityMem' with
              ⟨window, windowMem, windowId, ancestorLower, ancestorUpper⟩
            refine ⟨window, windowMem, ?_, ?_, ?_⟩
            · rw [windowId, parentData.1]
              exact canonicalId
            · exact ancestorLower.trans lower
            · exact upper.trans ancestorUpper
termination_by source.reference.depth
decreasing_by
  simp [AnnotatedOccurrence.reference, parentEq, parentData, OccurrenceRef.depth]

omit [DecidableEq Atom] in
/-- Parent-active skipped invariant leaves have the same independent-ancestor
coverage as independent sources. -/
theorem postponedInvariant_covered_by_independent_ancestor_of_admissible
    (node : Node Atom)
    {size offset : Nat} (admissible : node.JumpSizeAdmissible size)
    (strictlySkipped : offset < size) (provenance : node.ProvenanceValid)
    (source : AnnotatedOccurrence Atom) (sourceMem : source ∈ node.label)
    (sourceTemporal : source.isTemporal = true)
    (edge : Nat) (invariant : Stlsat.Formula Atom)
    (sourceShape : source.postponedInvariant? = some (edge, invariant))
    (validity : ValidityOccurrence)
    (validityMem : validity ∈ FormulaValidity.validityOccurrences invariant)
    (active : match source.interval? with
      | some interval => interval.lower ≤ node.time ∧ node.time < interval.upper
      | none => False) :
    ∃ window ∈ node.independentWindows,
      window.id = source.id ++ [edge] ++ validity.path ∧
      window.window.lower ≤ node.time + offset + validity.window.lower ∧
      node.time + offset + validity.window.upper ≤ window.window.upper := by
  rcases node.postponedInvariant_covered_by_source_of_admissible admissible strictlySkipped
      source sourceMem edge invariant sourceShape validity validityMem active with
    ⟨sourceValidity, sourceValidityMem, sourceId, sourceLower, sourceUpper⟩
  rcases node.validity_covered_by_independent_ancestor provenance source sourceMem
      sourceTemporal sourceValidity sourceValidityMem with
    ⟨window, windowMem, windowId, ancestorLower, ancestorUpper⟩
  refine ⟨window, windowMem, ?_, ancestorLower.trans sourceLower,
    sourceUpper.trans ancestorUpper⟩
  rw [windowId, sourceId]

omit [DecidableEq Atom] in
/-- Compatibility wrapper for the conservative JUMP calculation. -/
theorem postponedInvariant_covered_by_independent_ancestor (node : Node Atom)
    {size offset : Nat} (computed : node.jumpSize? = some size)
    (strictlySkipped : offset < size) (provenance : node.ProvenanceValid)
    (source : AnnotatedOccurrence Atom) (sourceMem : source ∈ node.label)
    (sourceTemporal : source.isTemporal = true)
    (edge : Nat) (invariant : Stlsat.Formula Atom)
    (sourceShape : source.postponedInvariant? = some (edge, invariant))
    (validity : ValidityOccurrence)
    (validityMem : validity ∈ FormulaValidity.validityOccurrences invariant)
    (active : match source.interval? with
      | some interval => interval.lower ≤ node.time ∧ node.time < interval.upper
      | none => False) :
    ∃ window ∈ node.independentWindows,
      window.id = source.id ++ [edge] ++ validity.path ∧
      window.window.lower ≤ node.time + offset + validity.window.lower ∧
      node.time + offset + validity.window.upper ≤ window.window.upper :=
  node.postponedInvariant_covered_by_independent_ancestor_of_admissible
    (node.jumpSizeAdmissible_of_computed computed) strictlySkipped provenance source sourceMem
    sourceTemporal edge invariant sourceShape validity validityMem active

omit [DecidableEq Atom] in
private theorem isTemporal_of_postponedInvariant
    (occurrence : AnnotatedOccurrence Atom) {edge : Nat}
    {invariant : Stlsat.Formula Atom}
    (shape : occurrence.postponedInvariant? = some (edge, invariant)) :
    occurrence.isTemporal = true := by
  cases occurrence with
  | mk id payload parent =>
      cases payload <;>
        simp_all [AnnotatedOccurrence.postponedInvariant?,
          AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal]

omit [DecidableEq Atom] in
/-- The soundness guard compares every skipped invariant leaf against every
other skipped invariant leaf, including the parent-active case, through the
other leaf's first independent temporal ancestor. -/
theorem skippedInvariants_disjoint (node : Node Atom)
    {size firstOffset secondOffset : Nat}
    (computed : node.jumpSize? = some size) (sound : node.SoundSafe)
    (provenance : node.ProvenanceValid)
    (firstSkipped : firstOffset < size) (secondSkipped : secondOffset < size)
    (first : AnnotatedOccurrence Atom) (firstMem : first ∈ node.label)
    (firstEdge : Nat) (firstInvariant : Stlsat.Formula Atom)
    (firstShape : first.postponedInvariant? = some (firstEdge, firstInvariant))
    (firstValidity : ValidityOccurrence)
    (firstValidityMem : firstValidity ∈
      FormulaValidity.validityOccurrences firstInvariant)
    (second : AnnotatedOccurrence Atom) (secondMem : second ∈ node.label)
    (secondEdge : Nat) (secondInvariant : Stlsat.Formula Atom)
    (secondShape : second.postponedInvariant? = some (secondEdge, secondInvariant))
    (secondValidity : ValidityOccurrence)
    (secondValidityMem : secondValidity ∈
      FormulaValidity.validityOccurrences secondInvariant)
    (secondActive : match second.interval? with
      | some interval => interval.lower ≤ node.time ∧ node.time < interval.upper
      | none => False)
    (distinct : first.id ++ [firstEdge] ++ firstValidity.path ≠
      second.id ++ [secondEdge] ++ secondValidity.path) :
    ¬∃ instant,
      node.time + firstOffset + firstValidity.window.lower ≤ instant ∧
      instant ≤ node.time + firstOffset + firstValidity.window.upper ∧
      node.time + secondOffset + secondValidity.window.lower ≤ instant ∧
      instant ≤ node.time + secondOffset + secondValidity.window.upper := by
  rintro ⟨instant, firstLower, firstUpper, secondLower, secondUpper⟩
  let firstWindow :=
    (WindowOccurrence.ofValidity (first.id ++ [firstEdge]) firstValidity).shift node.time
  have firstWindowMem : firstWindow ∈ node.invariantWindows :=
    node.invariantWindow_mem first firstMem firstEdge firstInvariant firstShape
      firstValidity firstValidityMem
  have secondTemporal := isTemporal_of_postponedInvariant second secondShape
  rcases node.postponedInvariant_covered_by_independent_ancestor computed secondSkipped
      provenance second secondMem secondTemporal secondEdge secondInvariant secondShape
      secondValidity secondValidityMem secondActive with
    ⟨secondWindow, secondWindowMem, secondId, coveringLower, coveringUpper⟩
  have windowDistinct : firstWindow.id ≠ secondWindow.id := by
    intro equal
    apply distinct
    simpa [firstWindow, WindowOccurrence.shift, WindowOccurrence.ofValidity,
      List.append_assoc, secondId] using equal
  have disjoint := node.shiftedInvariant_disjoint computed sound firstSkipped
    firstWindow secondWindow firstWindowMem secondWindowMem windowDistinct
  apply disjoint
  constructor
  · simp only [firstWindow, WindowOccurrence.shift, WindowOccurrence.ofValidity,
      Stlsat.Interval.shift]
    omega
  · simp only [firstWindow, WindowOccurrence.shift, WindowOccurrence.ofValidity,
      Stlsat.Interval.shift]
    omega

omit [DecidableEq Atom] in
/-- A strictly skipped invariant instance is separated from every distinct
leaf of every live temporal occurrence.  Parent-active occurrences are
covered through their first independent ancestor. -/
theorem skippedInvariant_disjoint_from_liveTemporal (node : Node Atom)
    {size offset : Nat} (computed : node.jumpSize? = some size)
    (sound : node.SoundSafe) (provenance : node.ProvenanceValid)
    (strictlySkipped : offset < size)
    (source : AnnotatedOccurrence Atom) (sourceMem : source ∈ node.label)
    (edge : Nat) (invariant : Stlsat.Formula Atom)
    (sourceShape : source.postponedInvariant? = some (edge, invariant))
    (invariantValidity : ValidityOccurrence)
    (invariantMem : invariantValidity ∈
      FormulaValidity.validityOccurrences invariant)
    (other : AnnotatedOccurrence Atom) (otherMem : other ∈ node.label)
    (otherTemporal : other.isTemporal = true)
    (otherValidity : ValidityOccurrence)
    (otherValidityMem : otherValidity ∈
      FormulaValidity.validityOccurrences other.formula)
    (distinct : source.id ++ [edge] ++ invariantValidity.path ≠
      other.id ++ otherValidity.path) :
    ¬∃ instant,
      node.time + offset + invariantValidity.window.lower ≤ instant ∧
      instant ≤ node.time + offset + invariantValidity.window.upper ∧
      otherValidity.window.lower ≤ instant ∧
      instant ≤ otherValidity.window.upper := by
  rintro ⟨instant, invariantLower, invariantUpper, otherLower, otherUpper⟩
  let invariantWindow :=
    (WindowOccurrence.ofValidity (source.id ++ [edge]) invariantValidity).shift node.time
  have invariantWindowMem : invariantWindow ∈ node.invariantWindows :=
    node.invariantWindow_mem source sourceMem edge invariant sourceShape
      invariantValidity invariantMem
  rcases node.validity_covered_by_independent_ancestor provenance other otherMem
      otherTemporal otherValidity otherValidityMem with
    ⟨otherWindow, otherWindowMem, otherId, coveringLower, coveringUpper⟩
  have windowDistinct : invariantWindow.id ≠ otherWindow.id := by
    intro equal
    apply distinct
    simpa [invariantWindow, WindowOccurrence.shift, WindowOccurrence.ofValidity,
      List.append_assoc, otherId] using equal
  have disjoint := node.shiftedInvariant_disjoint computed sound strictlySkipped
    invariantWindow otherWindow invariantWindowMem otherWindowMem windowDistinct
  apply disjoint
  constructor
  · simp only [invariantWindow, WindowOccurrence.shift, WindowOccurrence.ofValidity,
      Stlsat.Interval.shift]
    omega
  · simp only [invariantWindow, WindowOccurrence.shift, WindowOccurrence.ofValidity,
      Stlsat.Interval.shift]
    omega

end Node
end Stlsat.Tableau
