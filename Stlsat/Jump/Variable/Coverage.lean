/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.AtomicSupport
import Stlsat.Jump.RankedSplicing

/-!
# Signed coverage for variable-aware windows

The original provenance argument produces unsigned ancestor windows.  This
module refines those witnesses with their signed semantic leaf and proves
that the refinement denotes the same canonical leaf.
-/

namespace Stlsat.Tableau

universe u

namespace Node

open FormulaValidity

variable {Atom : Type u} [DecidableEq Atom]

omit [DecidableEq Atom] in
private theorem supportedIndependent_of_independent
    (node : Node Atom) (canonical : node.CanonicalLeavesValid)
    (source : AnnotatedOccurrence Atom) (sourceMem : source ∈ node.label)
    (sourceLeaf : SemanticOccurrence Atom)
    (sourceLeafMem : sourceLeaf ∈ semanticOccurrences source.formula)
    (window : WindowOccurrence) (windowMem : window ∈ node.independentWindows)
    (identifier : window.id = source.id ++ sourceLeaf.path) :
    ∃ supported ∈ node.supportedIndependentWindows,
      supported.erase = window ∧ supported.leaf = sourceLeaf.leaf := by
  classical
  unfold independentWindows at windowMem
  rcases List.mem_flatMap.mp windowMem with ⟨ancestor, ancestorListMem, windowMem⟩
  have ancestorMem : ancestor ∈ node.label := Finset.mem_toList.mp ancestorListMem
  split at windowMem
  next selected =>
    rcases selected with ⟨ancestorTemporal, ancestorIndependent⟩
    change window ∈ (validityOccurrences ancestor.formula).map
      (WindowOccurrence.ofValidity ancestor.id) at windowMem
    rcases List.mem_map.mp windowMem with ⟨validity, validityMem, rfl⟩
    rcases exists_semanticOccurrence_of_mem validityMem with
      ⟨ancestorLeaf, ancestorLeafMem, ancestorValidity⟩
    let supported := SupportedWindowOccurrence.ofSemantic ancestor.id ancestorLeaf
    have supportedMem : supported ∈ node.supportedIndependentWindows :=
      node.supportedIndependentWindow_mem ancestor ancestorMem ancestorTemporal
        ancestorIndependent ancestorLeaf ancestorLeafMem
    have canonicalId : source.id ++ sourceLeaf.path =
        ancestor.id ++ ancestorLeaf.path := by
      have pathEq : ancestorLeaf.path = validity.path :=
        congrArg ValidityOccurrence.path ancestorValidity
      rw [← identifier, pathEq]
      rfl
    have sameLeaf := canonical source sourceMem ancestor ancestorMem sourceLeaf
      sourceLeafMem ancestorLeaf ancestorLeafMem canonicalId
    refine ⟨supported, supportedMem, ?_, sameLeaf.symm⟩
    change WindowOccurrence.ofValidity ancestor.id ancestorLeaf.toValidity =
      WindowOccurrence.ofValidity ancestor.id validity
    rw [ancestorValidity]
  next => simp at windowMem

omit [DecidableEq Atom] in
/-- A live temporal semantic leaf is covered by a signed independent ancestor
window carrying the same signed atom. -/
theorem semantic_covered_by_supportedIndependentAncestor
    (node : Node Atom) (provenance : node.ProvenanceValid)
    (canonical : node.CanonicalLeavesValid)
    (source : AnnotatedOccurrence Atom) (sourceMem : source ∈ node.label)
    (sourceTemporal : source.isTemporal = true)
    (leaf : SemanticOccurrence Atom)
    (leafMem : leaf ∈ semanticOccurrences source.formula) :
    ∃ window ∈ node.supportedIndependentWindows,
      window.id = source.id ++ leaf.path ∧ window.leaf = leaf.leaf ∧
      window.window.lower ≤ leaf.window.lower ∧
        leaf.window.upper ≤ window.window.upper := by
  have validityMem := toValidity_mem_validityOccurrences source.formula leaf leafMem
  rcases node.validity_covered_by_independent_ancestor provenance source sourceMem
      sourceTemporal leaf.toValidity validityMem with
    ⟨window, windowMem, identifier, lower, upper⟩
  rcases node.supportedIndependent_of_independent canonical source sourceMem leaf leafMem
      window windowMem identifier with ⟨supported, supportedMem, erased, sameLeaf⟩
  refine ⟨supported, supportedMem, ?_, sameLeaf, ?_, ?_⟩
  · simpa [SupportedWindowOccurrence.erase, SemanticOccurrence.toValidity] using
      (congrArg WindowOccurrence.id erased).trans identifier
  · have windowEq : supported.window = window.window :=
      congrArg WindowOccurrence.window erased
    rw [windowEq]
    exact lower
  · have windowEq : supported.window = window.window :=
      congrArg WindowOccurrence.window erased
    rw [windowEq]
    exact upper

/-- A semantic leaf of a skipped invariant is covered by a signed independent
ancestor window with the same leaf and with the original containment bounds. -/
theorem skippedSemantic_covered_by_supportedIndependentAncestor
    (node : Node Atom) {size offset : Nat}
    (computed : node.jumpSize? = some size) (strictlySkipped : offset < size)
    (derivation : node.FullDerivationValid)
    (source : AnnotatedOccurrence Atom) (sourceMem : source ∈ node.label)
    (edge : Nat) (invariant : Stlsat.Formula Atom)
    (shape : source.postponedInvariant? = some (edge, invariant))
    (leaf : SemanticOccurrence Atom)
    (leafMem : leaf ∈ semanticOccurrences invariant)
    (active : match source.interval? with
      | some interval => interval.lower ≤ node.time ∧ node.time < interval.upper
      | none => False) :
    ∃ window ∈ node.supportedIndependentWindows,
      window.id = source.id ++ [edge] ++ leaf.path ∧ window.leaf = leaf.leaf ∧
      window.window.lower ≤ node.time + offset + leaf.window.lower ∧
        node.time + offset + leaf.window.upper ≤ window.window.upper := by
  rcases postponedInvariant_semantic_source source shape (by
      cases intervalEq : source.interval? with
      | none => simp [intervalEq] at active
      | some interval =>
          rw [intervalEq] at active
          simp only
          omega) leaf leafMem with
    ⟨sourceLeaf, sourceLeafMem, sourceIdentifier, sourceLeafEq⟩
  have validityMem := toValidity_mem_validityOccurrences invariant leaf leafMem
  have sourceTemporal : source.isTemporal = true := by
    cases source with
    | mk id payload parent =>
        cases payload <;>
          simp_all [AnnotatedOccurrence.postponedInvariant?,
            AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal]
  rcases node.postponedInvariant_covered_by_independent_ancestor computed strictlySkipped
      derivation.1.1.1 source sourceMem sourceTemporal edge invariant shape leaf.toValidity
      validityMem active with ⟨window, windowMem, identifier, lower, upper⟩
  have sourceWindowId : window.id = source.id ++ sourceLeaf.path := by
    rw [identifier, sourceIdentifier]
    rfl
  rcases node.supportedIndependent_of_independent derivation.2 source sourceMem sourceLeaf
      sourceLeafMem window windowMem sourceWindowId with
    ⟨supported, supportedMem, erased, sameSourceLeaf⟩
  refine ⟨supported, supportedMem, ?_, sameSourceLeaf.trans sourceLeafEq, ?_, ?_⟩
  · simpa [SupportedWindowOccurrence.erase, SemanticOccurrence.toValidity] using
      (congrArg WindowOccurrence.id erased).trans identifier
  · have windowEq : supported.window = window.window :=
      congrArg WindowOccurrence.window erased
    rw [windowEq]
    exact lower
  · have windowEq : supported.window = window.window :=
      congrArg WindowOccurrence.window erased
    rw [windowEq]
    exact upper

omit [DecidableEq Atom] in
/-- Refine an unsigned `S(u)` witness to the signed conflict window carrying a
given canonical source leaf. -/
theorem semanticSource_covered_by_supportedConflict
    (node : Node Atom) (canonical : node.CanonicalLeavesValid)
    (source : AnnotatedOccurrence Atom) (sourceMem : source ∈ node.label)
    (sourceLeaf : SemanticOccurrence Atom)
    (sourceLeafMem : sourceLeaf ∈ semanticOccurrences source.formula)
    (conflict : WindowOccurrence) (conflictMem : conflict ∈ node.conflictWindows)
    (identifier : conflict.id = source.id ++ sourceLeaf.path) :
    ∃ supported ∈ node.supportedConflictWindows,
      supported.erase = conflict ∧ supported.leaf = sourceLeaf.leaf := by
  rcases List.mem_append.mp conflictMem with independentMem | atomicMem
  · rcases node.supportedIndependent_of_independent canonical source sourceMem
        sourceLeaf sourceLeafMem conflict independentMem identifier with
      ⟨supported, supportedMem, erased, leafEq⟩
    exact ⟨supported, List.mem_append.mpr (Or.inl supportedMem), erased, leafEq⟩
  · classical
    unfold atomicConflictWindows at atomicMem
    rcases List.mem_flatMap.mp atomicMem with ⟨atomOccurrence, atomListMem, atomicMem⟩
    have atomMem : atomOccurrence ∈ node.label := Finset.mem_toList.mp atomListMem
    by_cases parentActive : node.ParentActive atomOccurrence
    · simp [parentActive] at atomicMem
    · simp only [parentActive, if_false] at atomicMem
      cases atomOccurrence with
      | mk atomId payload parent =>
          cases payload with
          | unmarked formula =>
              cases formula with
              | atom atom =>
                  simp only [List.mem_singleton] at atomicMem
                  subst conflict
                  let atomLeaf : SemanticOccurrence Atom :=
                    { path := [], window := ⟨0, 0, le_rfl⟩, leaf := .positive atom }
                  have atomLeafMem : atomLeaf ∈ semanticOccurrences (.atom atom) := by
                    simp [atomLeaf, semanticOccurrences]
                  have canonicalId : source.id ++ sourceLeaf.path = atomId ++ atomLeaf.path := by
                    simpa [atomLeaf, WindowOccurrence.ofValidity] using identifier.symm
                  have sameLeaf := canonical source sourceMem
                    { id := atomId, payload := .unmarked (.atom atom), parent := parent }
                    atomMem sourceLeaf sourceLeafMem atomLeaf atomLeafMem canonicalId
                  let supported : SupportedWindowOccurrence Atom :=
                    { id := atomId, window := ⟨node.time, node.time, le_rfl⟩,
                      leaf := .positive atom }
                  have supportedMem : supported ∈ node.supportedAtomicConflictWindows :=
                    node.supportedPositiveAtomicWindow_mem
                      { id := atomId, payload := .unmarked (.atom atom), parent := parent }
                      atomMem parentActive atom rfl
                  refine ⟨supported, List.mem_append.mpr (Or.inr supportedMem), rfl, ?_⟩
                  exact sameLeaf.symm
              | neg body =>
                  cases body with
                  | atom atom =>
                      simp only [List.mem_singleton] at atomicMem
                      subst conflict
                      let atomLeaf : SemanticOccurrence Atom :=
                        { path := [0], window := ⟨0, 0, le_rfl⟩, leaf := .negative atom }
                      have atomLeafMem : atomLeaf ∈
                          semanticOccurrences (.neg (.atom atom)) := by
                        simp [atomLeaf, semanticOccurrences,
                          SemanticOccurrence.negate, SemanticOccurrence.prefixPath,
                          SignedLeaf.negate]
                      have canonicalId : source.id ++ sourceLeaf.path =
                          atomId ++ atomLeaf.path := by
                        simpa [atomLeaf, WindowOccurrence.ofValidity] using identifier.symm
                      have sameLeaf := canonical source sourceMem
                        { id := atomId, payload := .unmarked (.neg (.atom atom)),
                          parent := parent }
                        atomMem sourceLeaf sourceLeafMem atomLeaf atomLeafMem canonicalId
                      let supported : SupportedWindowOccurrence Atom :=
                        { id := atomId ++ [0],
                          window := ⟨node.time, node.time, le_rfl⟩,
                          leaf := .negative atom }
                      have supportedMem : supported ∈
                          node.supportedAtomicConflictWindows :=
                        node.supportedNegativeAtomicWindow_mem
                          { id := atomId, payload := .unmarked (.neg (.atom atom)),
                            parent := parent }
                          atomMem parentActive atom rfl
                      refine ⟨supported, List.mem_append.mpr (Or.inr supportedMem),
                        rfl, ?_⟩
                      exact sameLeaf.symm
                  | truth => simp at atomicMem
                  | neg nested => simp at atomicMem
                  | and left right => simp at atomicMem
                  | or left right => simp at atomicMem
                  | eventually interval nested => simp at atomicMem
                  | always interval nested => simp at atomicMem
                  | strictUntil interval left right => simp at atomicMem
                  | strictRelease interval left right => simp at atomicMem
              | truth => simp at atomicMem
              | and left right => simp at atomicMem
              | or left right => simp at atomicMem
              | eventually interval body => simp at atomicMem
              | always interval body => simp at atomicMem
              | strictUntil interval left right => simp at atomicMem
              | strictRelease interval left right => simp at atomicMem
          | markedEventually interval body => simp at atomicMem
          | markedAlways interval body => simp at atomicMem
          | markedStrictUntil interval left right => simp at atomicMem
          | markedStrictRelease interval left right => simp at atomicMem

end Node
end Stlsat.Tableau
