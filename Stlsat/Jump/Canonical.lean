/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.CompatibleSplicing

/-!
# Canonical signed leaves

Stable occurrence identifiers name signed syntax leaves.  This file proves
that rule derivations never assign two different signed leaves to the same
identifier.
-/

namespace Stlsat.Jump
universe u
namespace FormulaValidity

variable {Atom : Type u}

/-- Inside one formula, a syntax path determines its signed leaf. -/
theorem semanticOccurrences_leaf_of_path_eq (formula : Stlsat.Formula Atom)
    {left right : SemanticOccurrence Atom}
    (leftMem : left ∈ semanticOccurrences formula)
    (rightMem : right ∈ semanticOccurrences formula)
    (path : left.path = right.path) : left.leaf = right.leaf := by
  induction formula generalizing left right with
  | truth =>
      simp only [semanticOccurrences, List.mem_singleton] at leftMem rightMem
      subst left
      subst right
      rfl
  | atom atom =>
      simp only [semanticOccurrences, List.mem_singleton] at leftMem rightMem
      subst left
      subst right
      rfl
  | neg body ih =>
      rcases List.mem_map.mp leftMem with ⟨leftSource, leftSourceMem, rfl⟩
      rcases List.mem_map.mp rightMem with ⟨rightSource, rightSourceMem, rfl⟩
      have sourcePath : leftSource.path = rightSource.path := by
        simpa [SemanticOccurrence.prefixPath, SemanticOccurrence.negate] using path
      have sourceLeaf := ih leftSourceMem rightSourceMem sourcePath
      simpa [SemanticOccurrence.prefixPath, SemanticOccurrence.negate] using
        congrArg SignedLeaf.negate sourceLeaf
  | and left right ihLeft ihRight =>
      simp only [semanticOccurrences, List.mem_append, List.mem_map] at leftMem rightMem
      rcases leftMem with ⟨leftSource, leftSourceMem, rfl⟩ |
          ⟨leftSource, leftSourceMem, rfl⟩ <;>
        rcases rightMem with ⟨rightSource, rightSourceMem, rfl⟩ |
          ⟨rightSource, rightSourceMem, rfl⟩
      · apply ihLeft leftSourceMem rightSourceMem
        simpa [SemanticOccurrence.prefixPath] using path
      · simp [SemanticOccurrence.prefixPath] at path
      · simp [SemanticOccurrence.prefixPath] at path
      · apply ihRight leftSourceMem rightSourceMem
        simpa [SemanticOccurrence.prefixPath] using path
  | or left right ihLeft ihRight =>
      simp only [semanticOccurrences, List.mem_append, List.mem_map] at leftMem rightMem
      rcases leftMem with ⟨leftSource, leftSourceMem, rfl⟩ |
          ⟨leftSource, leftSourceMem, rfl⟩ <;>
        rcases rightMem with ⟨rightSource, rightSourceMem, rfl⟩ |
          ⟨rightSource, rightSourceMem, rfl⟩
      · apply ihLeft leftSourceMem rightSourceMem
        simpa [SemanticOccurrence.prefixPath] using path
      · simp [SemanticOccurrence.prefixPath] at path
      · simp [SemanticOccurrence.prefixPath] at path
      · apply ihRight leftSourceMem rightSourceMem
        simpa [SemanticOccurrence.prefixPath] using path
  | eventually interval body ih =>
      rcases List.mem_map.mp leftMem with ⟨leftSource, leftSourceMem, rfl⟩
      rcases List.mem_map.mp rightMem with ⟨rightSource, rightSourceMem, rfl⟩
      apply ih leftSourceMem rightSourceMem
      simpa [SemanticOccurrence.prefixPath, SemanticOccurrence.through] using path
  | always interval body ih =>
      rcases List.mem_map.mp leftMem with ⟨leftSource, leftSourceMem, rfl⟩
      rcases List.mem_map.mp rightMem with ⟨rightSource, rightSourceMem, rfl⟩
      apply ih leftSourceMem rightSourceMem
      simpa [SemanticOccurrence.prefixPath, SemanticOccurrence.through] using path
  | strictUntil interval invariant target ihInvariant ihTarget =>
      by_cases nontrivial : interval.lower < interval.upper
      · simp only [semanticOccurrences, dif_pos nontrivial, List.mem_append,
          List.mem_map] at leftMem rightMem
        rcases leftMem with ⟨leftSource, leftSourceMem, rfl⟩ |
            ⟨leftSource, leftSourceMem, rfl⟩ <;>
          rcases rightMem with ⟨rightSource, rightSourceMem, rfl⟩ |
            ⟨rightSource, rightSourceMem, rfl⟩
        · apply ihInvariant leftSourceMem rightSourceMem
          simpa [SemanticOccurrence.prefixPath, SemanticOccurrence.beforeTarget] using path
        · simp [SemanticOccurrence.prefixPath] at path
        · simp [SemanticOccurrence.prefixPath] at path
        · apply ihTarget leftSourceMem rightSourceMem
          simpa [SemanticOccurrence.prefixPath, SemanticOccurrence.through] using path
      · simp only [semanticOccurrences, dif_neg nontrivial, List.nil_append,
          List.mem_map] at leftMem rightMem
        rcases leftMem with ⟨leftSource, leftSourceMem, rfl⟩
        rcases rightMem with ⟨rightSource, rightSourceMem, rfl⟩
        apply ihTarget leftSourceMem rightSourceMem
        simpa [SemanticOccurrence.prefixPath, SemanticOccurrence.through] using path
  | strictRelease interval target invariant ihTarget ihInvariant =>
      by_cases nontrivial : interval.lower < interval.upper
      · simp only [semanticOccurrences, dif_pos nontrivial, List.mem_append,
          List.mem_map] at leftMem rightMem
        rcases leftMem with ⟨leftSource, leftSourceMem, rfl⟩ |
            ⟨leftSource, leftSourceMem, rfl⟩ <;>
          rcases rightMem with ⟨rightSource, rightSourceMem, rfl⟩ |
            ⟨rightSource, rightSourceMem, rfl⟩
        · apply ihTarget leftSourceMem rightSourceMem
          simpa [SemanticOccurrence.prefixPath, SemanticOccurrence.beforeTarget] using path
        · simp [SemanticOccurrence.prefixPath] at path
        · simp [SemanticOccurrence.prefixPath] at path
        · apply ihInvariant leftSourceMem rightSourceMem
          simpa [SemanticOccurrence.prefixPath, SemanticOccurrence.through] using path
      · simp only [semanticOccurrences, dif_neg nontrivial, List.nil_append,
          List.mem_map] at leftMem rightMem
        rcases leftMem with ⟨leftSource, leftSourceMem, rfl⟩
        rcases rightMem with ⟨rightSource, rightSourceMem, rfl⟩
        apply ihInvariant leftSourceMem rightSourceMem
        simpa [SemanticOccurrence.prefixPath, SemanticOccurrence.through] using path

/-- Temporal expansion changes windows but neither paths nor signed leaves. -/
theorem semanticOccurrences_temporalExpansion_source
    (formula : Stlsat.Formula Atom) (time : Nat)
    (expanded : SemanticOccurrence Atom)
    (expandedMem : expanded ∈ semanticOccurrences (formula.temporalExpansion time)) :
    ∃ source ∈ semanticOccurrences formula,
      source.path = expanded.path ∧ source.leaf = expanded.leaf := by
  induction formula generalizing expanded with
  | truth =>
      exact ⟨expanded, by
        simpa [Stlsat.Formula.temporalExpansion, semanticOccurrences] using expandedMem,
        rfl, rfl⟩
  | atom atom =>
      exact ⟨expanded, by
        simpa [Stlsat.Formula.temporalExpansion, semanticOccurrences] using expandedMem,
        rfl, rfl⟩
  | neg body ih =>
      rcases List.mem_map.mp expandedMem with ⟨child, childMem, rfl⟩
      rcases ih child childMem with ⟨source, sourceMem, sourcePath, sourceLeaf⟩
      refine ⟨(source.negate).prefixPath 0, List.mem_map.mpr ⟨source, sourceMem, rfl⟩,
        ?_, ?_⟩
      · simp [SemanticOccurrence.prefixPath, SemanticOccurrence.negate, sourcePath]
      · simp [SemanticOccurrence.prefixPath, SemanticOccurrence.negate, sourceLeaf]
  | and left right ihLeft ihRight =>
      simp only [Stlsat.Formula.temporalExpansion, semanticOccurrences,
        List.mem_append, List.mem_map] at expandedMem
      rcases expandedMem with ⟨child, childMem, rfl⟩ | ⟨child, childMem, rfl⟩
      · rcases ihLeft child childMem with ⟨source, sourceMem, sourcePath, sourceLeaf⟩
        exact ⟨source.prefixPath 0, List.mem_append.mpr
          (Or.inl (List.mem_map.mpr ⟨source, sourceMem, rfl⟩)), by
            simp [SemanticOccurrence.prefixPath, sourcePath], by
            simp [SemanticOccurrence.prefixPath, sourceLeaf]⟩
      · rcases ihRight child childMem with ⟨source, sourceMem, sourcePath, sourceLeaf⟩
        exact ⟨source.prefixPath 1, List.mem_append.mpr
          (Or.inr (List.mem_map.mpr ⟨source, sourceMem, rfl⟩)), by
            simp [SemanticOccurrence.prefixPath, sourcePath], by
            simp [SemanticOccurrence.prefixPath, sourceLeaf]⟩
  | or left right ihLeft ihRight =>
      simp only [Stlsat.Formula.temporalExpansion, semanticOccurrences,
        List.mem_append, List.mem_map] at expandedMem
      rcases expandedMem with ⟨child, childMem, rfl⟩ | ⟨child, childMem, rfl⟩
      · rcases ihLeft child childMem with ⟨source, sourceMem, sourcePath, sourceLeaf⟩
        exact ⟨source.prefixPath 0, List.mem_append.mpr
          (Or.inl (List.mem_map.mpr ⟨source, sourceMem, rfl⟩)), by
            simp [SemanticOccurrence.prefixPath, sourcePath], by
            simp [SemanticOccurrence.prefixPath, sourceLeaf]⟩
      · rcases ihRight child childMem with ⟨source, sourceMem, sourcePath, sourceLeaf⟩
        exact ⟨source.prefixPath 1, List.mem_append.mpr
          (Or.inr (List.mem_map.mpr ⟨source, sourceMem, rfl⟩)), by
            simp [SemanticOccurrence.prefixPath, sourcePath], by
            simp [SemanticOccurrence.prefixPath, sourceLeaf]⟩
  | eventually interval body ih =>
      simp only [Stlsat.Formula.temporalExpansion, semanticOccurrences,
        List.mem_map] at expandedMem
      rcases expandedMem with ⟨child, childMem, rfl⟩
      refine ⟨(child.through interval).prefixPath 0,
        List.mem_map.mpr ⟨child, childMem, rfl⟩, ?_, ?_⟩ <;>
        simp [SemanticOccurrence.prefixPath, SemanticOccurrence.through]
  | always interval body ih =>
      simp only [Stlsat.Formula.temporalExpansion, semanticOccurrences,
        List.mem_map] at expandedMem
      rcases expandedMem with ⟨child, childMem, rfl⟩
      refine ⟨(child.through interval).prefixPath 0,
        List.mem_map.mpr ⟨child, childMem, rfl⟩, ?_, ?_⟩ <;>
        simp [SemanticOccurrence.prefixPath, SemanticOccurrence.through]
  | strictUntil interval left right ihLeft ihRight =>
      simp only [Stlsat.Formula.temporalExpansion, semanticOccurrences] at expandedMem
      have nontrivial : interval.lower < interval.upper ↔
          (interval.shift time).lower < (interval.shift time).upper := by
        simp [Stlsat.Interval.shift]
      split at expandedMem <;> rename_i shifted
      · have original := nontrivial.mpr shifted
        simp only [List.mem_append, List.mem_map] at expandedMem
        rcases expandedMem with ⟨child, childMem, rfl⟩ | ⟨child, childMem, rfl⟩
        · refine ⟨(child.beforeTarget interval original).prefixPath 0, ?_, ?_, ?_⟩
          · simp only [semanticOccurrences, dif_pos original, List.mem_append]
            exact Or.inl (List.mem_map.mpr ⟨child, childMem, rfl⟩)
          · simp [SemanticOccurrence.prefixPath, SemanticOccurrence.beforeTarget]
          · simp [SemanticOccurrence.prefixPath, SemanticOccurrence.beforeTarget]
        · refine ⟨(child.through interval).prefixPath 1, ?_, ?_, ?_⟩
          · simp only [semanticOccurrences, List.mem_append]
            exact Or.inr (List.mem_map.mpr ⟨child, childMem, rfl⟩)
          · simp [SemanticOccurrence.prefixPath, SemanticOccurrence.through]
          · simp [SemanticOccurrence.prefixPath, SemanticOccurrence.through]
      · have original : ¬interval.lower < interval.upper := by
          simpa [nontrivial] using shifted
        simp only [List.nil_append, List.mem_map] at expandedMem
        rcases expandedMem with ⟨child, childMem, rfl⟩
        refine ⟨(child.through interval).prefixPath 1, ?_, ?_, ?_⟩
        · simp only [semanticOccurrences, dif_neg original, List.nil_append]
          exact List.mem_map.mpr ⟨child, childMem, rfl⟩
        · simp [SemanticOccurrence.prefixPath, SemanticOccurrence.through]
        · simp [SemanticOccurrence.prefixPath, SemanticOccurrence.through]
  | strictRelease interval left right ihLeft ihRight =>
      simp only [Stlsat.Formula.temporalExpansion, semanticOccurrences] at expandedMem
      have nontrivial : interval.lower < interval.upper ↔
          (interval.shift time).lower < (interval.shift time).upper := by
        simp [Stlsat.Interval.shift]
      split at expandedMem <;> rename_i shifted
      · have original := nontrivial.mpr shifted
        simp only [List.mem_append, List.mem_map] at expandedMem
        rcases expandedMem with ⟨child, childMem, rfl⟩ | ⟨child, childMem, rfl⟩
        · refine ⟨(child.beforeTarget interval original).prefixPath 0, ?_, ?_, ?_⟩
          · simp only [semanticOccurrences, dif_pos original, List.mem_append]
            exact Or.inl (List.mem_map.mpr ⟨child, childMem, rfl⟩)
          · simp [SemanticOccurrence.prefixPath, SemanticOccurrence.beforeTarget]
          · simp [SemanticOccurrence.prefixPath, SemanticOccurrence.beforeTarget]
        · refine ⟨(child.through interval).prefixPath 1, ?_, ?_, ?_⟩
          · simp only [semanticOccurrences, List.mem_append]
            exact Or.inr (List.mem_map.mpr ⟨child, childMem, rfl⟩)
          · simp [SemanticOccurrence.prefixPath, SemanticOccurrence.through]
          · simp [SemanticOccurrence.prefixPath, SemanticOccurrence.through]
      · have original : ¬interval.lower < interval.upper := by
          simpa [nontrivial] using shifted
        simp only [List.nil_append, List.mem_map] at expandedMem
        rcases expandedMem with ⟨child, childMem, rfl⟩
        refine ⟨(child.through interval).prefixPath 1, ?_, ?_, ?_⟩
        · simp only [semanticOccurrences, dif_neg original, List.nil_append]
          exact List.mem_map.mpr ⟨child, childMem, rfl⟩
        · simp [SemanticOccurrence.prefixPath, SemanticOccurrence.through]
        · simp [SemanticOccurrence.prefixPath, SemanticOccurrence.through]

end FormulaValidity

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

/-- Stable identifiers determine signed leaves throughout a derived label. -/
def CanonicalLeavesValid (node : Node Atom) : Prop :=
  ∀ first ∈ node.label, ∀ second ∈ node.label,
    ∀ firstLeaf ∈ FormulaValidity.semanticOccurrences first.formula,
      ∀ secondLeaf ∈ FormulaValidity.semanticOccurrences second.formula,
        first.id ++ firstLeaf.path = second.id ++ secondLeaf.path →
          firstLeaf.leaf = secondLeaf.leaf

omit [DecidableEq Atom] in
theorem initial_canonicalLeavesValid (formula : Stlsat.Formula Atom) :
    (Node.initial formula).CanonicalLeavesValid := by
  intro first firstMem second secondMem firstLeaf firstLeafMem secondLeaf secondLeafMem ids
  simp only [Node.initial, Finset.mem_singleton] at firstMem secondMem
  subst first
  subst second
  apply FormulaValidity.semanticOccurrences_leaf_of_path_eq formula firstLeafMem secondLeafMem
  simpa using ids

/-- Canonical-leaf validity is preserved by a replacement whenever every new
leaf embeds into a leaf of the selected old occurrence. -/
theorem canonicalLeavesValid_replace {node : Node Atom}
    {selected : AnnotatedOccurrence Atom}
    {replacement : List (AnnotatedOccurrence Atom)}
    (valid : node.CanonicalLeavesValid) (selectedMem : selected ∈ node.label)
    (embeds : ∀ fresh ∈ replacement,
      ∀ freshLeaf ∈ FormulaValidity.semanticOccurrences fresh.formula,
        ∃ selectedLeaf ∈ FormulaValidity.semanticOccurrences selected.formula,
          selected.id ++ selectedLeaf.path = fresh.id ++ freshLeaf.path ∧
            selectedLeaf.leaf = freshLeaf.leaf) :
    (node.replace selected replacement).CanonicalLeavesValid := by
  intro first firstMem second secondMem firstLeaf firstLeafMem secondLeaf secondLeafMem ids
  change first ∈ node.label.erase selected ∪ replacement.toFinset at firstMem
  change second ∈ node.label.erase selected ∪ replacement.toFinset at secondMem
  rcases Finset.mem_union.mp firstMem with firstOld | firstFresh
  · have firstOldMem := Finset.mem_of_mem_erase firstOld
    rcases Finset.mem_union.mp secondMem with secondOld | secondFresh
    · exact valid first firstOldMem second (Finset.mem_of_mem_erase secondOld)
        firstLeaf firstLeafMem secondLeaf secondLeafMem ids
    · rcases embeds second (by simpa using secondFresh) secondLeaf secondLeafMem with
        ⟨selectedLeaf, selectedLeafMem, selectedId, selectedLeafEq⟩
      rw [← selectedLeafEq]
      apply valid first firstOldMem selected selectedMem firstLeaf firstLeafMem
        selectedLeaf selectedLeafMem
      rw [selectedId]
      exact ids
  · rcases embeds first (by simpa using firstFresh) firstLeaf firstLeafMem with
      ⟨firstSelected, firstSelectedMem, firstId, firstLeafEq⟩
    rcases Finset.mem_union.mp secondMem with secondOld | secondFresh
    · rw [← firstLeafEq]
      apply valid selected selectedMem second (Finset.mem_of_mem_erase secondOld)
        firstSelected firstSelectedMem secondLeaf secondLeafMem
      rw [firstId]
      exact ids
    · rcases embeds second (by simpa using secondFresh) secondLeaf secondLeafMem with
        ⟨secondSelected, secondSelectedMem, secondId, secondLeafEq⟩
      rw [← firstLeafEq, ← secondLeafEq]
      apply FormulaValidity.semanticOccurrences_leaf_of_path_eq selected.formula
        firstSelectedMem secondSelectedMem
      have canonical : selected.id ++ firstSelected.path =
          selected.id ++ secondSelected.path := by
        rw [firstId, secondId]
        exact ids
      exact List.append_cancel_left canonical

end Node

namespace Expansion

variable {Atom : Type u} [DecidableEq Atom]

omit [DecidableEq Atom] in
private theorem expandedChildSource (formula : Stlsat.Formula Atom) (time _edge : Nat)
    (fresh : FormulaValidity.SemanticOccurrence Atom)
    (freshMem : fresh ∈ FormulaValidity.semanticOccurrences
      (formula.temporalExpansion time)) :
    ∃ source ∈ FormulaValidity.semanticOccurrences formula,
      (source.path = fresh.path) ∧ source.leaf = fresh.leaf :=
  FormulaValidity.semanticOccurrences_temporalExpansion_source formula time fresh freshMem

/-- Formula expansion preserves the canonical signed-leaf invariant. -/
theorem child_canonicalLeavesValid {node child : Node Atom}
    {children : List (Node Atom)} (expansion : Expansion node children)
    (valid : node.CanonicalLeavesValid) (childMem : child ∈ children) :
    child.CanonicalLeavesValid := by
  cases expansion with
  | disjunction selected left right shape present =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      rcases childMem with rfl | rfl
      · apply Node.canonicalLeavesValid_replace valid present
        intro fresh freshMem leaf leafMem
        simp only [List.mem_singleton] at freshMem
        subst fresh
        refine ⟨leaf.prefixPath 0, ?_, ?_, rfl⟩
        · have selectedFormula : selected.formula = .or left right := by
            cases selected with
            | mk id payload parent =>
                change payload = .unmarked (.or left right) at shape
                subst payload
                rfl
          rw [selectedFormula]
          exact List.mem_append.mpr (Or.inl
            (List.mem_map.mpr ⟨leaf, leafMem, rfl⟩))
        · simp [AnnotatedOccurrence.child, FormulaValidity.SemanticOccurrence.prefixPath,
            List.append_assoc]
      · apply Node.canonicalLeavesValid_replace valid present
        intro fresh freshMem leaf leafMem
        simp only [List.mem_singleton] at freshMem
        subst fresh
        refine ⟨leaf.prefixPath 1, ?_, ?_, rfl⟩
        · have selectedFormula : selected.formula = .or left right := by
            cases selected with
            | mk id payload parent =>
                change payload = .unmarked (.or left right) at shape
                subst payload
                rfl
          rw [selectedFormula]
          exact List.mem_append.mpr (Or.inr
            (List.mem_map.mpr ⟨leaf, leafMem, rfl⟩))
        · simp [AnnotatedOccurrence.child, FormulaValidity.SemanticOccurrence.prefixPath,
            List.append_assoc]
  | conjunction selected left right shape present =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.canonicalLeavesValid_replace valid present
      intro fresh freshMem leaf leafMem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at freshMem
      rcases freshMem with rfl | rfl
      · refine ⟨leaf.prefixPath 0, ?_, ?_, rfl⟩
        · have selectedFormula : selected.formula = .and left right := by
            cases selected with
            | mk id payload parent =>
                change payload = .unmarked (.and left right) at shape
                subst payload
                rfl
          rw [selectedFormula]
          exact List.mem_append.mpr (Or.inl
            (List.mem_map.mpr ⟨leaf, leafMem, rfl⟩))
        · simp [AnnotatedOccurrence.child, FormulaValidity.SemanticOccurrence.prefixPath,
            List.append_assoc]
      · refine ⟨leaf.prefixPath 1, ?_, ?_, rfl⟩
        · have selectedFormula : selected.formula = .and left right := by
            cases selected with
            | mk id payload parent =>
                change payload = .unmarked (.and left right) at shape
                subst payload
                rfl
          rw [selectedFormula]
          exact List.mem_append.mpr (Or.inr
            (List.mem_map.mpr ⟨leaf, leafMem, rfl⟩))
        · simp [AnnotatedOccurrence.child, FormulaValidity.SemanticOccurrence.prefixPath,
            List.append_assoc]
  | eventuallyBeforeEnd selected interval body shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      rcases childMem with rfl | rfl
      · apply Node.canonicalLeavesValid_replace valid present
        intro fresh freshMem leaf leafMem
        simp only [List.mem_singleton] at freshMem
        subst fresh
        rcases expandedChildSource body node.time 0 leaf leafMem with
          ⟨source, sourceMem, sourcePath, sourceLeaf⟩
        refine ⟨(source.through interval).prefixPath 0, ?_, ?_, ?_⟩
        · simpa [AnnotatedOccurrence.formula, shape,
            FormulaValidity.semanticOccurrences] using
            List.mem_map.mpr ⟨source, sourceMem, rfl⟩
        · simp [AnnotatedOccurrence.child, FormulaValidity.SemanticOccurrence.prefixPath,
            FormulaValidity.SemanticOccurrence.through, sourcePath, List.append_assoc]
        · simpa [FormulaValidity.SemanticOccurrence.prefixPath,
            FormulaValidity.SemanticOccurrence.through] using sourceLeaf
      · apply Node.canonicalLeavesValid_replace valid present
        intro fresh freshMem leaf leafMem
        simp only [List.mem_singleton] at freshMem
        subst fresh
        refine ⟨leaf, ?_, ?_, rfl⟩
        · simpa [AnnotatedOccurrence.relabel, AnnotatedOccurrence.formula, shape] using leafMem
        · simp [AnnotatedOccurrence.relabel]
  | eventuallyAtEnd selected interval body shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.canonicalLeavesValid_replace valid present
      intro fresh freshMem leaf leafMem
      simp only [List.mem_singleton] at freshMem
      subst fresh
      rcases expandedChildSource body node.time 0 leaf leafMem with
        ⟨source, sourceMem, sourcePath, sourceLeaf⟩
      refine ⟨(source.through interval).prefixPath 0, ?_, ?_, ?_⟩
      · simpa [AnnotatedOccurrence.formula, shape,
          FormulaValidity.semanticOccurrences] using
          List.mem_map.mpr ⟨source, sourceMem, rfl⟩
      · simp [AnnotatedOccurrence.child, FormulaValidity.SemanticOccurrence.prefixPath,
          FormulaValidity.SemanticOccurrence.through, sourcePath, List.append_assoc]
      · simpa [FormulaValidity.SemanticOccurrence.prefixPath,
          FormulaValidity.SemanticOccurrence.through] using sourceLeaf
  | alwaysBeforeEnd selected interval body shape present active beforeEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.canonicalLeavesValid_replace valid present
      intro fresh freshMem leaf leafMem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at freshMem
      rcases freshMem with rfl | rfl
      · exact ⟨leaf, by simpa [AnnotatedOccurrence.relabel,
          AnnotatedOccurrence.formula, shape] using leafMem, by
            simp [AnnotatedOccurrence.relabel], rfl⟩
      · rcases expandedChildSource body node.time 0 leaf leafMem with
          ⟨source, sourceMem, sourcePath, sourceLeaf⟩
        refine ⟨(source.through interval).prefixPath 0, ?_, ?_, ?_⟩
        · simpa [AnnotatedOccurrence.formula, shape,
            FormulaValidity.semanticOccurrences] using
            List.mem_map.mpr ⟨source, sourceMem, rfl⟩
        · simp [AnnotatedOccurrence.child, FormulaValidity.SemanticOccurrence.prefixPath,
            FormulaValidity.SemanticOccurrence.through, sourcePath, List.append_assoc]
        · simpa [FormulaValidity.SemanticOccurrence.prefixPath,
            FormulaValidity.SemanticOccurrence.through] using sourceLeaf
  | alwaysAtEnd selected interval body shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.canonicalLeavesValid_replace valid present
      intro fresh freshMem leaf leafMem
      simp only [List.mem_singleton] at freshMem
      subst fresh
      rcases expandedChildSource body node.time 0 leaf leafMem with
        ⟨source, sourceMem, sourcePath, sourceLeaf⟩
      refine ⟨(source.through interval).prefixPath 0, ?_, ?_, ?_⟩
      · simpa [AnnotatedOccurrence.formula, shape,
          FormulaValidity.semanticOccurrences] using
          List.mem_map.mpr ⟨source, sourceMem, rfl⟩
      · simp [AnnotatedOccurrence.child, FormulaValidity.SemanticOccurrence.prefixPath,
          FormulaValidity.SemanticOccurrence.through, sourcePath, List.append_assoc]
      · simpa [FormulaValidity.SemanticOccurrence.prefixPath,
          FormulaValidity.SemanticOccurrence.through] using sourceLeaf
  | strictUntilBeforeEnd selected interval invariant target shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      have nontrivial : interval.lower < interval.upper := by omega
      rcases childMem with rfl | rfl
      · apply Node.canonicalLeavesValid_replace valid present
        intro fresh freshMem leaf leafMem
        simp only [List.mem_singleton] at freshMem
        subst fresh
        rcases expandedChildSource target node.time 1 leaf leafMem with
          ⟨source, sourceMem, sourcePath, sourceLeaf⟩
        refine ⟨(source.through interval).prefixPath 1, ?_, ?_, ?_⟩
        · simp only [AnnotatedOccurrence.formula, shape,
            FormulaValidity.semanticOccurrences, List.mem_append]
          exact Or.inr (List.mem_map.mpr ⟨source, sourceMem, rfl⟩)
        · simp [AnnotatedOccurrence.child, FormulaValidity.SemanticOccurrence.prefixPath,
            FormulaValidity.SemanticOccurrence.through, sourcePath, List.append_assoc]
        · simpa [FormulaValidity.SemanticOccurrence.prefixPath,
            FormulaValidity.SemanticOccurrence.through] using sourceLeaf
      · apply Node.canonicalLeavesValid_replace valid present
        intro fresh freshMem leaf leafMem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at freshMem
        rcases freshMem with rfl | rfl
        · exact ⟨leaf, by simpa [AnnotatedOccurrence.relabel,
            AnnotatedOccurrence.formula, shape] using leafMem, by
              simp [AnnotatedOccurrence.relabel], rfl⟩
        · rcases expandedChildSource invariant node.time 0 leaf leafMem with
            ⟨source, sourceMem, sourcePath, sourceLeaf⟩
          refine ⟨(source.beforeTarget interval nontrivial).prefixPath 0, ?_, ?_, ?_⟩
          · simp only [AnnotatedOccurrence.formula, shape,
              FormulaValidity.semanticOccurrences, dif_pos nontrivial,
              List.mem_append]
            exact Or.inl (List.mem_map.mpr ⟨source, sourceMem, rfl⟩)
          · simp [AnnotatedOccurrence.child, FormulaValidity.SemanticOccurrence.prefixPath,
              FormulaValidity.SemanticOccurrence.beforeTarget, sourcePath,
              List.append_assoc]
          · simpa [FormulaValidity.SemanticOccurrence.prefixPath,
              FormulaValidity.SemanticOccurrence.beforeTarget] using sourceLeaf
  | strictUntilAtEnd selected interval invariant target shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.canonicalLeavesValid_replace valid present
      intro fresh freshMem leaf leafMem
      simp only [List.mem_singleton] at freshMem
      subst fresh
      rcases expandedChildSource target node.time 1 leaf leafMem with
        ⟨source, sourceMem, sourcePath, sourceLeaf⟩
      refine ⟨(source.through interval).prefixPath 1, ?_, ?_, ?_⟩
      · simp only [AnnotatedOccurrence.formula, shape,
          FormulaValidity.semanticOccurrences, List.mem_append]
        exact Or.inr (List.mem_map.mpr ⟨source, sourceMem, rfl⟩)
      · simp [AnnotatedOccurrence.child, FormulaValidity.SemanticOccurrence.prefixPath,
          FormulaValidity.SemanticOccurrence.through, sourcePath, List.append_assoc]
      · simpa [FormulaValidity.SemanticOccurrence.prefixPath,
          FormulaValidity.SemanticOccurrence.through] using sourceLeaf
  | strictReleaseBeforeEnd selected interval target invariant shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      have nontrivial : interval.lower < interval.upper := by omega
      rcases childMem with rfl | rfl
      · apply Node.canonicalLeavesValid_replace valid present
        intro fresh freshMem leaf leafMem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at freshMem
        rcases freshMem with rfl | rfl
        · rcases expandedChildSource target node.time 0 leaf leafMem with
            ⟨source, sourceMem, sourcePath, sourceLeaf⟩
          refine ⟨(source.beforeTarget interval nontrivial).prefixPath 0, ?_, ?_, ?_⟩
          · simp only [AnnotatedOccurrence.formula, shape,
              FormulaValidity.semanticOccurrences, dif_pos nontrivial,
              List.mem_append]
            exact Or.inl (List.mem_map.mpr ⟨source, sourceMem, rfl⟩)
          · simp [AnnotatedOccurrence.child, FormulaValidity.SemanticOccurrence.prefixPath,
              FormulaValidity.SemanticOccurrence.beforeTarget, sourcePath,
              List.append_assoc]
          · simpa [FormulaValidity.SemanticOccurrence.prefixPath,
              FormulaValidity.SemanticOccurrence.beforeTarget] using sourceLeaf
        · rcases expandedChildSource invariant node.time 1 leaf leafMem with
            ⟨source, sourceMem, sourcePath, sourceLeaf⟩
          refine ⟨(source.through interval).prefixPath 1, ?_, ?_, ?_⟩
          · simp only [AnnotatedOccurrence.formula, shape,
              FormulaValidity.semanticOccurrences, List.mem_append]
            exact Or.inr (List.mem_map.mpr ⟨source, sourceMem, rfl⟩)
          · simp [AnnotatedOccurrence.child, FormulaValidity.SemanticOccurrence.prefixPath,
              FormulaValidity.SemanticOccurrence.through, sourcePath, List.append_assoc]
          · simpa [FormulaValidity.SemanticOccurrence.prefixPath,
              FormulaValidity.SemanticOccurrence.through] using sourceLeaf
      · apply Node.canonicalLeavesValid_replace valid present
        intro fresh freshMem leaf leafMem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at freshMem
        rcases freshMem with rfl | rfl
        · exact ⟨leaf, by simpa [AnnotatedOccurrence.relabel,
            AnnotatedOccurrence.formula, shape] using leafMem, by
              simp [AnnotatedOccurrence.relabel], rfl⟩
        · rcases expandedChildSource invariant node.time 1 leaf leafMem with
            ⟨source, sourceMem, sourcePath, sourceLeaf⟩
          refine ⟨(source.through interval).prefixPath 1, ?_, ?_, ?_⟩
          · simp only [AnnotatedOccurrence.formula, shape,
              FormulaValidity.semanticOccurrences, List.mem_append]
            exact Or.inr (List.mem_map.mpr ⟨source, sourceMem, rfl⟩)
          · simp [AnnotatedOccurrence.child, FormulaValidity.SemanticOccurrence.prefixPath,
              FormulaValidity.SemanticOccurrence.through, sourcePath, List.append_assoc]
          · simpa [FormulaValidity.SemanticOccurrence.prefixPath,
              FormulaValidity.SemanticOccurrence.through] using sourceLeaf
  | strictReleaseAtEnd selected interval target invariant shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.canonicalLeavesValid_replace valid present
      intro fresh freshMem leaf leafMem
      simp only [List.mem_singleton] at freshMem
      subst fresh
      rcases expandedChildSource invariant node.time 1 leaf leafMem with
        ⟨source, sourceMem, sourcePath, sourceLeaf⟩
      refine ⟨(source.through interval).prefixPath 1, ?_, ?_, ?_⟩
      · simp only [AnnotatedOccurrence.formula, shape,
          FormulaValidity.semanticOccurrences, List.mem_append]
        exact Or.inr (List.mem_map.mpr ⟨source, sourceMem, rfl⟩)
      · simp [AnnotatedOccurrence.child, FormulaValidity.SemanticOccurrence.prefixPath,
          FormulaValidity.SemanticOccurrence.through, sourcePath, List.append_assoc]
      · simpa [FormulaValidity.SemanticOccurrence.prefixPath,
          FormulaValidity.SemanticOccurrence.through] using sourceLeaf

end Expansion

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

private theorem step_origin (node : Node Atom) (child : AnnotatedOccurrence Atom)
    (childMem : child ∈ node.stepLabel) :
    ∃ source ∈ node.label, source.id = child.id ∧ source.formula = child.formula := by
  rcases Finset.mem_union.mp childMem with unchanged | continued
  · rcases Finset.mem_filter.mp unchanged with ⟨sourceMem, _⟩
    exact ⟨child, sourceMem, rfl, rfl⟩
  · rcases Finset.mem_image.mp continued with ⟨source, sourceFiltered, equal⟩
    rcases Finset.mem_filter.mp sourceFiltered with ⟨sourceMem, _⟩
    refine ⟨source, sourceMem, ?_, ?_⟩
    · rw [← equal]
      exact AnnotatedOccurrence.unmark_id source |>.symm
    · rw [← equal]
      exact AnnotatedOccurrence.unmark_formula source |>.symm

theorem step_canonicalLeavesValid {node : Node Atom}
    (valid : node.CanonicalLeavesValid) : node.step.CanonicalLeavesValid := by
  intro first firstMem second secondMem firstLeaf firstLeafMem secondLeaf secondLeafMem ids
  change first ∈ node.stepLabel at firstMem
  change second ∈ node.stepLabel at secondMem
  rcases step_origin node first firstMem with ⟨firstSource, firstSourceMem, firstId, firstFormula⟩
  rcases step_origin node second secondMem with
    ⟨secondSource, secondSourceMem, secondId, secondFormula⟩
  apply valid firstSource firstSourceMem secondSource secondSourceMem firstLeaf
    (by simpa [firstFormula] using firstLeafMem) secondLeaf
    (by simpa [secondFormula] using secondLeafMem)
  simpa [firstId, secondId] using ids

private theorem jump_origin (node : Node Atom) (size : Nat)
    (child : AnnotatedOccurrence Atom) (childMem : child ∈ node.jumpLabel size) :
    ∃ source ∈ node.label, source.id = child.id ∧ source.formula = child.formula := by
  rcases Finset.mem_image.mp childMem with ⟨source, sourceFiltered, equal⟩
  rcases Finset.mem_filter.mp sourceFiltered with ⟨sourceMem, _⟩
  refine ⟨source, sourceMem, ?_, ?_⟩
  · rw [← equal]
    exact AnnotatedOccurrence.unmark_id source |>.symm
  · rw [← equal]
    exact AnnotatedOccurrence.unmark_formula source |>.symm

theorem jump_canonicalLeavesValid {node : Node Atom} (size : Nat)
    (valid : node.CanonicalLeavesValid) : (node.jump size).CanonicalLeavesValid := by
  intro first firstMem second secondMem firstLeaf firstLeafMem secondLeaf secondLeafMem ids
  change first ∈ node.jumpLabel size at firstMem
  change second ∈ node.jumpLabel size at secondMem
  rcases jump_origin node size first firstMem with
    ⟨firstSource, firstSourceMem, firstId, firstFormula⟩
  rcases jump_origin node size second secondMem with
    ⟨secondSource, secondSourceMem, secondId, secondFormula⟩
  apply valid firstSource firstSourceMem secondSource secondSourceMem firstLeaf
    (by simpa [firstFormula] using firstLeafMem) secondLeaf
    (by simpa [secondFormula] using secondLeafMem)
  simpa [firstId, secondId] using ids

/-- All reachability information used by the local JUMP soundness proof. -/
def FullDerivationValid (node : Node Atom) : Prop :=
  node.SoundnessDerivationValid ∧ node.CanonicalLeavesValid

theorem initial_fullDerivationValid (formula : Stlsat.Formula Atom) :
    (Node.initial formula).FullDerivationValid :=
  ⟨Node.initial_soundnessDerivationValid formula,
    Node.initial_canonicalLeavesValid formula⟩

end Node

namespace Rule

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom}

theorem child_canonicalLeavesValid {node child : Node Atom}
    {children : List (Node Atom)} (rule : Rule semantics node children)
    (valid : node.CanonicalLeavesValid) (childMem : child ∈ children) :
    child.CanonicalLeavesValid := by
  cases rule with
  | expand notRejected expansion => exact expansion.child_canonicalLeavesValid valid childMem
  | step notRejected poised hasTemporal jumpDisabled =>
      simp only [List.mem_singleton] at childMem
      subst child
      exact Node.step_canonicalLeavesValid valid
  | jump notRejected poised hasTemporal sound complete size computed =>
      simp only [List.mem_singleton] at childMem
      subst child
      exact Node.jump_canonicalLeavesValid size valid

theorem child_fullDerivationValid {node child : Node Atom}
    {children : List (Node Atom)} (rule : Rule semantics node children)
    (valid : node.FullDerivationValid) (childMem : child ∈ children) :
    child.FullDerivationValid :=
  ⟨rule.child_soundnessDerivationValid valid.1 childMem,
    rule.child_canonicalLeavesValid valid.2 childMem⟩

end Rule

end Stlsat.Jump
