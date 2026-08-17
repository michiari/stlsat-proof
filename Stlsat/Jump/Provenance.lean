/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.LocalSoundness

/-!
# Provenance of validity windows

Parent references created by temporal expansion carry enough information to
relate every live descendant validity window to the temporal formula which
created it.  This file records that fact as a node invariant and proves that
all tableau rules preserve it.
-/

namespace Stlsat.Jump
universe u

namespace AnnotatedOccurrence

variable {Atom : Type u}

/-- Every stored parent link points to a temporal formula, and every validity
window of the child is contained in a validity window of that parent with the
same canonical leaf identifier. -/
def ParentLinkValid (time : Nat) (child : AnnotatedOccurrence Atom) : Prop :=
  match child.parent with
  | none => True
  | some (.mk parentId parentFormula _) =>
      parentFormula.isTemporal = true ∧
        ∀ childValidity ∈ FormulaValidity.validityFrom time child.formula,
          ∃ parentValidity ∈ FormulaValidity.validityOccurrences parentFormula,
            parentId ++ parentValidity.path = child.id ++ childValidity.path ∧
              parentValidity.window.lower ≤ childValidity.window.lower ∧
              childValidity.window.upper ≤ parentValidity.window.upper

@[simp]
theorem parentLinkValid_parentless (time : Nat) (id : OccurrenceId)
    (payload : Stlsat.Occurrence Atom) :
    ParentLinkValid time { id := id, payload := payload, parent := none } := by
  simp [ParentLinkValid]

@[simp]
theorem formula_isTemporal (child : AnnotatedOccurrence Atom) :
    child.formula.isTemporal = child.isTemporal := by
  cases child with
  | mk id payload parent => cases payload <;> rfl

@[simp]
theorem unmark_formula (child : AnnotatedOccurrence Atom) :
    child.unmark.formula = child.formula := by
  cases child with
  | mk id payload parent => cases payload <;>
      rfl

@[simp]
theorem unmark_isTemporal (child : AnnotatedOccurrence Atom) :
    child.unmark.isTemporal = child.isTemporal := by
  rw [← formula_isTemporal child.unmark, unmark_formula, formula_isTemporal]

@[simp]
theorem unmark_parent (child : AnnotatedOccurrence Atom) :
    child.unmark.parent = child.parent := by
  cases child
  rfl

@[simp]
theorem unmark_id (child : AnnotatedOccurrence Atom) :
    child.unmark.id = child.id := by
  cases child
  rfl

theorem ParentLinkValid.at_time_of_temporal {child : AnnotatedOccurrence Atom}
    {oldTime : Nat} (valid : child.ParentLinkValid oldTime)
    (temporal : child.isTemporal = true) (newTime : Nat) :
    child.ParentLinkValid newTime := by
  have formulaTemporal : child.formula.isTemporal = true :=
    (formula_isTemporal child).trans temporal
  cases child with
  | mk id payload parent =>
      cases parent with
      | none => trivial
      | some parentRef =>
          cases parentRef with
          | mk parentId parentFormula parentParent =>
              rcases valid with ⟨parentTemporal, covered⟩
              refine ⟨parentTemporal, ?_⟩
              intro childValidity childValidityMem
              apply covered childValidity
              rw [FormulaValidity.validityFrom_temporal newTime _ formulaTemporal]
                at childValidityMem
              rw [FormulaValidity.validityFrom_temporal oldTime _ formulaTemporal]
              exact childValidityMem

theorem ParentLinkValid.unmark {child : AnnotatedOccurrence Atom} {time : Nat}
    (valid : child.ParentLinkValid time) : child.unmark.ParentLinkValid time := by
  cases child with
  | mk id payload parent =>
      cases parent with
      | none => simp [ParentLinkValid]
      | some parentRef =>
          simpa only [ParentLinkValid, unmark_parent, unmark_formula,
            unmark_id] using valid

theorem ParentLinkValid.child_parentless (selected : AnnotatedOccurrence Atom)
    (edge time : Nat) (payload : Stlsat.Occurrence Atom) :
    (selected.child edge payload none).ParentLinkValid time := by
  cases selected
  simp [ParentLinkValid, child]

end AnnotatedOccurrence

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

/-- The provenance invariant is local to each occurrence; no deleted ancestor
needs to remain in the label because its complete reference is stored. -/
def ProvenanceValid (node : Node Atom) : Prop :=
  ∀ occurrence ∈ node.label, occurrence.ParentLinkValid node.time

omit [DecidableEq Atom] in
theorem initial_provenanceValid (formula : Stlsat.Formula Atom) :
    (Node.initial formula).ProvenanceValid := by
  intro occurrence present
  simp only [Node.initial, Finset.mem_singleton] at present
  subst occurrence
  exact AnnotatedOccurrence.parentLinkValid_parentless 0 [] (.unmarked formula)

theorem provenanceValid_replace {node : Node Atom}
    {selected : AnnotatedOccurrence Atom}
    {replacement : List (AnnotatedOccurrence Atom)}
    (valid : node.ProvenanceValid)
    (replacementValid : ∀ occurrence ∈ replacement,
      occurrence.ParentLinkValid node.time) :
    (node.replace selected replacement).ProvenanceValid := by
  intro occurrence present
  change occurrence ∈ node.label.erase selected ∪ replacement.toFinset at present
  rcases Finset.mem_union.mp present with old | fresh
  · exact valid occurrence (Finset.mem_of_mem_erase old)
  · exact replacementValid occurrence (by simpa using fresh)

omit [DecidableEq Atom] in
private theorem inheritedChildValid {time edge : Nat}
    {selected : AnnotatedOccurrence Atom} {childFormula : Stlsat.Formula Atom}
    (selectedValid : selected.ParentLinkValid time)
    (embed : ∀ childValidity ∈ FormulaValidity.validityFrom time childFormula,
      ∃ selectedValidity ∈ FormulaValidity.validityFrom time selected.formula,
        selectedValidity.path = edge :: childValidity.path ∧
          selectedValidity.window = childValidity.window) :
    (selected.child edge (.unmarked childFormula) selected.parent).ParentLinkValid time := by
  cases selected with
  | mk id payload parent =>
      cases parent with
      | none => simp [AnnotatedOccurrence.ParentLinkValid,
          AnnotatedOccurrence.child]
      | some parentRef =>
          cases parentRef with
          | mk parentId parentFormula parentParent =>
              rcases selectedValid with ⟨parentTemporal, covered⟩
              refine ⟨parentTemporal, ?_⟩
              intro childValidity childValidityMem
              rcases embed childValidity childValidityMem with
                ⟨selectedValidity, selectedValidityMem, selectedPath, selectedWindow⟩
              rcases covered selectedValidity selectedValidityMem with
                ⟨parentValidity, parentValidityMem, parentIdEq, lower, upper⟩
              refine ⟨parentValidity, parentValidityMem, ?_, ?_, ?_⟩
              · simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.formula,
                  selectedPath, List.append_assoc] using parentIdEq
              · simpa [selectedWindow] using lower
              · simpa [selectedWindow] using upper

omit [DecidableEq Atom] in
private theorem directAlwaysChildValid (selected : AnnotatedOccurrence Atom)
    (interval : Stlsat.Interval) (body : Stlsat.Formula Atom) (time : Nat)
    (shape : selected.payload = .unmarked (.always interval body))
    (active : interval.lower ≤ time) (notAfter : time ≤ interval.upper) :
    (selected.child 0 (.unmarked (body.temporalExpansion time))
      (some selected.reference)).ParentLinkValid time := by
  cases selected with
  | mk id payload parent =>
      change payload = .unmarked (.always interval body) at shape
      subst payload
      refine ⟨by simp [AnnotatedOccurrence.formula,
        Stlsat.Formula.isTemporal], ?_⟩
      intro childValidity childValidityMem
      change childValidity ∈
        FormulaValidity.validityFrom time (body.temporalExpansion time) at childValidityMem
      change ∃ parentValidity ∈
          FormulaValidity.validityOccurrences (.always interval body),
        id ++ parentValidity.path = (id ++ [0]) ++ childValidity.path ∧
          parentValidity.window.lower ≤ childValidity.window.lower ∧
          childValidity.window.upper ≤ parentValidity.window.upper
      rw [FormulaValidity.validityFrom_temporalExpansion] at childValidityMem
      rcases List.mem_map.mp childValidityMem with ⟨validity, validityMem, rfl⟩
      let parentValidity := ValidityOccurrence.prefixPath 0 (validity.through interval)
      refine ⟨parentValidity, ?_, ?_, ?_, ?_⟩
      · exact List.mem_map.mpr ⟨validity, validityMem, rfl⟩
      · simp [parentValidity, ValidityOccurrence.prefixPath, ValidityOccurrence.through,
          ValidityOccurrence.shift, List.append_assoc]
      · simp [parentValidity, ValidityOccurrence.prefixPath,
          ValidityOccurrence.through, ValidityOccurrence.shift,
          Stlsat.Interval.shift]
        omega
      · simp [parentValidity, ValidityOccurrence.prefixPath,
          ValidityOccurrence.through, ValidityOccurrence.shift,
          Stlsat.Interval.shift]
        omega

omit [DecidableEq Atom] in
private theorem directUntilChildValid (selected : AnnotatedOccurrence Atom)
    (interval : Stlsat.Interval) (invariant target : Stlsat.Formula Atom) (time : Nat)
    (shape : selected.payload = .unmarked (.strictUntil interval invariant target))
    (active : interval.lower ≤ time) (beforeEnd : time < interval.upper) :
    (selected.child 0 (.unmarked (invariant.temporalExpansion time))
      (some selected.reference)).ParentLinkValid time := by
  cases selected with
  | mk id payload parent =>
      change payload = .unmarked (.strictUntil interval invariant target) at shape
      subst payload
      refine ⟨by simp [AnnotatedOccurrence.formula,
        Stlsat.Formula.isTemporal], ?_⟩
      intro childValidity childValidityMem
      change childValidity ∈ FormulaValidity.validityFrom time
        (invariant.temporalExpansion time) at childValidityMem
      change ∃ parentValidity ∈ FormulaValidity.validityOccurrences
          (.strictUntil interval invariant target),
        id ++ parentValidity.path = (id ++ [0]) ++ childValidity.path ∧
          parentValidity.window.lower ≤ childValidity.window.lower ∧
          childValidity.window.upper ≤ parentValidity.window.upper
      rw [FormulaValidity.validityFrom_temporalExpansion] at childValidityMem
      rcases List.mem_map.mp childValidityMem with ⟨validity, validityMem, rfl⟩
      have nontrivial : interval.lower < interval.upper := by omega
      let parentValidity :=
        ValidityOccurrence.prefixPath 0 (validity.beforeTarget interval nontrivial)
      refine ⟨parentValidity, ?_, ?_, ?_, ?_⟩
      · simp only [parentValidity, FormulaValidity.validityOccurrences,
          dif_pos nontrivial, List.mem_append]
        exact Or.inl (List.mem_map.mpr ⟨validity, validityMem, rfl⟩)
      · simp [parentValidity, ValidityOccurrence.prefixPath,
          ValidityOccurrence.beforeTarget,
          ValidityOccurrence.shift, List.append_assoc]
      · simp [parentValidity, ValidityOccurrence.prefixPath,
          ValidityOccurrence.beforeTarget, ValidityOccurrence.shift,
          Stlsat.Interval.shift]
        omega
      · simp [parentValidity, ValidityOccurrence.prefixPath,
          ValidityOccurrence.beforeTarget, ValidityOccurrence.shift,
          Stlsat.Interval.shift]
        omega

omit [DecidableEq Atom] in
private theorem directReleaseChildValid (selected : AnnotatedOccurrence Atom)
    (interval : Stlsat.Interval) (target invariant : Stlsat.Formula Atom) (time : Nat)
    (shape : selected.payload = .unmarked (.strictRelease interval target invariant))
    (active : interval.lower ≤ time) (notAfter : time ≤ interval.upper) :
    (selected.child 1 (.unmarked (invariant.temporalExpansion time))
      (some selected.reference)).ParentLinkValid time := by
  cases selected with
  | mk id payload parent =>
      change payload = .unmarked (.strictRelease interval target invariant) at shape
      subst payload
      refine ⟨by simp [AnnotatedOccurrence.formula,
        Stlsat.Formula.isTemporal], ?_⟩
      intro childValidity childValidityMem
      change childValidity ∈ FormulaValidity.validityFrom time
        (invariant.temporalExpansion time) at childValidityMem
      change ∃ parentValidity ∈ FormulaValidity.validityOccurrences
          (.strictRelease interval target invariant),
        id ++ parentValidity.path = (id ++ [1]) ++ childValidity.path ∧
          parentValidity.window.lower ≤ childValidity.window.lower ∧
          childValidity.window.upper ≤ parentValidity.window.upper
      rw [FormulaValidity.validityFrom_temporalExpansion] at childValidityMem
      rcases List.mem_map.mp childValidityMem with ⟨validity, validityMem, rfl⟩
      let parentValidity := ValidityOccurrence.prefixPath 1 (validity.through interval)
      refine ⟨parentValidity, ?_, ?_, ?_, ?_⟩
      · simp only [parentValidity, FormulaValidity.validityOccurrences, List.mem_append]
        exact Or.inr (List.mem_map.mpr ⟨validity, validityMem, rfl⟩)
      · simp [parentValidity, ValidityOccurrence.prefixPath, ValidityOccurrence.through,
          ValidityOccurrence.shift, List.append_assoc]
      · simp [parentValidity, ValidityOccurrence.prefixPath,
          ValidityOccurrence.through, ValidityOccurrence.shift,
          Stlsat.Interval.shift]
        omega
      · simp [parentValidity, ValidityOccurrence.prefixPath,
          ValidityOccurrence.through, ValidityOccurrence.shift,
          Stlsat.Interval.shift]
        omega

end Node

namespace Expansion

variable {Atom : Type u} [DecidableEq Atom]

/-- Formula expansion preserves the validity-window provenance carried by
parent references. -/
theorem child_provenanceValid {node child : Node Atom} {children : List (Node Atom)}
    (expansion : Expansion node children) (valid : node.ProvenanceValid)
    (childMem : child ∈ children) : child.ProvenanceValid := by
  cases expansion with
  | disjunction selected left right shape present =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      rcases childMem with rfl | rfl
      · apply Node.provenanceValid_replace valid
        intro occurrence occurrenceMem
        simp only [List.mem_singleton] at occurrenceMem
        subst occurrence
        apply Node.inheritedChildValid (valid selected present)
        intro childValidity childValidityMem
        refine ⟨childValidity.prefixPath 0, ?_, rfl, rfl⟩
        have selectedFormula : selected.formula = .or left right := by
          cases selected with
          | mk id payload parent =>
              change payload = .unmarked (.or left right) at shape
              subst payload
              rfl
        rw [selectedFormula]
        change childValidity.prefixPath 0 ∈
          (FormulaValidity.validityFrom node.time left).map
              (ValidityOccurrence.prefixPath 0) ++
            (FormulaValidity.validityFrom node.time right).map
              (ValidityOccurrence.prefixPath 1)
        exact List.mem_append.mpr (Or.inl
          (List.mem_map.mpr ⟨childValidity, childValidityMem, rfl⟩))
      · apply Node.provenanceValid_replace valid
        intro occurrence occurrenceMem
        simp only [List.mem_singleton] at occurrenceMem
        subst occurrence
        apply Node.inheritedChildValid (valid selected present)
        intro childValidity childValidityMem
        refine ⟨childValidity.prefixPath 1, ?_, rfl, rfl⟩
        have selectedFormula : selected.formula = .or left right := by
          cases selected with
          | mk id payload parent =>
              change payload = .unmarked (.or left right) at shape
              subst payload
              rfl
        rw [selectedFormula]
        change childValidity.prefixPath 1 ∈
          (FormulaValidity.validityFrom node.time left).map
              (ValidityOccurrence.prefixPath 0) ++
            (FormulaValidity.validityFrom node.time right).map
              (ValidityOccurrence.prefixPath 1)
        exact List.mem_append.mpr (Or.inr
          (List.mem_map.mpr ⟨childValidity, childValidityMem, rfl⟩))
  | conjunction selected left right shape present =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.provenanceValid_replace valid
      intro occurrence occurrenceMem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMem
      rcases occurrenceMem with rfl | rfl
      · apply Node.inheritedChildValid (valid selected present)
        intro childValidity childValidityMem
        refine ⟨childValidity.prefixPath 0, ?_, rfl, rfl⟩
        have selectedFormula : selected.formula = .and left right := by
          cases selected with
          | mk id payload parent =>
              change payload = .unmarked (.and left right) at shape
              subst payload
              rfl
        rw [selectedFormula]
        change childValidity.prefixPath 0 ∈
          (FormulaValidity.validityFrom node.time left).map
              (ValidityOccurrence.prefixPath 0) ++
            (FormulaValidity.validityFrom node.time right).map
              (ValidityOccurrence.prefixPath 1)
        exact List.mem_append.mpr (Or.inl
          (List.mem_map.mpr ⟨childValidity, childValidityMem, rfl⟩))
      · apply Node.inheritedChildValid (valid selected present)
        intro childValidity childValidityMem
        refine ⟨childValidity.prefixPath 1, ?_, rfl, rfl⟩
        have selectedFormula : selected.formula = .and left right := by
          cases selected with
          | mk id payload parent =>
              change payload = .unmarked (.and left right) at shape
              subst payload
              rfl
        rw [selectedFormula]
        change childValidity.prefixPath 1 ∈
          (FormulaValidity.validityFrom node.time left).map
              (ValidityOccurrence.prefixPath 0) ++
            (FormulaValidity.validityFrom node.time right).map
              (ValidityOccurrence.prefixPath 1)
        exact List.mem_append.mpr (Or.inr
          (List.mem_map.mpr ⟨childValidity, childValidityMem, rfl⟩))
  | eventuallyBeforeEnd selected interval body shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      rcases childMem with rfl | rfl
      · apply Node.provenanceValid_replace valid
        intro occurrence occurrenceMem
        simp only [List.mem_singleton] at occurrenceMem
        subst occurrence
        exact AnnotatedOccurrence.ParentLinkValid.child_parentless selected 0 node.time
          (.unmarked (body.temporalExpansion node.time))
      · apply Node.provenanceValid_replace valid
        intro occurrence occurrenceMem
        simp only [List.mem_singleton] at occurrenceMem
        subst occurrence
        simpa [AnnotatedOccurrence.ParentLinkValid, AnnotatedOccurrence.relabel,
          AnnotatedOccurrence.formula, shape] using valid selected present
  | eventuallyAtEnd selected interval body shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.provenanceValid_replace valid
      intro occurrence occurrenceMem
      simp only [List.mem_singleton] at occurrenceMem
      subst occurrence
      exact AnnotatedOccurrence.ParentLinkValid.child_parentless selected 0 node.time
        (.unmarked (body.temporalExpansion node.time))
  | alwaysBeforeEnd selected interval body shape present active beforeEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.provenanceValid_replace valid
      intro occurrence occurrenceMem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMem
      rcases occurrenceMem with rfl | rfl
      · simpa [AnnotatedOccurrence.ParentLinkValid, AnnotatedOccurrence.relabel,
          AnnotatedOccurrence.formula, shape] using valid selected present
      · exact Node.directAlwaysChildValid selected interval body node.time shape active
          (Nat.le_of_lt beforeEnd)
  | alwaysAtEnd selected interval body shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.provenanceValid_replace valid
      intro occurrence occurrenceMem
      simp only [List.mem_singleton] at occurrenceMem
      subst occurrence
      exact Node.directAlwaysChildValid selected interval body node.time shape
        (by simpa [atEnd] using interval.lower_le_upper) (by omega)
  | strictUntilBeforeEnd selected interval invariant target shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      rcases childMem with rfl | rfl
      · apply Node.provenanceValid_replace valid
        intro occurrence occurrenceMem
        simp only [List.mem_singleton] at occurrenceMem
        subst occurrence
        exact AnnotatedOccurrence.ParentLinkValid.child_parentless selected 1 node.time
          (.unmarked (target.temporalExpansion node.time))
      · apply Node.provenanceValid_replace valid
        intro occurrence occurrenceMem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMem
        rcases occurrenceMem with rfl | rfl
        · simpa [AnnotatedOccurrence.ParentLinkValid, AnnotatedOccurrence.relabel,
            AnnotatedOccurrence.formula, shape] using valid selected present
        · exact Node.directUntilChildValid selected interval invariant target node.time shape
            active beforeEnd
  | strictUntilAtEnd selected interval invariant target shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.provenanceValid_replace valid
      intro occurrence occurrenceMem
      simp only [List.mem_singleton] at occurrenceMem
      subst occurrence
      exact AnnotatedOccurrence.ParentLinkValid.child_parentless selected 1 node.time
        (.unmarked (target.temporalExpansion node.time))
  | strictReleaseBeforeEnd selected interval target invariant shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      rcases childMem with rfl | rfl
      · apply Node.provenanceValid_replace valid
        intro occurrence occurrenceMem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMem
        rcases occurrenceMem with rfl | rfl
        · exact AnnotatedOccurrence.ParentLinkValid.child_parentless selected 0 node.time
            (.unmarked (target.temporalExpansion node.time))
        · exact AnnotatedOccurrence.ParentLinkValid.child_parentless selected 1 node.time
            (.unmarked (invariant.temporalExpansion node.time))
      · apply Node.provenanceValid_replace valid
        intro occurrence occurrenceMem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMem
        rcases occurrenceMem with rfl | rfl
        · simpa [AnnotatedOccurrence.ParentLinkValid, AnnotatedOccurrence.relabel,
            AnnotatedOccurrence.formula, shape] using valid selected present
        · exact Node.directReleaseChildValid selected interval target invariant node.time shape
            active (Nat.le_of_lt beforeEnd)
  | strictReleaseAtEnd selected interval target invariant shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Node.provenanceValid_replace valid
      intro occurrence occurrenceMem
      simp only [List.mem_singleton] at occurrenceMem
      subst occurrence
      exact Node.directReleaseChildValid selected interval target invariant node.time shape
        (by simpa [atEnd] using interval.lower_le_upper) (by omega)

end Expansion

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

theorem step_provenanceValid {node : Node Atom} (valid : node.ProvenanceValid) :
    node.step.ProvenanceValid := by
  intro occurrence present
  change occurrence ∈ node.stepLabel at present
  rcases Finset.mem_union.mp present with unchanged | continued
  · rcases Finset.mem_filter.mp unchanged with ⟨sourceMem, temporal⟩
    apply (valid occurrence sourceMem).at_time_of_temporal
      (newTime := node.time + 1)
    cases occurrence with
    | mk id payload parent =>
        cases payload <;>
          simp_all [AnnotatedOccurrence.isUnmarkedTemporal,
            Stlsat.Occurrence.isUnmarkedTemporal, AnnotatedOccurrence.isTemporal,
            Stlsat.Occurrence.isTemporal]
  · rcases Finset.mem_image.mp continued with ⟨source, sourceFiltered, rfl⟩
    rcases Finset.mem_filter.mp sourceFiltered with ⟨sourceMem, continues⟩
    have sourceTemporal : source.isTemporal = true := by
      cases source with
      | mk id payload parent =>
          cases payload <;>
            simp_all [AnnotatedOccurrence.markedContinuesAt,
              Stlsat.Occurrence.markedContinuesAt, AnnotatedOccurrence.isTemporal,
              Stlsat.Occurrence.isTemporal]
    apply (valid source sourceMem).unmark.at_time_of_temporal
      (newTime := node.time + 1)
    simpa only [AnnotatedOccurrence.unmark_isTemporal] using sourceTemporal

theorem jump_provenanceValid {node : Node Atom} (size : Nat)
    (valid : node.ProvenanceValid) : node.jump size |>.ProvenanceValid := by
  intro occurrence present
  change occurrence ∈ node.jumpLabel size at present
  rcases Finset.mem_image.mp present with ⟨source, sourceFiltered, rfl⟩
  rcases Finset.mem_filter.mp sourceFiltered with ⟨sourceMem, survives⟩
  have sourceTemporal : source.isTemporal = true := by
    cases source with
    | mk id payload parent =>
        cases payload with
        | unmarked formula =>
            cases formula <;>
              simp_all [Node.survivesJump, AnnotatedOccurrence.interval?,
                AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal,
                Stlsat.Formula.isTemporal]
        | markedEventually interval body => simp [AnnotatedOccurrence.isTemporal,
            Stlsat.Occurrence.isTemporal]
        | markedAlways interval body => simp [AnnotatedOccurrence.isTemporal,
            Stlsat.Occurrence.isTemporal]
        | markedStrictUntil interval invariant target => simp [AnnotatedOccurrence.isTemporal,
            Stlsat.Occurrence.isTemporal]
        | markedStrictRelease interval target invariant => simp [AnnotatedOccurrence.isTemporal,
            Stlsat.Occurrence.isTemporal]
  apply (valid source sourceMem).unmark.at_time_of_temporal
    (newTime := node.time + size)
  simpa only [AnnotatedOccurrence.unmark_isTemporal] using sourceTemporal

/-- Every marked occurrence in a reachable node has already reached the lower
endpoint of its absolute interval. -/
def MarkedActive (node : Node Atom) : Prop :=
  ∀ occurrence ∈ node.label,
    match occurrence.payload with
    | .markedEventually interval _
    | .markedAlways interval _
    | .markedStrictUntil interval _ _
    | .markedStrictRelease interval _ _ => interval.lower ≤ node.time
    | .unmarked _ => True

omit [DecidableEq Atom] in
theorem initial_markedActive (formula : Stlsat.Formula Atom) :
    (Node.initial formula).MarkedActive := by
  intro occurrence present
  simp only [Node.initial, Finset.mem_singleton] at present
  subst occurrence
  trivial

theorem markedActive_replace {node : Node Atom}
    {selected : AnnotatedOccurrence Atom}
    {replacement : List (AnnotatedOccurrence Atom)}
    (active : node.MarkedActive)
    (replacementActive : ∀ occurrence ∈ replacement,
      match occurrence.payload with
      | .markedEventually interval _
      | .markedAlways interval _
      | .markedStrictUntil interval _ _
      | .markedStrictRelease interval _ _ => interval.lower ≤ node.time
      | .unmarked _ => True) :
    (node.replace selected replacement).MarkedActive := by
  intro occurrence present
  change occurrence ∈ node.label.erase selected ∪ replacement.toFinset at present
  rcases Finset.mem_union.mp present with old | fresh
  · exact active occurrence (Finset.mem_of_mem_erase old)
  · exact replacementActive occurrence (by simpa using fresh)

theorem step_markedActive {node : Node Atom} : node.step.MarkedActive := by
  intro occurrence present
  change occurrence ∈ node.stepLabel at present
  rcases Finset.mem_union.mp present with unchanged | continued
  · rcases Finset.mem_filter.mp unchanged with ⟨_, unmarked⟩
    cases occurrence with
    | mk id payload parent =>
        cases payload <;>
          simp_all [AnnotatedOccurrence.isUnmarkedTemporal,
            Stlsat.Occurrence.isUnmarkedTemporal]
  · rcases Finset.mem_image.mp continued with ⟨source, _, rfl⟩
    cases source with
    | mk id payload parent => cases payload <;> trivial

theorem jump_markedActive {node : Node Atom} (size : Nat) :
    (node.jump size).MarkedActive := by
  intro occurrence present
  change occurrence ∈ node.jumpLabel size at present
  rcases Finset.mem_image.mp present with ⟨source, _, rfl⟩
  cases source with
  | mk id payload parent => cases payload <;> trivial

/-- The two provenance facts needed at a derived JUMP node. -/
def DerivationValid (node : Node Atom) : Prop :=
  node.ProvenanceValid ∧ node.MarkedActive

omit [DecidableEq Atom] in
theorem initial_derivationValid (formula : Stlsat.Formula Atom) :
    (Node.initial formula).DerivationValid :=
  ⟨Node.initial_provenanceValid formula, Node.initial_markedActive formula⟩

end Node

namespace Rule

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom}

theorem child_provenanceValid {node child : Node Atom} {children : List (Node Atom)}
    (rule : Rule semantics node children) (valid : node.ProvenanceValid)
    (childMem : child ∈ children) : child.ProvenanceValid := by
  cases rule with
  | expand notRejected expansion => exact expansion.child_provenanceValid valid childMem
  | step notRejected poised hasTemporal jumpDisabled =>
      simp only [List.mem_singleton] at childMem
      subst child
      exact Node.step_provenanceValid valid
  | jump notRejected poised hasTemporal sound complete size computed =>
      simp only [List.mem_singleton] at childMem
      subst child
      exact Node.jump_provenanceValid size valid

/-- Every tableau rule preserves validity provenance and marked activity. -/
theorem child_derivationValid {node child : Node Atom} {children : List (Node Atom)}
    (rule : Rule semantics node children) (valid : node.DerivationValid)
    (childMem : child ∈ children) : child.DerivationValid := by
  refine ⟨rule.child_provenanceValid valid.1 childMem, ?_⟩
  cases rule with
  | expand notRejected expansion =>
      cases expansion with
      | disjunction selected left right shape present =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
          rcases childMem with rfl | rfl <;>
            apply Node.markedActive_replace valid.2 <;>
            intro occurrence occurrenceMem <;>
            simp_all [AnnotatedOccurrence.child]
      | conjunction selected left right shape present =>
          simp only [List.mem_singleton] at childMem
          subst child
          apply Node.markedActive_replace valid.2
          intro occurrence occurrenceMem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMem
          rcases occurrenceMem with rfl | rfl <;> trivial
      | eventuallyBeforeEnd selected interval body shape present active beforeEnd =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
          rcases childMem with rfl | rfl
          · apply Node.markedActive_replace valid.2
            intro occurrence occurrenceMem
            simp only [List.mem_singleton] at occurrenceMem
            subst occurrence
            trivial
          · apply Node.markedActive_replace valid.2
            intro occurrence occurrenceMem
            simp only [List.mem_singleton] at occurrenceMem
            subst occurrence
            exact active
      | eventuallyAtEnd selected interval body shape present atEnd =>
          simp only [List.mem_singleton] at childMem
          subst child
          apply Node.markedActive_replace valid.2
          intro occurrence occurrenceMem
          simp_all [AnnotatedOccurrence.child]
      | alwaysBeforeEnd selected interval body shape present active beforeEnd =>
          simp only [List.mem_singleton] at childMem
          subst child
          apply Node.markedActive_replace valid.2
          intro occurrence occurrenceMem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMem
          rcases occurrenceMem with rfl | rfl
          · exact active
          · trivial
      | alwaysAtEnd selected interval body shape present atEnd =>
          simp only [List.mem_singleton] at childMem
          subst child
          apply Node.markedActive_replace valid.2
          intro occurrence occurrenceMem
          simp_all [AnnotatedOccurrence.child]
      | strictUntilBeforeEnd selected interval invariant target shape present active beforeEnd =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
          rcases childMem with rfl | rfl
          · apply Node.markedActive_replace valid.2
            intro occurrence occurrenceMem
            simp only [List.mem_singleton] at occurrenceMem
            subst occurrence
            trivial
          · apply Node.markedActive_replace valid.2
            intro occurrence occurrenceMem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMem
            rcases occurrenceMem with rfl | rfl
            · exact active
            · trivial
      | strictUntilAtEnd selected interval invariant target shape present atEnd =>
          simp only [List.mem_singleton] at childMem
          subst child
          apply Node.markedActive_replace valid.2
          intro occurrence occurrenceMem
          simp_all [AnnotatedOccurrence.child]
      | strictReleaseBeforeEnd selected interval target invariant shape present active beforeEnd =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
          rcases childMem with rfl | rfl
          · apply Node.markedActive_replace valid.2
            intro occurrence occurrenceMem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMem
            rcases occurrenceMem with rfl | rfl <;> trivial
          · apply Node.markedActive_replace valid.2
            intro occurrence occurrenceMem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMem
            rcases occurrenceMem with rfl | rfl
            · exact active
            · trivial
      | strictReleaseAtEnd selected interval target invariant shape present atEnd =>
          simp only [List.mem_singleton] at childMem
          subst child
          apply Node.markedActive_replace valid.2
          intro occurrence occurrenceMem
          simp_all [AnnotatedOccurrence.child]
  | step notRejected poised hasTemporal jumpDisabled =>
      simp only [List.mem_singleton] at childMem
      subst child
      exact Node.step_markedActive
  | jump notRejected poised hasTemporal sound complete size computed =>
      simp only [List.mem_singleton] at childMem
      subst child
      exact Node.jump_markedActive size

end Rule
end Stlsat.Jump
