/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.Soundness

/-!
# Semantic validity windows

Validity windows over-approximate every signal instant inspected while an STL
formula is evaluated.  The main theorem states that two signals which agree
on those windows agree on the formula's truth value.
-/

namespace Stlsat.Jump
universe u

namespace FormulaValidity

variable {Atom : Type u}

/-- Validity windows of a formula as it occurs in a label at `time`.

Top-level propositional structure is evaluated at the node time, whereas a
top-level temporal operator already carries absolute bounds produced by
`temporalExpansion`. -/
def validityFrom (time : Nat) : Stlsat.Formula Atom → List ValidityOccurrence
  | .truth | .atom _ =>
      [{ path := [],
         window := { lower := time, upper := time, lower_le_upper := le_rfl } }]
  | .neg body => (validityFrom time body).map (ValidityOccurrence.prefixPath 0)
  | .and left right | .or left right =>
      (validityFrom time left).map (ValidityOccurrence.prefixPath 0) ++
        (validityFrom time right).map (ValidityOccurrence.prefixPath 1)
  | formula@(.eventually _ _) | formula@(.always _ _) |
      formula@(.strictUntil _ _ _) | formula@(.strictRelease _ _ _) =>
      validityOccurrences formula

@[simp]
theorem validityFrom_temporal (time : Nat) (formula : Stlsat.Formula Atom)
    (temporal : formula.isTemporal = true) :
    validityFrom time formula = validityOccurrences formula := by
  cases formula <;> simp_all [validityFrom, Stlsat.Formula.isTemporal]

/-- Expanding relative temporal bounds at `time` has the same effect on
validity windows as translating every relative validity occurrence by
`time`. -/
theorem validityFrom_temporalExpansion (formula : Stlsat.Formula Atom) (time : Nat) :
    validityFrom time (formula.temporalExpansion time) =
      (validityOccurrences formula).map (ValidityOccurrence.shift time) := by
  induction formula with
  | truth => simp [validityFrom, validityOccurrences, ValidityOccurrence.shift,
      Stlsat.Formula.temporalExpansion, Stlsat.Interval.shift]
  | atom proposition => simp [validityFrom, validityOccurrences, ValidityOccurrence.shift,
      Stlsat.Formula.temporalExpansion, Stlsat.Interval.shift]
  | neg body ih =>
      simp only [Stlsat.Formula.temporalExpansion, validityFrom, validityOccurrences, ih,
        List.map_map]
      apply List.map_congr_left
      intro occurrence present
      cases occurrence
      simp [Function.comp_def, ValidityOccurrence.prefixPath, ValidityOccurrence.shift,
        Stlsat.Interval.shift]
  | and left right ihLeft ihRight =>
      simp only [Stlsat.Formula.temporalExpansion, validityFrom, validityOccurrences,
        ihLeft, ihRight, List.map_append, List.map_map]
      congr 1 <;> apply List.map_congr_left <;> intro occurrence present <;>
        cases occurrence <;>
        simp [Function.comp_def, ValidityOccurrence.prefixPath, ValidityOccurrence.shift,
          Stlsat.Interval.shift]
  | or left right ihLeft ihRight =>
      simp only [Stlsat.Formula.temporalExpansion, validityFrom, validityOccurrences,
        ihLeft, ihRight, List.map_append, List.map_map]
      congr 1 <;> apply List.map_congr_left <;> intro occurrence present <;>
        cases occurrence <;>
        simp [Function.comp_def, ValidityOccurrence.prefixPath, ValidityOccurrence.shift,
          Stlsat.Interval.shift]
  | eventually interval body ih =>
      simp only [Stlsat.Formula.temporalExpansion, validityFrom, validityOccurrences,
        List.map_map]
      apply List.map_congr_left
      intro occurrence present
      cases occurrence
      simp [Function.comp_def, ValidityOccurrence.prefixPath, ValidityOccurrence.through,
        ValidityOccurrence.shift, Stlsat.Interval.shift]
      omega
  | always interval body ih =>
      simp only [Stlsat.Formula.temporalExpansion, validityFrom, validityOccurrences,
        List.map_map]
      apply List.map_congr_left
      intro occurrence present
      cases occurrence
      simp [Function.comp_def, ValidityOccurrence.prefixPath, ValidityOccurrence.through,
        ValidityOccurrence.shift, Stlsat.Interval.shift]
      omega
  | strictUntil interval left right ihLeft ihRight =>
      simp only [Stlsat.Formula.temporalExpansion, validityFrom, validityOccurrences,
        List.map_append, List.map_map]
      have nontrivial : interval.lower < interval.upper ↔
          (interval.shift time).lower < (interval.shift time).upper := by
        simp [Stlsat.Interval.shift]
      split <;> rename_i shifted
      · have original : interval.lower < interval.upper := nontrivial.mpr shifted
        simp only [dif_pos original]
        simp only [List.map_map]
        congr 1
        · apply List.map_congr_left
          intro occurrence present
          cases occurrence
          simp [Function.comp_def, ValidityOccurrence.prefixPath,
            ValidityOccurrence.beforeTarget, ValidityOccurrence.shift,
            Stlsat.Interval.shift]
          omega
        · apply List.map_congr_left
          intro occurrence present
          cases occurrence
          simp [Function.comp_def, ValidityOccurrence.prefixPath,
            ValidityOccurrence.through, ValidityOccurrence.shift, Stlsat.Interval.shift]
          omega
      · have original : ¬interval.lower < interval.upper := by
          simpa [nontrivial] using shifted
        simp only [dif_neg original, List.nil_append, List.map_map]
        apply List.map_congr_left
        intro occurrence present
        cases occurrence
        simp [Function.comp_def, ValidityOccurrence.prefixPath,
          ValidityOccurrence.through, ValidityOccurrence.shift, Stlsat.Interval.shift]
        omega
  | strictRelease interval left right ihLeft ihRight =>
      simp only [Stlsat.Formula.temporalExpansion, validityFrom, validityOccurrences,
        List.map_append, List.map_map]
      have nontrivial : interval.lower < interval.upper ↔
          (interval.shift time).lower < (interval.shift time).upper := by
        simp [Stlsat.Interval.shift]
      split <;> rename_i shifted
      · have original : interval.lower < interval.upper := nontrivial.mpr shifted
        simp only [dif_pos original]
        simp only [List.map_map]
        congr 1
        · apply List.map_congr_left
          intro occurrence present
          cases occurrence
          simp [Function.comp_def, ValidityOccurrence.prefixPath,
            ValidityOccurrence.beforeTarget, ValidityOccurrence.shift,
            Stlsat.Interval.shift]
          omega
        · apply List.map_congr_left
          intro occurrence present
          cases occurrence
          simp [Function.comp_def, ValidityOccurrence.prefixPath,
            ValidityOccurrence.through, ValidityOccurrence.shift, Stlsat.Interval.shift]
          omega
      · have original : ¬interval.lower < interval.upper := by
          simpa [nontrivial] using shifted
        simp only [dif_neg original, List.nil_append, List.map_map]
        apply List.map_congr_left
        intro occurrence present
        cases occurrence
        simp [Function.comp_def, ValidityOccurrence.prefixPath,
          ValidityOccurrence.through, ValidityOccurrence.shift, Stlsat.Interval.shift]
        omega

def SignalsAgree (formula : Stlsat.Formula Atom) (start : Nat)
    {semantics : Stlsat.AtomicSemantics Atom}
    (left right : Stlsat.Signal semantics) : Prop :=
  ∀ occurrence ∈ validityOccurrences formula, ∀ instant,
    start + occurrence.window.lower ≤ instant →
    instant ≤ start + occurrence.window.upper → left instant = right instant

theorem satisfies_congr_of_signalsAgree (formula : Stlsat.Formula Atom)
    (semantics : Stlsat.AtomicSemantics Atom) {left right : Stlsat.Signal semantics}
    {start : Nat} (agree : SignalsAgree formula start left right) :
    formula.Satisfies semantics left start ↔ formula.Satisfies semantics right start := by
  induction formula generalizing start with
  | truth => simp [Stlsat.Formula.Satisfies]
  | atom proposition =>
      let base : ValidityOccurrence :=
        { path := [], window := { lower := 0, upper := 0, lower_le_upper := le_rfl } }
      have atStart : left start = right start := by
        apply agree base
        · simp only [validityOccurrences, List.mem_cons, List.not_mem_nil, or_false]
          dsimp [base]
        · simp [base]
        · simp [base]
      simp [Stlsat.Formula.Satisfies, atStart]
  | neg body ih =>
      simp only [Stlsat.Formula.Satisfies]
      apply not_congr
      apply ih
      intro occurrence occurrenceMem instant lower upper
      apply agree (occurrence.prefixPath 0)
      · simp only [validityOccurrences]
        exact List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩
      · exact lower
      · exact upper
  | and leftFormula rightFormula ihLeft ihRight =>
      simp only [Stlsat.Formula.Satisfies]
      apply and_congr
      · apply ihLeft
        intro occurrence occurrenceMem instant lower upper
        apply agree (occurrence.prefixPath 0)
        · simp only [validityOccurrences]
          apply List.mem_append.mpr
          exact Or.inl (List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩)
        · exact lower
        · exact upper
      · apply ihRight
        intro occurrence occurrenceMem instant lower upper
        apply agree (occurrence.prefixPath 1)
        · simp only [validityOccurrences]
          apply List.mem_append.mpr
          exact Or.inr (List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩)
        · exact lower
        · exact upper
  | or leftFormula rightFormula ihLeft ihRight =>
      simp only [Stlsat.Formula.Satisfies]
      apply or_congr
      · apply ihLeft
        intro occurrence occurrenceMem instant lower upper
        apply agree (occurrence.prefixPath 0)
        · simp only [validityOccurrences]
          apply List.mem_append.mpr
          exact Or.inl (List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩)
        · exact lower
        · exact upper
      · apply ihRight
        intro occurrence occurrenceMem instant lower upper
        apply agree (occurrence.prefixPath 1)
        · simp only [validityOccurrences]
          apply List.mem_append.mpr
          exact Or.inr (List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩)
        · exact lower
        · exact upper
  | eventually interval body ih =>
      simp only [Stlsat.Formula.Satisfies]
      apply exists_congr
      intro offset
      apply and_congr_right
      intro contained
      apply ih
      intro occurrence occurrenceMem instant lower upper
      apply agree (ValidityOccurrence.prefixPath 0 (occurrence.through interval))
      · simp only [validityOccurrences]
        exact List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩
      · simp only [ValidityOccurrence.prefixPath, ValidityOccurrence.through]
        rcases contained with ⟨offsetLower, offsetUpper⟩
        omega
      · simp only [ValidityOccurrence.prefixPath, ValidityOccurrence.through]
        rcases contained with ⟨offsetLower, offsetUpper⟩
        omega
  | always interval body ih =>
      simp only [Stlsat.Formula.Satisfies]
      apply forall_congr'
      intro offset
      apply imp_congr_right
      intro contained
      apply ih
      intro occurrence occurrenceMem instant lower upper
      apply agree (ValidityOccurrence.prefixPath 0 (occurrence.through interval))
      · simp only [validityOccurrences]
        exact List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩
      · simp only [ValidityOccurrence.prefixPath, ValidityOccurrence.through]
        rcases contained with ⟨offsetLower, offsetUpper⟩
        omega
      · simp only [ValidityOccurrence.prefixPath, ValidityOccurrence.through]
        rcases contained with ⟨offsetLower, offsetUpper⟩
        omega
  | strictUntil interval invariant target ihInvariant ihTarget =>
      simp only [Stlsat.Formula.Satisfies]
      apply exists_congr
      intro targetOffset
      apply and_congr_right
      intro targetContained
      apply and_congr
      · apply ihTarget
        intro occurrence occurrenceMem instant lower upper
        apply agree (ValidityOccurrence.prefixPath 1 (occurrence.through interval))
        · simp only [validityOccurrences]
          apply List.mem_append.mpr
          exact Or.inr (List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩)
        · simp only [ValidityOccurrence.prefixPath, ValidityOccurrence.through]
          rcases targetContained with ⟨targetLower, targetUpper⟩
          omega
        · simp only [ValidityOccurrence.prefixPath, ValidityOccurrence.through]
          rcases targetContained with ⟨targetLower, targetUpper⟩
          omega
      · apply forall_congr'
        intro invariantOffset
        apply imp_congr_right
        intro invariantLower
        apply imp_congr_right
        intro beforeTarget
        have nontrivial : interval.lower < interval.upper := by
          rcases targetContained with ⟨_, targetUpper⟩
          omega
        apply ihInvariant
        intro occurrence occurrenceMem instant lower upper
        apply agree (ValidityOccurrence.prefixPath 0
          (occurrence.beforeTarget interval nontrivial))
        · simp only [validityOccurrences, dif_pos nontrivial]
          apply List.mem_append.mpr
          exact Or.inl (List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩)
        · simp only [ValidityOccurrence.prefixPath, ValidityOccurrence.beforeTarget]
          omega
        · simp only [ValidityOccurrence.prefixPath, ValidityOccurrence.beforeTarget]
          rcases targetContained with ⟨_, targetUpper⟩
          omega
  | strictRelease interval target invariant ihTarget ihInvariant =>
      simp only [Stlsat.Formula.Satisfies]
      apply not_congr
      apply exists_congr
      intro violatingOffset
      apply and_congr_right
      intro violatingContained
      apply and_congr
      · apply not_congr
        apply ihInvariant
        intro occurrence occurrenceMem instant lower upper
        apply agree (ValidityOccurrence.prefixPath 1 (occurrence.through interval))
        · simp only [validityOccurrences]
          apply List.mem_append.mpr
          exact Or.inr (List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩)
        · simp only [ValidityOccurrence.prefixPath, ValidityOccurrence.through]
          rcases violatingContained with ⟨violatingLower, violatingUpper⟩
          omega
        · simp only [ValidityOccurrence.prefixPath, ValidityOccurrence.through]
          rcases violatingContained with ⟨violatingLower, violatingUpper⟩
          omega
      · apply forall_congr'
        intro targetOffset
        apply imp_congr_right
        intro targetLower
        apply imp_congr_right
        intro beforeViolation
        apply not_congr
        have nontrivial : interval.lower < interval.upper := by
          rcases violatingContained with ⟨_, violatingUpper⟩
          omega
        apply ihTarget
        intro occurrence occurrenceMem instant lower upper
        apply agree (ValidityOccurrence.prefixPath 0
          (occurrence.beforeTarget interval nontrivial))
        · simp only [validityOccurrences, dif_pos nontrivial]
          apply List.mem_append.mpr
          exact Or.inl (List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩)
        · simp only [ValidityOccurrence.prefixPath, ValidityOccurrence.beforeTarget]
          omega
        · simp only [ValidityOccurrence.prefixPath, ValidityOccurrence.beforeTarget]
          rcases violatingContained with ⟨_, violatingUpper⟩
          omega

end FormulaValidity
end Stlsat.Jump
