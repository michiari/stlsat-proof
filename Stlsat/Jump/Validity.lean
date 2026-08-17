/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.Semantics

/-!
# Semantic validity windows

Validity windows over-approximate every signal instant inspected while an STL
formula is evaluated.  This module relates the relative windows of a formula
to the absolute windows of its temporal expansion.
-/

namespace Stlsat.Tableau
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
      simp [ValidityOccurrence.prefixPath, ValidityOccurrence.shift,
        Stlsat.Interval.shift]
  | and left right ihLeft ihRight =>
      simp only [Stlsat.Formula.temporalExpansion, validityFrom, validityOccurrences,
        ihLeft, ihRight, List.map_append, List.map_map]
      congr 1
  | or left right ihLeft ihRight =>
      simp only [Stlsat.Formula.temporalExpansion, validityFrom, validityOccurrences,
        ihLeft, ihRight, List.map_append, List.map_map]
      congr 1
  | eventually interval body ih =>
      simp only [Stlsat.Formula.temporalExpansion, validityFrom, validityOccurrences,
        List.map_map]
      apply List.map_congr_left
      intro occurrence present
      cases occurrence
      simp [ValidityOccurrence.prefixPath, ValidityOccurrence.through,
        ValidityOccurrence.shift, Stlsat.Interval.shift]
      omega
  | always interval body ih =>
      simp only [Stlsat.Formula.temporalExpansion, validityFrom, validityOccurrences,
        List.map_map]
      apply List.map_congr_left
      intro occurrence present
      cases occurrence
      simp [ValidityOccurrence.prefixPath, ValidityOccurrence.through,
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
          simp [ValidityOccurrence.prefixPath,
            ValidityOccurrence.beforeTarget, ValidityOccurrence.shift,
            Stlsat.Interval.shift]
          omega
        · apply List.map_congr_left
          intro occurrence present
          cases occurrence
          simp [ValidityOccurrence.prefixPath,
            ValidityOccurrence.through, ValidityOccurrence.shift, Stlsat.Interval.shift]
          omega
      · have original : ¬interval.lower < interval.upper := by
          simpa [nontrivial] using shifted
        simp only [dif_neg original, List.nil_append]
        apply List.map_congr_left
        intro occurrence present
        cases occurrence
        simp [ValidityOccurrence.prefixPath,
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
          simp [ValidityOccurrence.prefixPath,
            ValidityOccurrence.beforeTarget, ValidityOccurrence.shift,
            Stlsat.Interval.shift]
          omega
        · apply List.map_congr_left
          intro occurrence present
          cases occurrence
          simp [ValidityOccurrence.prefixPath,
            ValidityOccurrence.through, ValidityOccurrence.shift, Stlsat.Interval.shift]
          omega
      · have original : ¬interval.lower < interval.upper := by
          simpa [nontrivial] using shifted
        simp only [dif_neg original, List.nil_append]
        apply List.map_congr_left
        intro occurrence present
        cases occurrence
        simp [ValidityOccurrence.prefixPath,
          ValidityOccurrence.through, ValidityOccurrence.shift, Stlsat.Interval.shift]
        omega

end FormulaValidity
end Stlsat.Tableau
