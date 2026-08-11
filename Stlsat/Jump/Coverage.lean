/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.LocalSoundness

namespace Stlsat.Jump
universe u
namespace Node

variable {Atom : Type u} [DecidableEq Atom]

omit [DecidableEq Atom] in
/-- The complete validity window of an independent marked parent covers every
leaf window of each strictly skipped invariant instance. -/
theorem postponedInvariant_covered_of_independent (node : Node Atom) {size offset : Nat}
    (computed : node.jumpSize? = some size) (strictlySkipped : offset < size)
    (source : AnnotatedOccurrence Atom) (sourceMem : source ∈ node.label)
    (notParentActive : ¬node.ParentActive source)
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
          let parentValidity := ValidityOccurrence.prefixPath 0 (validity.through interval)
          have parentValidityMem : parentValidity ∈
              FormulaValidity.validityOccurrences (.always interval body) := by
            simp only [parentValidity, FormulaValidity.validityOccurrences]
            exact List.mem_map.mpr ⟨validity, validityMem, rfl⟩
          let window := WindowOccurrence.ofValidity id parentValidity
          have windowMem : window ∈ node.independentWindows := by
            apply node.independentWindow_mem
              { id := id, payload := .markedAlways interval body, parent := parent }
              sourceMem
            · simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal]
            · exact notParentActive
            · exact parentValidityMem
          refine ⟨window, windowMem, ?_, ?_, ?_⟩
          · simp [window, parentValidity, WindowOccurrence.ofValidity,
              ValidityOccurrence.prefixPath, ValidityOccurrence.through,
              List.append_assoc]
          · simp [window, parentValidity, WindowOccurrence.ofValidity,
              ValidityOccurrence.prefixPath, ValidityOccurrence.through]
            omega
          · have destination := node.jump_destination_le_upper
                { id := id, payload := .markedAlways interval body, parent := parent }
                interval sourceMem rfl computed active.2
            simp [window, parentValidity, WindowOccurrence.ofValidity,
              ValidityOccurrence.prefixPath, ValidityOccurrence.through]
            omega
      | markedStrictUntil interval left right =>
          simp only [AnnotatedOccurrence.postponedInvariant?, Option.some.injEq,
            Prod.mk.injEq] at sourceShape
          rcases sourceShape with ⟨rfl, rfl⟩
          simp only [AnnotatedOccurrence.interval?] at active
          have nontrivial : interval.lower < interval.upper := by omega
          let parentValidity :=
            ValidityOccurrence.prefixPath 0 (validity.beforeTarget interval nontrivial)
          have parentValidityMem : parentValidity ∈
              FormulaValidity.validityOccurrences (.strictUntil interval left right) := by
            simp only [parentValidity, FormulaValidity.validityOccurrences, dif_pos nontrivial]
            apply List.mem_append.mpr
            exact Or.inl (List.mem_map.mpr ⟨validity, validityMem, rfl⟩)
          let window := WindowOccurrence.ofValidity id parentValidity
          have windowMem : window ∈ node.independentWindows := by
            apply node.independentWindow_mem
              { id := id, payload := .markedStrictUntil interval left right, parent := parent }
              sourceMem
            · simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal]
            · exact notParentActive
            · exact parentValidityMem
          refine ⟨window, windowMem, ?_, ?_, ?_⟩
          · simp [window, parentValidity, WindowOccurrence.ofValidity,
              ValidityOccurrence.prefixPath, ValidityOccurrence.beforeTarget,
              List.append_assoc]
          · simp [window, parentValidity, WindowOccurrence.ofValidity,
              ValidityOccurrence.prefixPath, ValidityOccurrence.beforeTarget]
            omega
          · have destination := node.jump_destination_le_upper
                { id := id, payload := .markedStrictUntil interval left right, parent := parent }
                interval sourceMem rfl computed active.2
            simp [window, parentValidity, WindowOccurrence.ofValidity,
              ValidityOccurrence.prefixPath, ValidityOccurrence.beforeTarget]
            omega
      | markedStrictRelease interval left right =>
          simp only [AnnotatedOccurrence.postponedInvariant?, Option.some.injEq,
            Prod.mk.injEq] at sourceShape
          rcases sourceShape with ⟨rfl, rfl⟩
          simp only [AnnotatedOccurrence.interval?] at active
          let parentValidity :=
            ValidityOccurrence.prefixPath 1 (validity.through interval)
          have parentValidityMem : parentValidity ∈
              FormulaValidity.validityOccurrences (.strictRelease interval left right) := by
            simp only [parentValidity, FormulaValidity.validityOccurrences]
            apply List.mem_append.mpr
            exact Or.inr (List.mem_map.mpr ⟨validity, validityMem, rfl⟩)
          let window := WindowOccurrence.ofValidity id parentValidity
          have windowMem : window ∈ node.independentWindows := by
            apply node.independentWindow_mem
              { id := id, payload := .markedStrictRelease interval left right, parent := parent }
              sourceMem
            · simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal]
            · exact notParentActive
            · exact parentValidityMem
          refine ⟨window, windowMem, ?_, ?_, ?_⟩
          · simp [window, parentValidity, WindowOccurrence.ofValidity,
              ValidityOccurrence.prefixPath, ValidityOccurrence.through,
              List.append_assoc]
          · simp [window, parentValidity, WindowOccurrence.ofValidity,
              ValidityOccurrence.prefixPath, ValidityOccurrence.through]
            omega
          · have destination := node.jump_destination_le_upper
                { id := id, payload := .markedStrictRelease interval left right, parent := parent }
                interval sourceMem rfl computed active.2
            simp [window, parentValidity, WindowOccurrence.ofValidity,
              ValidityOccurrence.prefixPath, ValidityOccurrence.through]
            omega

omit [DecidableEq Atom] in
/-- Two distinct leaf requirements generated by skipped invariant instances
cannot share an instant when the second marked parent is independent.  Thus an
invariant is tested against another invariant through the latter parent's
covering `O(u)` window. -/
theorem skippedInvariants_disjoint_of_secondIndependent (node : Node Atom)
    {size firstOffset secondOffset : Nat}
    (computed : node.jumpSize? = some size) (sound : node.SoundSafe)
    (firstSkipped : firstOffset < size) (secondSkipped : secondOffset < size)
    (first : AnnotatedOccurrence Atom) (firstMem : first ∈ node.label)
    (firstEdge : Nat) (firstInvariant : Stlsat.Formula Atom)
    (firstShape : first.postponedInvariant? = some (firstEdge, firstInvariant))
    (firstValidity : ValidityOccurrence)
    (firstValidityMem : firstValidity ∈
      FormulaValidity.validityOccurrences firstInvariant)
    (second : AnnotatedOccurrence Atom) (secondMem : second ∈ node.label)
    (secondIndependent : ¬node.ParentActive second)
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
  rcases node.postponedInvariant_covered_of_independent computed secondSkipped second
      secondMem secondIndependent secondEdge secondInvariant secondShape secondValidity
      secondValidityMem secondActive with
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

end Node
end Stlsat.Jump
