/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.CompatibleSplicing

/-!
# Variable support for validity-window conflicts

The ordinary JUMP guard treats every two distinct canonical leaves as
potentially conflicting.  This module records the signed leaf belonging to a
window and defines the less conservative guard which only separates distinct
atomic leaves whose variable supports overlap.

This syntactic optimization is not sound for an arbitrary `AtomicSemantics`.
`AtomicSupport.amalgamate` is the exact additional semantic hypothesis used
below: at one instant, valuations carrying equal signed tests or tests on
disjoint supports can be amalgamated into one valuation.
-/

namespace Stlsat.Tableau

universe u v w

namespace FormulaValidity

variable {Atom : Type u}

namespace SignedLeaf

/-- Variable support of a signed leaf. -/
def support {Var : Type w} (atomSupport : Atom → Finset Var) :
    SignedLeaf Atom → Finset Var
  | .truth | .falsity => ∅
  | .positive atom | .negative atom => atomSupport atom

@[simp] theorem support_truth {Var : Type w} (atomSupport : Atom → Finset Var) :
    (truth : SignedLeaf Atom).support atomSupport = ∅ := rfl

@[simp] theorem support_falsity {Var : Type w} (atomSupport : Atom → Finset Var) :
    (falsity : SignedLeaf Atom).support atomSupport = ∅ := rfl

@[simp] theorem support_positive {Var : Type w} (atomSupport : Atom → Finset Var)
    (atom : Atom) : (positive atom).support atomSupport = atomSupport atom := rfl

@[simp] theorem support_negative {Var : Type w} (atomSupport : Atom → Finset Var)
    (atom : Atom) : (negative atom).support atomSupport = atomSupport atom := rfl

end SignedLeaf

/-- A validity window retaining its signed semantic leaf. -/
structure SupportedWindowOccurrence (Atom : Type u) where
  id : OccurrenceId
  window : Stlsat.Interval
  leaf : SignedLeaf Atom
deriving DecidableEq

namespace SupportedWindowOccurrence

/-- Attach the canonical formula-root identity to a semantic occurrence. -/
def ofSemantic (root : OccurrenceId) (occurrence : SemanticOccurrence Atom) :
    SupportedWindowOccurrence Atom where
  id := root ++ occurrence.path
  window := occurrence.window
  leaf := occurrence.leaf

/-- Shift only the temporal window. -/
def shift (offset : Nat) (occurrence : SupportedWindowOccurrence Atom) :
    SupportedWindowOccurrence Atom where
  id := occurrence.id
  window := occurrence.window.shift offset
  leaf := occurrence.leaf

/-- Forget signed-leaf metadata. -/
def erase (occurrence : SupportedWindowOccurrence Atom) : WindowOccurrence where
  id := occurrence.id
  window := occurrence.window

@[simp] theorem erase_ofSemantic (root : OccurrenceId)
    (occurrence : SemanticOccurrence Atom) :
    (ofSemantic root occurrence).erase = WindowOccurrence.ofValidity root occurrence.toValidity :=
  by rfl

@[simp] theorem erase_shift (offset : Nat) (occurrence : SupportedWindowOccurrence Atom) :
    (occurrence.shift offset).erase = occurrence.erase.shift offset := by rfl

end SupportedWindowOccurrence

private def supportedWindowsOf (root : OccurrenceId) (formula : Stlsat.Formula Atom) :
    List (SupportedWindowOccurrence Atom) :=
  (semanticOccurrences formula).map (SupportedWindowOccurrence.ofSemantic root)

/-- Signed and unsigned validity occurrence generation have exactly the same
paths and windows. -/
theorem map_toValidity_semanticOccurrences (formula : Stlsat.Formula Atom) :
    (semanticOccurrences formula).map SemanticOccurrence.toValidity =
      validityOccurrences formula := by
  induction formula with
  | truth => rfl
  | atom atom => rfl
  | neg body ih =>
      simp only [semanticOccurrences, validityOccurrences]
      rw [← ih]
      simp only [List.map_map]
      apply List.map_congr_left
      intro occurrence occurrenceMem
      simp [SemanticOccurrence.toValidity, SemanticOccurrence.negate,
        SemanticOccurrence.prefixPath, ValidityOccurrence.prefixPath]
  | and left right ihLeft ihRight =>
      simp only [semanticOccurrences, validityOccurrences, List.map_append]
      rw [← ihLeft, ← ihRight]
      simp only [List.map_map]
      congr 1
  | or left right ihLeft ihRight =>
      simp only [semanticOccurrences, validityOccurrences, List.map_append]
      rw [← ihLeft, ← ihRight]
      simp only [List.map_map]
      congr 1
  | eventually interval body ih =>
      simp only [semanticOccurrences, validityOccurrences]
      rw [← ih]
      simp only [List.map_map]
      apply List.map_congr_left
      intro occurrence occurrenceMem
      simp [SemanticOccurrence.toValidity, SemanticOccurrence.prefixPath,
        SemanticOccurrence.through, ValidityOccurrence.prefixPath,
        ValidityOccurrence.through]
  | always interval body ih =>
      simp only [semanticOccurrences, validityOccurrences]
      rw [← ih]
      simp only [List.map_map]
      apply List.map_congr_left
      intro occurrence occurrenceMem
      simp [SemanticOccurrence.toValidity, SemanticOccurrence.prefixPath,
        SemanticOccurrence.through, ValidityOccurrence.prefixPath,
        ValidityOccurrence.through]
  | strictUntil interval left right ihLeft ihRight =>
      by_cases nontrivial : interval.lower < interval.upper
      · simp only [semanticOccurrences, validityOccurrences, dif_pos nontrivial,
          List.map_append]
        rw [← ihLeft, ← ihRight]
        simp only [List.map_map]
        congr 1
      · simp only [semanticOccurrences, validityOccurrences, dif_neg nontrivial,
          List.nil_append]
        rw [← ihRight]
        simp only [List.map_map]
        apply List.map_congr_left
        intro occurrence occurrenceMem
        simp [SemanticOccurrence.toValidity, SemanticOccurrence.prefixPath,
          SemanticOccurrence.through, ValidityOccurrence.prefixPath,
          ValidityOccurrence.through]
  | strictRelease interval left right ihLeft ihRight =>
      by_cases nontrivial : interval.lower < interval.upper
      · simp only [semanticOccurrences, validityOccurrences, dif_pos nontrivial,
          List.map_append]
        rw [← ihLeft, ← ihRight]
        simp only [List.map_map]
        congr 1
      · simp only [semanticOccurrences, validityOccurrences, dif_neg nontrivial,
          List.nil_append]
        rw [← ihRight]
        simp only [List.map_map]
        apply List.map_congr_left
        intro occurrence occurrenceMem
        simp [SemanticOccurrence.toValidity, SemanticOccurrence.prefixPath,
          SemanticOccurrence.through, ValidityOccurrence.prefixPath,
          ValidityOccurrence.through]

/-- Every unsigned validity occurrence has a signed refinement. -/
theorem exists_semanticOccurrence_of_mem {formula : Stlsat.Formula Atom}
    {validity : ValidityOccurrence} (present : validity ∈ validityOccurrences formula) :
    ∃ semantic ∈ semanticOccurrences formula, semantic.toValidity = validity := by
  rw [← map_toValidity_semanticOccurrences formula] at present
  exact List.mem_map.mp present

end FormulaValidity

/-- Semantic variable-support data for an atomic theory.  `Amalgamates` is
deliberately a property rather than a field of `AtomicSemantics`: the original
tableau remains valid for completely abstract atomic theories. -/
structure AtomicSupport {Atom : Type u} (semantics : Stlsat.AtomicSemantics Atom)
    (Var : Type w) [DecidableEq Var] where
  /-- Variables on which an atom semantically depends. -/
  atomSupport : Atom → Finset Var
  /-- Global, instantaneous amalgamation needed by variable-aware splicing.

  The first alternative covers demands already satisfied by one valuation;
  the second covers repeated copies of one signed atom; the last covers
  genuinely independent demands. -/
  amalgamate :
    ∀ {Index : Type (max u w)}
      (leaf : Index → FormulaValidity.SignedLeaf Atom)
      (valuation : Index → semantics.Valuation),
      (∀ index, (leaf index).Holds semantics (valuation index)) →
      (∀ left right,
        valuation left = valuation right ∨ leaf left = leaf right ∨
          Disjoint ((leaf left).support atomSupport) ((leaf right).support atomSupport)) →
      ∃ combined : semantics.Valuation,
        ∀ index, (leaf index).Holds semantics combined

namespace AtomicSupport

/-- Component-wise satisfiability is a sound general replacement for an
invalid pairwise-satisfiability test.  Demands in one component share a
component model; distinct components have disjoint supports, so the global
amalgamation law combines all component models. -/
theorem amalgamate_of_components
    {Atom : Type u} {Var : Type w} [DecidableEq Var]
    {semantics : Stlsat.AtomicSemantics Atom}
    (support : AtomicSupport semantics Var)
    {Index : Type (max u w)} {Component : Type v}
    (component : Index → Component)
    (leaf : Index → FormulaValidity.SignedLeaf Atom)
    (valuation : Index → semantics.Valuation)
    (holds : ∀ index, (leaf index).Holds semantics (valuation index))
    (sameComponent : ∀ left right,
      component left = component right → valuation left = valuation right)
    (separateComponents : ∀ left right,
      component left ≠ component right →
        Disjoint ((leaf left).support support.atomSupport)
          ((leaf right).support support.atomSupport)) :
    ∃ combined : semantics.Valuation,
      ∀ index, (leaf index).Holds semantics combined := by
  apply support.amalgamate leaf valuation holds
  intro left right
  by_cases same : component left = component right
  · exact Or.inl (sameComponent left right same)
  · exact Or.inr (Or.inr (separateComponents left right same))

end AtomicSupport

namespace FormulaValidity

variable {Atom : Type u} {Var : Type w} [DecidableEq Var]
  {semantics : Stlsat.AtomicSemantics Atom}

namespace SemanticRequirement

/-- Cross-requirement compatibility used by the variable-aware guard. -/
def SupportCompatible (atomSupport : Atom → Finset Var)
    (left right : SemanticRequirement semantics) : Prop :=
  ∀ leftOccurrence ∈ left.leaves, ∀ rightOccurrence ∈ right.leaves, ∀ instant,
    leftOccurrence.window.lower ≤ instant → instant ≤ leftOccurrence.window.upper →
    rightOccurrence.window.lower ≤ instant → instant ≤ rightOccurrence.window.upper →
      (left.root ++ leftOccurrence.path = right.root ++ rightOccurrence.path ∧
          leftOccurrence.leaf = rightOccurrence.leaf) ∨
        Disjoint (leftOccurrence.leaf.support atomSupport)
          (rightOccurrence.leaf.support atomSupport)

omit [DecidableEq Var] in
theorem SupportCompatible.symm
    {left right : SemanticRequirement semantics} {atomSupport : Atom → Finset Var}
    (compatible : left.SupportCompatible atomSupport right) :
    right.SupportCompatible atomSupport left := by
  intro rightOccurrence rightMem leftOccurrence leftMem instant
    rightLower rightUpper leftLower leftUpper
  rcases compatible leftOccurrence leftMem rightOccurrence rightMem instant
    leftLower leftUpper rightLower rightUpper with same | disjoint
  · exact Or.inl ⟨same.1.symm, same.2.symm⟩
  · exact Or.inr disjoint.symm

end SemanticRequirement

/-- Variable-aware replacement for
`exists_signal_accepting_semanticRequirement_family`.  Unlike the original
choice construction, this theorem may have several simultaneous demands at
one instant and therefore invokes `AtomicSupport.Amalgamates`. -/
theorem exists_signal_accepting_supportCompatible_family
    (support : Stlsat.Tableau.AtomicSupport semantics Var)
    {Index : Type u} (requirement : Index → SemanticRequirement semantics)
    (compatible : ∀ left right,
      (requirement left).signal = (requirement right).signal ∨
        (requirement left).SupportCompatible support.atomSupport (requirement right)) :
    ∃ signal : Stlsat.Signal semantics, ∀ index, (requirement index).Accepts signal := by
  classical
  let Demand (instant : Nat) :=
    { demand : Index × SemanticOccurrence Atom //
      demand.2 ∈ (requirement demand.1).leaves ∧
        demand.2.window.lower ≤ instant ∧ instant ≤ demand.2.window.upper ∧
        demand.2.leaf.Holds semantics ((requirement demand.1).signal instant) }
  let combinedAt (instant : Nat) : semantics.Valuation :=
    if nonempty : Nonempty (Demand instant) then
      Classical.choose (support.amalgamate
        (fun demand : ULift.{max u w, u} (Demand instant) ↦ demand.down.1.2.leaf)
        (fun demand : ULift.{max u w, u} (Demand instant) ↦
          (requirement demand.down.1.1).signal instant)
        (fun demand ↦ demand.down.2.2.2.2)
        (by
          intro left right
          rcases compatible left.down.1.1 right.down.1.1 with sameSignal | cross
          · exact Or.inl (congrFun sameSignal instant)
          · rcases cross left.down.1.2 left.down.2.1 right.down.1.2 right.down.2.1 instant
                left.down.2.2.1 left.down.2.2.2.1 right.down.2.2.1
                right.down.2.2.2.1 with same | disjoint
            · exact Or.inr (Or.inl same.2)
            · exact Or.inr (Or.inr disjoint)))
    else Classical.choice semantics.nonempty
  let combined : Stlsat.Signal semantics := fun instant ↦ combinedAt instant
  refine ⟨combined, ?_⟩
  intro index
  apply (requirement index).preserves combined
  intro occurrence occurrenceMem instant lower upper leafHolds
  let demand : Demand instant :=
    ⟨(index, occurrence), occurrenceMem, lower, upper, leafHolds⟩
  have nonempty : Nonempty (Demand instant) := ⟨demand⟩
  have chosenSpec := Classical.choose_spec (support.amalgamate
    (fun demand : ULift.{max u w, u} (Demand instant) ↦ demand.down.1.2.leaf)
    (fun demand : ULift.{max u w, u} (Demand instant) ↦
      (requirement demand.down.1.1).signal instant)
    (fun demand ↦ demand.down.2.2.2.2)
    (by
      intro left right
      rcases compatible left.down.1.1 right.down.1.1 with sameSignal | cross
      · exact Or.inl (congrFun sameSignal instant)
      · rcases cross left.down.1.2 left.down.2.1 right.down.1.2 right.down.2.1 instant
            left.down.2.2.1 left.down.2.2.2.1 right.down.2.2.1
            right.down.2.2.2.1 with same | disjoint
        · exact Or.inr (Or.inl same.2)
        · exact Or.inr (Or.inr disjoint))) (ULift.up demand)
  simpa only [combined, combinedAt, dif_pos nonempty] using chosenSpec

end FormulaValidity

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

open FormulaValidity

/-- Signed counterpart of `N(u)`. -/
noncomputable def supportedInvariantWindows (node : Node Atom) :
    List (SupportedWindowOccurrence Atom) :=
  node.label.toList.flatMap fun occurrence ↦
    match occurrence.postponedInvariant? with
    | none => []
    | some (edge, invariant) =>
        (FormulaValidity.supportedWindowsOf (occurrence.id ++ [edge]) invariant).map
          (SupportedWindowOccurrence.shift node.time)

/-- Signed counterpart of `M(u)`. -/
noncomputable def supportedTargetWindows (node : Node Atom) :
    List (SupportedWindowOccurrence Atom) :=
  node.label.toList.flatMap fun occurrence ↦
    match occurrence.postponedTarget? with
    | none => []
    | some (edge, target) =>
        (FormulaValidity.supportedWindowsOf (occurrence.id ++ [edge]) target).map
          (SupportedWindowOccurrence.shift node.time)

/-- Signed counterpart of `O(u)`. -/
noncomputable def supportedIndependentWindows (node : Node Atom) :
    List (SupportedWindowOccurrence Atom) := by
  classical
  exact node.label.toList.flatMap fun occurrence ↦
    if occurrence.isTemporal = true ∧ ¬node.ParentActive occurrence then
      FormulaValidity.supportedWindowsOf occurrence.id occurrence.formula
    else []

/-- Current-time signed atomic constraints. -/
noncomputable def supportedAtomicConflictWindows (node : Node Atom) :
    List (SupportedWindowOccurrence Atom) := by
  classical
  exact node.label.toList.flatMap fun occurrence ↦
    if node.ParentActive occurrence then []
    else
      match occurrence.payload with
      | .unmarked (.atom atom) =>
          [{ id := occurrence.id,
             window := ⟨node.time, node.time, le_rfl⟩,
             leaf := .positive atom }]
      | .unmarked (.neg (.atom atom)) =>
          [{ id := occurrence.id ++ [0],
             window := ⟨node.time, node.time, le_rfl⟩,
             leaf := .negative atom }]
      | _ => []

/-- Signed counterpart of the revised `S(u)`. -/
noncomputable def supportedConflictWindows (node : Node Atom) :
    List (SupportedWindowOccurrence Atom) :=
  node.supportedIndependentWindows ++ node.supportedAtomicConflictWindows

omit [DecidableEq Atom] in
/-- Erasing signed metadata sends supported invariant windows to `N(u)`. -/
theorem erase_mem_invariantWindows (node : Node Atom)
    {window : SupportedWindowOccurrence Atom}
    (present : window ∈ node.supportedInvariantWindows) :
    window.erase ∈ node.invariantWindows := by
  classical
  unfold supportedInvariantWindows at present
  rcases List.mem_flatMap.mp present with ⟨occurrence, occurrenceMem, present⟩
  cases shape : occurrence.postponedInvariant? with
  | none => simp [shape] at present
  | some data =>
      rcases data with ⟨edge, invariant⟩
      rw [shape] at present
      rcases List.mem_map.mp present with ⟨supported, supportedMem, rfl⟩
      rcases List.mem_map.mp supportedMem with ⟨leaf, leafMem, rfl⟩
      exact node.invariantWindow_mem occurrence (Finset.mem_toList.mp occurrenceMem)
        edge invariant shape leaf.toValidity
        (toValidity_mem_validityOccurrences invariant leaf leafMem)

omit [DecidableEq Atom] in
/-- Erasing signed metadata sends supported target windows to `M(u)`. -/
theorem erase_mem_targetWindows (node : Node Atom)
    {window : SupportedWindowOccurrence Atom}
    (present : window ∈ node.supportedTargetWindows) :
    window.erase ∈ node.targetWindows := by
  classical
  unfold supportedTargetWindows at present
  rcases List.mem_flatMap.mp present with ⟨occurrence, occurrenceMem, present⟩
  cases shape : occurrence.postponedTarget? with
  | none => simp [shape] at present
  | some data =>
      rcases data with ⟨edge, target⟩
      rw [shape] at present
      rcases List.mem_map.mp present with ⟨supported, supportedMem, rfl⟩
      rcases List.mem_map.mp supportedMem with ⟨leaf, leafMem, rfl⟩
      exact node.targetWindow_mem occurrence (Finset.mem_toList.mp occurrenceMem)
        edge target shape leaf.toValidity
        (toValidity_mem_validityOccurrences target leaf leafMem)

omit [DecidableEq Atom] in
/-- Erasing signed metadata sends supported independent windows to `O(u)`. -/
theorem erase_mem_independentWindows (node : Node Atom)
    {window : SupportedWindowOccurrence Atom}
    (present : window ∈ node.supportedIndependentWindows) :
    window.erase ∈ node.independentWindows := by
  classical
  unfold supportedIndependentWindows at present
  rcases List.mem_flatMap.mp present with ⟨occurrence, occurrenceMem, present⟩
  split at present
  next selected =>
    rcases selected with ⟨temporal, notParentActive⟩
    rcases List.mem_map.mp present with ⟨leaf, leafMem, rfl⟩
    exact node.independentWindow_mem occurrence (Finset.mem_toList.mp occurrenceMem)
      temporal notParentActive leaf.toValidity
      (toValidity_mem_validityOccurrences occurrence.formula leaf leafMem)
  next => simp at present

omit [DecidableEq Atom] in
/-- Erasing signed metadata sends supported current literals to the original
atomic conflict set. -/
theorem erase_mem_atomicConflictWindows (node : Node Atom)
    {window : SupportedWindowOccurrence Atom}
    (present : window ∈ node.supportedAtomicConflictWindows) :
    window.erase ∈ node.atomicConflictWindows := by
  classical
  unfold supportedAtomicConflictWindows at present
  unfold atomicConflictWindows
  rcases List.mem_flatMap.mp present with ⟨occurrence, occurrenceMem, present⟩
  apply List.mem_flatMap.mpr
  refine ⟨occurrence, occurrenceMem, ?_⟩
  by_cases parentActive : node.ParentActive occurrence
  · simp [parentActive] at present
  · simp only [parentActive, if_false] at present ⊢
    cases occurrence with
    | mk id payload parent =>
        cases payload with
        | unmarked formula =>
            cases formula with
            | truth => simp at present
            | atom atom =>
                simp only [List.mem_singleton] at present ⊢
                subst window
                rfl
            | neg body =>
              cases body with
              | truth => simp at present
              | atom atom =>
                  simp only [List.mem_singleton] at present ⊢
                  subst window
                  rfl
              | neg nested => simp at present
              | and left right => simp at present
              | or left right => simp at present
              | eventually interval nested => simp at present
              | always interval nested => simp at present
              | strictUntil interval left right => simp at present
              | strictRelease interval left right => simp at present
            | and left right => simp at present
            | or left right => simp at present
            | eventually interval body => simp at present
            | always interval body => simp at present
            | strictUntil interval left right => simp at present
            | strictRelease interval left right => simp at present
        | markedEventually interval body => simp at present
        | markedAlways interval body => simp at present
        | markedStrictUntil interval invariant target => simp at present
        | markedStrictRelease interval target invariant => simp at present

omit [DecidableEq Atom] in
theorem erase_mem_conflictWindows (node : Node Atom)
    {window : SupportedWindowOccurrence Atom}
    (present : window ∈ node.supportedConflictWindows) :
    window.erase ∈ node.conflictWindows := by
  rcases List.mem_append.mp present with independent | atom
  · exact node.independentWindow_mem_conflictWindows _
      (node.erase_mem_independentWindows independent)
  · exact node.atomicWindow_mem_conflictWindows _
      (node.erase_mem_atomicConflictWindows atom)

omit [DecidableEq Atom] in
theorem supportedInvariantWindow_mem (node : Node Atom)
    (occurrence : AnnotatedOccurrence Atom) (present : occurrence ∈ node.label)
    (edge : Nat) (invariant : Stlsat.Formula Atom)
    (shape : occurrence.postponedInvariant? = some (edge, invariant))
    (leaf : SemanticOccurrence Atom) (leafMem : leaf ∈ semanticOccurrences invariant) :
    ((SupportedWindowOccurrence.ofSemantic (occurrence.id ++ [edge]) leaf).shift node.time) ∈
      node.supportedInvariantWindows := by
  classical
  unfold supportedInvariantWindows
  apply List.mem_flatMap.mpr
  refine ⟨occurrence, Finset.mem_toList.mpr present, ?_⟩
  rw [shape]
  apply List.mem_map.mpr
  exact ⟨SupportedWindowOccurrence.ofSemantic (occurrence.id ++ [edge]) leaf,
    List.mem_map.mpr ⟨leaf, leafMem, rfl⟩, rfl⟩

omit [DecidableEq Atom] in
theorem supportedTargetWindow_mem (node : Node Atom)
    (occurrence : AnnotatedOccurrence Atom) (present : occurrence ∈ node.label)
    (edge : Nat) (target : Stlsat.Formula Atom)
    (shape : occurrence.postponedTarget? = some (edge, target))
    (leaf : SemanticOccurrence Atom) (leafMem : leaf ∈ semanticOccurrences target) :
    ((SupportedWindowOccurrence.ofSemantic (occurrence.id ++ [edge]) leaf).shift node.time) ∈
      node.supportedTargetWindows := by
  classical
  unfold supportedTargetWindows
  apply List.mem_flatMap.mpr
  refine ⟨occurrence, Finset.mem_toList.mpr present, ?_⟩
  rw [shape]
  apply List.mem_map.mpr
  exact ⟨SupportedWindowOccurrence.ofSemantic (occurrence.id ++ [edge]) leaf,
    List.mem_map.mpr ⟨leaf, leafMem, rfl⟩, rfl⟩

omit [DecidableEq Atom] in
theorem supportedIndependentWindow_mem (node : Node Atom)
    (occurrence : AnnotatedOccurrence Atom) (present : occurrence ∈ node.label)
    (temporal : occurrence.isTemporal = true)
    (notParentActive : ¬node.ParentActive occurrence)
    (leaf : SemanticOccurrence Atom) (leafMem : leaf ∈ semanticOccurrences occurrence.formula) :
    SupportedWindowOccurrence.ofSemantic occurrence.id leaf ∈
      node.supportedIndependentWindows := by
  classical
  unfold supportedIndependentWindows
  apply List.mem_flatMap.mpr
  refine ⟨occurrence, Finset.mem_toList.mpr present, ?_⟩
  simp only [temporal, notParentActive, not_false_eq_true, and_self, if_true]
  exact List.mem_map.mpr ⟨leaf, leafMem, rfl⟩

omit [DecidableEq Atom] in
theorem supportedPositiveAtomicWindow_mem (node : Node Atom)
    (occurrence : AnnotatedOccurrence Atom) (present : occurrence ∈ node.label)
    (notParentActive : ¬node.ParentActive occurrence) (atom : Atom)
    (shape : occurrence.payload = .unmarked (.atom atom)) :
    { id := occurrence.id, window := ⟨node.time, node.time, le_rfl⟩,
      leaf := .positive atom } ∈ node.supportedAtomicConflictWindows := by
  classical
  unfold supportedAtomicConflictWindows
  apply List.mem_flatMap.mpr
  refine ⟨occurrence, Finset.mem_toList.mpr present, ?_⟩
  simp [notParentActive, shape]

omit [DecidableEq Atom] in
theorem supportedNegativeAtomicWindow_mem (node : Node Atom)
    (occurrence : AnnotatedOccurrence Atom) (present : occurrence ∈ node.label)
    (notParentActive : ¬node.ParentActive occurrence) (atom : Atom)
    (shape : occurrence.payload = .unmarked (.neg (.atom atom))) :
    { id := occurrence.id ++ [0], window := ⟨node.time, node.time, le_rfl⟩,
      leaf := .negative atom } ∈ node.supportedAtomicConflictWindows := by
  classical
  unfold supportedAtomicConflictWindows
  apply List.mem_flatMap.mpr
  refine ⟨occurrence, Finset.mem_toList.mpr present, ?_⟩
  simp [notParentActive, shape]

/-- Two supported windows are semantically independent when their variable
supports are disjoint. -/
def SupportDisjoint {Var : Type w} (atomSupport : Atom → Finset Var)
    (left right : SupportedWindowOccurrence Atom) : Prop :=
  Disjoint (left.leaf.support atomSupport) (right.leaf.support atomSupport)

/-- A pair which the variable-aware checker must still separate. -/
def VariableConflict {Var : Type w} (atomSupport : Atom → Finset Var)
    (left right : SupportedWindowOccurrence Atom) : Prop :=
  left.id ≠ right.id ∧ ¬SupportDisjoint atomSupport left right

def SupportedWindowsOverlap (left right : SupportedWindowOccurrence Atom) : Prop :=
  left.window.lower ≤ right.window.upper ∧ right.window.lower ≤ left.window.upper

/-- Variable-aware soundness guard.

This does not test whether overlapping constraints happen to be pairwise
satisfiable.  Instead it ensures that simultaneous requirements with
different canonical identities have disjoint support; canonicality handles
equal identities, and `AtomicSupport.amalgamate` handles the whole family. -/
def VariableSoundSafe {Var : Type w} (node : Node Atom)
    (atomSupport : Atom → Finset Var) : Prop :=
  ∀ invariant ∈ node.supportedInvariantWindows,
    ∀ other ∈ node.supportedIndependentWindows,
      VariableConflict atomSupport invariant other →
        ¬SupportedWindowsOverlap invariant other

/-- Variable-aware completeness guard. -/
def VariableCompleteSafe {Var : Type w} (node : Node Atom)
    (atomSupport : Atom → Finset Var) : Prop :=
  ∀ target ∈ node.supportedTargetWindows,
    ∀ conflict ∈ node.supportedConflictWindows,
      VariableConflict atomSupport target conflict →
        ¬SupportedWindowsOverlap target conflict

/-- The paper's variable-aware soundness limit.  Only ordered `N(u)`/`O(u)`
pairs whose signed leaves have overlapping variable support contribute a
finite gap; `none` denotes `+∞`. -/
noncomputable def variableSoundLimit? {Var : Type w}
    (node : Node Atom) (atomSupport : Atom → Finset Var) : Option Nat := by
  classical
  exact minimum? (node.supportedInvariantWindows.flatMap fun invariant ↦
    node.supportedIndependentWindows.filterMap fun other ↦
      if VariableConflict atomSupport invariant other ∧
          invariant.window.upper < other.window.lower then
        some (other.window.lower - invariant.window.upper)
      else none)

/-- The optimized jump size `k⁺(u)`: the temporal-bounds limit combined
with the support-filtered soundness limit.  It can be strictly larger than
the conservative `jumpSize?`. -/
noncomputable def variableJumpSize? {Var : Type w}
    (node : Node Atom) (atomSupport : Atom → Finset Var) : Option Nat :=
  match node.boundsLimit? with
  | none => none
  | some bounds => minLimit (some bounds) (node.variableSoundLimit? atomSupport)

omit [DecidableEq Atom] in
/-- A variable-aware jump cannot pass a future member of `K(u)`. -/
theorem variableJumpSize_le_future_boundCandidate {Var : Type w}
    (node : Node Atom) (atomSupport : Atom → Finset Var) {size bound : Nat}
    (computed : node.variableJumpSize? atomSupport = some size)
    (candidate : bound ∈ node.boundCandidates) (future : node.time < bound) :
    node.time + size ≤ bound := by
  classical
  unfold variableJumpSize? at computed
  cases boundsComputed : node.boundsLimit? with
  | none => simp [boundsComputed] at computed
  | some bounds =>
      have sizeLeBounds : size ≤ bounds :=
        minLimit_some_left_le (by simpa [boundsComputed] using computed)
      have distancePresent : bound - node.time ∈
          (node.boundCandidates.filter (node.time < ·)).map (· - node.time) := by
        apply List.mem_map.mpr
        exact ⟨bound, by simp [candidate, future], rfl⟩
      have boundsLeDistance : bounds ≤ bound - node.time := by
        apply minimum?_le_of_mem (value := bound - node.time)
        · simpa [boundsLimit?] using boundsComputed
        · exact distancePresent
      omega

omit [DecidableEq Atom] in
/-- Every computed variable-aware JUMP advances time. -/
theorem variableJumpSize_pos {Var : Type w}
    (node : Node Atom) (atomSupport : Atom → Finset Var) {size : Nat}
    (computed : node.variableJumpSize? atomSupport = some size) : 0 < size := by
  classical
  have boundsPositive : ∀ value, node.boundsLimit? = some value → 0 < value := by
    intro value valueComputed
    apply minimum?_positive_of_all_positive (by simpa [boundsLimit?] using valueComputed)
    intro distance present
    rcases List.mem_map.mp present with ⟨bound, boundPresent, rfl⟩
    have future : node.time < bound := by
      simpa using (List.mem_filter.mp boundPresent).2
    omega
  have soundPositive : ∀ value,
      node.variableSoundLimit? atomSupport = some value → 0 < value := by
    intro value valueComputed
    apply minimum?_positive_of_all_positive
      (by simpa [variableSoundLimit?] using valueComputed)
    intro distance present
    rcases List.mem_flatMap.mp present with ⟨invariant, _, present⟩
    rcases List.mem_filterMap.mp present with ⟨other, _, selected⟩
    split at selected <;> simp_all
    omega
  unfold variableJumpSize? at computed
  cases boundsComputed : node.boundsLimit? with
  | none => simp [boundsComputed] at computed
  | some bounds =>
      apply minLimit_positive
        (left := some bounds) (right := node.variableSoundLimit? atomSupport)
        (fun value equal ↦ by
          simp only [Option.some.injEq] at equal
          subst value
          exact boundsPositive bounds boundsComputed)
        soundPositive
        (by simpa [boundsComputed] using computed)

omit [DecidableEq Atom] in
/-- Every variable-aware computed size satisfies the common temporal-bounds
contract used by the semantic JUMP lemmas. -/
theorem variableJumpSizeAdmissible {Var : Type w}
    (node : Node Atom) (atomSupport : Atom → Finset Var) {size : Nat}
    (computed : node.variableJumpSize? atomSupport = some size) :
    node.JumpSizeAdmissible size :=
  ⟨node.variableJumpSize_pos atomSupport computed,
    fun bound candidate future ↦
      node.variableJumpSize_le_future_boundCandidate atomSupport (bound := bound) computed
        candidate future⟩

omit [DecidableEq Atom] in
/-- The optimized size is bounded by its finite support-filtered soundness
limit. -/
theorem variableJumpSize_le_soundLimit {Var : Type w}
    (node : Node Atom) (atomSupport : Atom → Finset Var) {size limit : Nat}
    (computed : node.variableJumpSize? atomSupport = some size)
    (soundComputed : node.variableSoundLimit? atomSupport = some limit) :
    size ≤ limit := by
  classical
  unfold variableJumpSize? at computed
  cases boundsComputed : node.boundsLimit? with
  | none => simp [boundsComputed] at computed
  | some bounds =>
      simp [boundsComputed, soundComputed, minLimit] at computed
      omega

omit [DecidableEq Atom] in
/-- Every ordered, support-conflicting `N(u)`/`O(u)` pair bounds the optimized
jump. -/
theorem variableJumpSize_le_soundGap {Var : Type w}
    (node : Node Atom) (atomSupport : Atom → Finset Var) {size : Nat}
    (computed : node.variableJumpSize? atomSupport = some size)
    (invariant other : SupportedWindowOccurrence Atom)
    (invariantMem : invariant ∈ node.supportedInvariantWindows)
    (otherMem : other ∈ node.supportedIndependentWindows)
    (conflict : VariableConflict atomSupport invariant other)
    (ordered : invariant.window.upper < other.window.lower) :
    size ≤ other.window.lower - invariant.window.upper := by
  classical
  let gap := other.window.lower - invariant.window.upper
  have gapMem : gap ∈ node.supportedInvariantWindows.flatMap fun invariant ↦
      node.supportedIndependentWindows.filterMap fun other ↦
        if VariableConflict atomSupport invariant other ∧
            invariant.window.upper < other.window.lower then
          some (other.window.lower - invariant.window.upper)
        else none := by
    apply List.mem_flatMap.mpr
    refine ⟨invariant, invariantMem, ?_⟩
    apply List.mem_filterMap.mpr
    exact ⟨other, otherMem, by simp [gap, conflict, ordered]⟩
  cases soundComputed : node.variableSoundLimit? atomSupport with
  | none =>
      have empty := (minimum?_eq_none_iff _).mp (by
        simpa [variableSoundLimit?] using soundComputed)
      rw [empty] at gapMem
      simp at gapMem
  | some limit =>
      exact (node.variableJumpSize_le_soundLimit atomSupport computed soundComputed).trans
        (minimum?_le_of_mem
          (by simpa [variableSoundLimit?] using soundComputed) gapMem)

omit [DecidableEq Atom] in
/-- Every optimized sound-gap candidate is also a conservative candidate.
Consequently, whenever the optimized sound limit is finite, the conservative
sound limit is no larger. -/
theorem soundLimit_le_variableSoundLimit {Var : Type w}
    (node : Node Atom) (atomSupport : Atom → Finset Var) {variableLimit : Nat}
    (variableComputed : node.variableSoundLimit? atomSupport = some variableLimit) :
    ∃ conservativeLimit,
      node.soundLimit? = some conservativeLimit ∧ conservativeLimit ≤ variableLimit := by
  classical
  have variableMem : variableLimit ∈
      node.supportedInvariantWindows.flatMap fun invariant ↦
        node.supportedIndependentWindows.filterMap fun other ↦
          if VariableConflict atomSupport invariant other ∧
              invariant.window.upper < other.window.lower then
            some (other.window.lower - invariant.window.upper)
          else none :=
    minimum?_mem (by simpa [variableSoundLimit?] using variableComputed)
  rcases List.mem_flatMap.mp variableMem with ⟨invariant, invariantMem, variableMem⟩
  rcases List.mem_filterMap.mp variableMem with ⟨other, otherMem, selected⟩
  by_cases eligible : VariableConflict atomSupport invariant other ∧
      invariant.window.upper < other.window.lower
  · have gapEq : other.window.lower - invariant.window.upper = variableLimit := by
      simpa [eligible] using selected
    have conservativeMem : variableLimit ∈
        node.invariantWindows.flatMap fun invariant ↦
          node.independentWindows.filterMap fun other ↦
            if invariant.id ≠ other.id ∧ invariant.window.upper < other.window.lower then
              some (other.window.lower - invariant.window.upper)
            else none := by
      apply List.mem_flatMap.mpr
      refine ⟨invariant.erase, node.erase_mem_invariantWindows invariantMem, ?_⟩
      apply List.mem_filterMap.mpr
      refine ⟨other.erase, node.erase_mem_independentWindows otherMem, ?_⟩
      simp [SupportedWindowOccurrence.erase, eligible.1.1, eligible.2, gapEq]
    cases conservativeComputed : node.soundLimit? with
    | none =>
        have empty := (minimum?_eq_none_iff _).mp (by
          simpa [soundLimit?] using conservativeComputed)
        rw [empty] at conservativeMem
        simp at conservativeMem
    | some conservativeLimit =>
        exact ⟨conservativeLimit, rfl,
          minimum?_le_of_mem
            (by simpa [soundLimit?] using conservativeComputed) conservativeMem⟩
  · simp [eligible] at selected

omit [DecidableEq Atom] in
/-- Filtering the soundness gaps by variable support never shortens a finite
JUMP.  The inequality can be strict when the conservative minimum comes from
a support-disjoint pair. -/
theorem jumpSize_le_variableJumpSize {Var : Type w}
    (node : Node Atom) (atomSupport : Atom → Finset Var)
    {conservativeSize variableSize : Nat}
    (conservativeComputed : node.jumpSize? = some conservativeSize)
    (variableComputed : node.variableJumpSize? atomSupport = some variableSize) :
    conservativeSize ≤ variableSize := by
  classical
  unfold jumpSize? at conservativeComputed
  unfold variableJumpSize? at variableComputed
  cases boundsComputed : node.boundsLimit? with
  | none => simp [boundsComputed] at conservativeComputed
  | some bounds =>
      cases conservativeSound : node.soundLimit? with
      | none =>
          cases variableSound : node.variableSoundLimit? atomSupport with
          | none =>
              simp [boundsComputed, conservativeSound, variableSound, minLimit] at *
              omega
          | some variableLimit =>
              rcases node.soundLimit_le_variableSoundLimit atomSupport variableSound with
                ⟨conservativeLimit, conservativeFinite, _⟩
              rw [conservativeSound] at conservativeFinite
              simp at conservativeFinite
      | some conservativeLimit =>
          cases variableSound : node.variableSoundLimit? atomSupport with
          | none =>
              simp [boundsComputed, conservativeSound, variableSound, minLimit] at *
              omega
          | some variableLimit =>
              rcases node.soundLimit_le_variableSoundLimit atomSupport variableSound with
                ⟨actualConservative, actualComputed, limitLe⟩
              rw [conservativeSound] at actualComputed
              simp only [Option.some.injEq] at actualComputed
              subst actualConservative
              simp [boundsComputed, conservativeSound, variableSound, minLimit] at *
              omega

omit [DecidableEq Atom] in
/-- A finite conservative jump implies that the variable-aware calculation
also has a finite (possibly larger) result, because both use the same finite
`K(u)` limit. -/
theorem exists_variableJumpSize_of_jumpSize {Var : Type w}
    (node : Node Atom) (atomSupport : Atom → Finset Var) {size : Nat}
    (computed : node.jumpSize? = some size) :
    ∃ variableSize, node.variableJumpSize? atomSupport = some variableSize := by
  classical
  have finiteBounds : ∃ bounds, node.boundsLimit? = some bounds := by
    unfold jumpSize? at computed
    cases boundsComputed : node.boundsLimit? with
    | none => simp [boundsComputed] at computed
    | some bounds => exact ⟨bounds, rfl⟩
  rcases finiteBounds with ⟨bounds, boundsComputed⟩
  cases soundComputed : node.variableSoundLimit? atomSupport with
  | none =>
      exact ⟨bounds, by simp [variableJumpSize?, boundsComputed, soundComputed, minLimit]⟩
  | some sound =>
      exact ⟨min bounds sound,
        by simp [variableJumpSize?, boundsComputed, soundComputed, minLimit]⟩

omit [DecidableEq Atom] in
/-- A strictly skipped copy of an invariant window cannot overlap a distinct
support-dependent independent window. -/
theorem shiftedSupportedInvariant_safe {Var : Type w} (node : Node Atom)
    (atomSupport : Atom → Finset Var) {size offset : Nat}
    (computed : node.variableJumpSize? atomSupport = some size)
    (sound : node.VariableSoundSafe atomSupport) (strictlySkipped : offset < size)
    (invariant other : SupportedWindowOccurrence Atom)
    (invariantMem : invariant ∈ node.supportedInvariantWindows)
    (otherMem : other ∈ node.supportedIndependentWindows)
    (conflict : VariableConflict atomSupport invariant other) :
    ¬SupportedWindowsOverlap (invariant.shift offset) other := by
  have initiallyDisjoint := sound invariant invariantMem other otherMem conflict
  have separated : invariant.window.upper < other.window.lower ∨
      other.window.upper < invariant.window.lower := by
    by_contra notSeparated
    apply initiallyDisjoint
    exact ⟨by omega, by omega⟩
  rcases separated with invariantBefore | otherBefore
  · have bounded := node.variableJumpSize_le_soundGap atomSupport computed invariant other
      invariantMem otherMem conflict invariantBefore
    intro overlap
    rcases overlap with ⟨left, right⟩
    simp only [SupportedWindowOccurrence.shift, Stlsat.Interval.shift] at left right
    omega
  · intro overlap
    rcases overlap with ⟨left, right⟩
    simp only [SupportedWindowOccurrence.shift, Stlsat.Interval.shift] at left right
    omega

omit [DecidableEq Atom] in
/-- The variable-aware soundness guard is a relaxation of the conservative
guard. -/
theorem variableSoundSafe_of_soundSafe {Var : Type w} (node : Node Atom)
    (atomSupport : Atom → Finset Var) (sound : node.SoundSafe) :
    node.VariableSoundSafe atomSupport := by
  intro invariant invariantMem other otherMem conflict overlap
  have erased := sound invariant.erase (node.erase_mem_invariantWindows invariantMem)
    other.erase (node.erase_mem_independentWindows otherMem) conflict.1
  exact erased overlap

omit [DecidableEq Atom] in
/-- The variable-aware completeness guard is a relaxation of the conservative
guard. -/
theorem variableCompleteSafe_of_completeSafe {Var : Type w} (node : Node Atom)
    (atomSupport : Atom → Finset Var) (complete : node.CompleteSafe) :
    node.VariableCompleteSafe atomSupport := by
  intro target targetMem conflict conflictMem variableConflict overlap
  have erased := complete target.erase (node.erase_mem_targetWindows targetMem)
    conflict.erase (node.erase_mem_conflictWindows conflictMem) variableConflict.1
  exact erased overlap

/-- Enabling condition for the variable-aware JUMP configuration. -/
noncomputable def CanVariableJump {Var : Type w} (node : Node Atom)
    (atomSupport : Atom → Finset Var) : Prop :=
  node.VariableSoundSafe atomSupport ∧ node.VariableCompleteSafe atomSupport ∧
    ∃ size, node.variableJumpSize? atomSupport = some size

omit [DecidableEq Atom] in
/-- Every conservative JUMP is admitted by the variable-aware checker. -/
theorem canVariableJump_of_canJump {Var : Type w} (node : Node Atom)
    (atomSupport : Atom → Finset Var) (canJump : node.CanJump) :
    node.CanVariableJump atomSupport :=
  ⟨node.variableSoundSafe_of_soundSafe atomSupport canJump.1,
    node.variableCompleteSafe_of_completeSafe atomSupport canJump.2.1,
    let ⟨_size, computed⟩ := canJump.2.2
    node.exists_variableJumpSize_of_jumpSize atomSupport computed⟩

end Node

/- The variable-aware JUMP rule configuration over the shared tableau core. -/
namespace VariableJump

inductive Rule {Atom : Type u} {Var : Type w} [DecidableEq Atom]
    (semantics : Stlsat.AtomicSemantics Atom) (atomSupport : Atom → Finset Var)
    (node : Node Atom) : List (Node Atom) → Prop where
  | expand {children : List (Node Atom)} (notRejected : ¬node.Rejected semantics)
      (expansion : Expansion node children) : Rule semantics atomSupport node children
  | step (notRejected : ¬node.Rejected semantics) (poised : node.Poised)
      (hasTemporal : node.ContainsTemporal)
      (jumpDisabled : ¬node.CanVariableJump atomSupport) :
      Rule semantics atomSupport node [node.step]
  | jump (notRejected : ¬node.Rejected semantics) (poised : node.Poised)
      (hasTemporal : node.ContainsTemporal)
      (sound : node.VariableSoundSafe atomSupport)
      (complete : node.VariableCompleteSafe atomSupport)
      (size : Nat) (computed : node.variableJumpSize? atomSupport = some size) :
      Rule semantics atomSupport node [node.jump size]

def TreeWellFormed {Atom : Type u} {Var : Type w} [DecidableEq Atom]
    (semantics : Stlsat.AtomicSemantics Atom) (atomSupport : Atom → Finset Var) :
    TableauTree Atom → Prop :=
  TableauTree.WellFormedWith (Rule semantics atomSupport)

abbrev Development {Atom : Type u} {Var : Type w} [DecidableEq Atom]
    (semantics : Stlsat.AtomicSemantics Atom) (atomSupport : Atom → Finset Var)
    (formula : Stlsat.Formula Atom) :=
  Stlsat.Tableau.Development semantics formula (Rule semantics atomSupport)

end VariableJump

end Stlsat.Tableau
