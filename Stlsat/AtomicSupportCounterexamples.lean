/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.AtomicSupport
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Limits of variable-support conflict optimization

These small regression theorems record why the optimized tableau carries the
global `AtomicSupport.amalgamate` hypothesis.  Neither a user-supplied
syntactic support for arbitrary semantics nor pairwise satisfiability of
overlapping-support constraints is sufficient by itself.
-/

namespace Stlsat.Tableau.AtomicSupportCounterexamples

/-! ## Arbitrary semantics need not respect declared support -/

inductive CoupledAtom where
  | left | right
deriving DecidableEq

inductive CoupledVar where
  | left | right
deriving DecidableEq

/-- Both syntactically distinct atoms inspect the same hidden Boolean state. -/
def coupledSemantics : Stlsat.AtomicSemantics CoupledAtom where
  Valuation := Bool
  nonempty := inferInstance
  holds valuation _ := valuation = true

def coupledSupport : CoupledAtom → Finset CoupledVar
  | .left => {.left}
  | .right => {.right}

/-- Declaring disjoint supports does not make requirements independent for an
arbitrary `AtomicSemantics`: positive `left` and negative `right` are
separately satisfiable but cannot be amalgamated. -/
theorem arbitrary_semantics_disjoint_support_counterexample :
    Disjoint (coupledSupport .left) (coupledSupport .right) ∧
      FormulaValidity.SignedLeaf.Holds coupledSemantics true (.positive .left) ∧
      FormulaValidity.SignedLeaf.Holds coupledSemantics false (.negative .right) ∧
      ¬∃ valuation,
        FormulaValidity.SignedLeaf.Holds coupledSemantics valuation (.positive .left) ∧
        FormulaValidity.SignedLeaf.Holds coupledSemantics valuation (.negative .right) := by
  simp [coupledSupport, coupledSemantics, FormulaValidity.SignedLeaf.Holds]

/-- Consequently no valid `AtomicSupport` can certify the dishonest support
annotation above. -/
theorem no_atomicSupport_for_coupledSemantics :
    ¬∃ support : AtomicSupport coupledSemantics CoupledVar,
      support.atomSupport = coupledSupport := by
  rintro ⟨support, supportEq⟩
  let leaf : Bool → FormulaValidity.SignedLeaf CoupledAtom
    | false => .positive .left
    | true => .negative .right
  let valuation : Bool → coupledSemantics.Valuation
    | false => true
    | true => false
  have holds : ∀ index, (leaf index).Holds coupledSemantics (valuation index) := by
    intro index
    cases index <;>
      simp [leaf, valuation, coupledSemantics, FormulaValidity.SignedLeaf.Holds]
  have compatible : ∀ left right,
      valuation left = valuation right ∨ leaf left = leaf right ∨
        Disjoint ((leaf left).support support.atomSupport)
          ((leaf right).support support.atomSupport) := by
    intro left right
    cases left <;> cases right
    · exact Or.inl rfl
    · right
      right
      rw [supportEq]
      simp [leaf, coupledSupport, FormulaValidity.SignedLeaf.support]
    · right
      right
      rw [supportEq]
      simp [leaf, coupledSupport, FormulaValidity.SignedLeaf.support]
    · exact Or.inl rfl
  rcases support.amalgamate leaf valuation holds compatible with
    ⟨combined, combinedHolds⟩
  have positive : combined = true := by
    simpa [leaf, coupledSemantics, FormulaValidity.SignedLeaf.Holds] using
      combinedHolds false
  have negative : ¬combined = true := by
    simpa [leaf, coupledSemantics, FormulaValidity.SignedLeaf.Holds] using
      combinedHolds true
  exact negative positive

/-! ## Pairwise compatibility is not global compatibility -/

inductive PairBoolVar where
  | x | y
deriving DecidableEq

inductive BoolConstraint where
  | xTrue | yTrue | notBoth
deriving DecidableEq

def boolConstraintHolds
    (valuation : PairBoolVar → Bool) : BoolConstraint → Prop
  | .xTrue => valuation .x = true
  | .yTrue => valuation .y = true
  | .notBoth => ¬(valuation .x = true ∧ valuation .y = true)

def boolConstraintSupport : BoolConstraint → Finset PairBoolVar
  | .xTrue => {.x}
  | .yTrue => {.y}
  | .notBoth => {.x, .y}

def boolConstraintTheory :
    FunctionalAtomicTheory BoolConstraint PairBoolVar Bool where
  holds := boolConstraintHolds
  atomSupport := boolConstraintSupport
  locality := by
    intro atom left right agree
    cases atom
    · simp only [boolConstraintHolds]
      rw [agree .x (by simp [boolConstraintSupport])]
    · simp only [boolConstraintHolds]
      rw [agree .y (by simp [boolConstraintSupport])]
    · have x := agree .x (by simp [boolConstraintSupport])
      have y := agree .y (by simp [boolConstraintSupport])
      simp only [boolConstraintHolds]
      rw [x, y]

/-- Three Boolean constraints can have every pair satisfiable while the full
family is inconsistent.  Thus a checker that merely asks whether each
overlapping-support pair has some common valuation is unsound. -/
theorem boolean_pairwise_not_global :
    (∃ valuation, boolConstraintHolds valuation .xTrue ∧
      boolConstraintHolds valuation .yTrue) ∧
    (∃ valuation, boolConstraintHolds valuation .xTrue ∧
      boolConstraintHolds valuation .notBoth) ∧
    (∃ valuation, boolConstraintHolds valuation .yTrue ∧
      boolConstraintHolds valuation .notBoth) ∧
    ¬∃ valuation, boolConstraintHolds valuation .xTrue ∧
      boolConstraintHolds valuation .yTrue ∧
      boolConstraintHolds valuation .notBoth := by
  refine ⟨⟨fun _ ↦ true, rfl, rfl⟩, ?_, ?_, ?_⟩
  · refine ⟨fun coordinate ↦ coordinate = .x, rfl, ?_⟩
    simp [boolConstraintHolds]
  · refine ⟨fun coordinate ↦ coordinate = .y, rfl, ?_⟩
    simp [boolConstraintHolds]
  · rintro ⟨valuation, xTrue, yTrue, notBoth⟩
    exact notBoth ⟨xTrue, yTrue⟩

/-! ## Linear real arithmetic has the same pairwise obstruction -/

noncomputable def lraXNonnegative : LRAAtom Bool where
  coefficients := Finsupp.single false (-1)
  bound := 0

noncomputable def lraYNonnegative : LRAAtom Bool where
  coefficients := Finsupp.single true (-1)
  bound := 0

noncomputable def lraNegativeSum : LRAAtom Bool where
  coefficients := Finsupp.single false 1 + Finsupp.single true 1
  bound := -1

theorem evaluate_lraXNonnegative (valuation : Bool → ℝ) :
    lraXNonnegative.evaluate valuation = -valuation false := by
  classical
  unfold lraXNonnegative LRAAtom.evaluate
  rw [Finsupp.sum_single_index (by simp)]
  simp

theorem evaluate_lraYNonnegative (valuation : Bool → ℝ) :
    lraYNonnegative.evaluate valuation = -valuation true := by
  classical
  unfold lraYNonnegative LRAAtom.evaluate
  rw [Finsupp.sum_single_index (by simp)]
  simp

theorem evaluate_lraNegativeSum (valuation : Bool → ℝ) :
    lraNegativeSum.evaluate valuation = valuation false + valuation true := by
  classical
  unfold lraNegativeSum LRAAtom.evaluate
  rw [Finsupp.sum_add_index' (by simp) (by simp [add_mul])]
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  simp

@[simp] theorem holds_lraXNonnegative (valuation : Bool → ℝ) :
    (LRASemantics Bool).holds valuation lraXNonnegative ↔
      0 ≤ valuation false := by
  change lraXNonnegative.evaluate valuation ≤ 0 ↔ _
  rw [evaluate_lraXNonnegative]
  constructor <;> intro hypothesis <;> linarith

@[simp] theorem holds_lraYNonnegative (valuation : Bool → ℝ) :
    (LRASemantics Bool).holds valuation lraYNonnegative ↔
      0 ≤ valuation true := by
  change lraYNonnegative.evaluate valuation ≤ 0 ↔ _
  rw [evaluate_lraYNonnegative]
  constructor <;> intro hypothesis <;> linarith

@[simp] theorem holds_lraNegativeSum (valuation : Bool → ℝ) :
    (LRASemantics Bool).holds valuation lraNegativeSum ↔
      valuation false + valuation true ≤ -1 := by
  change lraNegativeSum.evaluate valuation ≤ -1 ↔ _
  rw [evaluate_lraNegativeSum]

/-- `x ≥ 0`, `y ≥ 0`, and `x+y ≤ -1` are pairwise feasible but
jointly infeasible. -/
theorem lra_pairwise_not_global :
    (∃ valuation, (LRASemantics Bool).holds valuation lraXNonnegative ∧
      (LRASemantics Bool).holds valuation lraYNonnegative) ∧
    (∃ valuation, (LRASemantics Bool).holds valuation lraXNonnegative ∧
      (LRASemantics Bool).holds valuation lraNegativeSum) ∧
    (∃ valuation, (LRASemantics Bool).holds valuation lraYNonnegative ∧
      (LRASemantics Bool).holds valuation lraNegativeSum) ∧
    ¬∃ valuation, (LRASemantics Bool).holds valuation lraXNonnegative ∧
      (LRASemantics Bool).holds valuation lraYNonnegative ∧
      (LRASemantics Bool).holds valuation lraNegativeSum := by
  constructor
  · refine ⟨fun _ ↦ 0, ?_, ?_⟩
    · change lraXNonnegative.evaluate (fun _ ↦ 0) ≤ 0
      rw [evaluate_lraXNonnegative]
      norm_num
    · change lraYNonnegative.evaluate (fun _ ↦ 0) ≤ 0
      rw [evaluate_lraYNonnegative]
      norm_num
  constructor
  · let valuation : Bool → ℝ := fun coordinate ↦ if coordinate then -1 else 0
    refine ⟨valuation, ?_, ?_⟩
    · change lraXNonnegative.evaluate valuation ≤ 0
      rw [evaluate_lraXNonnegative]
      simp [valuation]
    · change lraNegativeSum.evaluate valuation ≤ -1
      rw [evaluate_lraNegativeSum]
      norm_num [valuation]
  constructor
  · let valuation : Bool → ℝ := fun coordinate ↦ if coordinate then 0 else -1
    refine ⟨valuation, ?_, ?_⟩
    · change lraYNonnegative.evaluate valuation ≤ 0
      rw [evaluate_lraYNonnegative]
      simp [valuation]
    · change lraNegativeSum.evaluate valuation ≤ -1
      rw [evaluate_lraNegativeSum]
      norm_num [valuation]
  · rintro ⟨valuation, xNonnegative, yNonnegative, negativeSum⟩
    change lraXNonnegative.evaluate (fun coordinate ↦ valuation coordinate) ≤ 0 at xNonnegative
    change lraYNonnegative.evaluate (fun coordinate ↦ valuation coordinate) ≤ 0 at yNonnegative
    change lraNegativeSum.evaluate (fun coordinate ↦ valuation coordinate) ≤ -1 at negativeSum
    rw [evaluate_lraXNonnegative] at xNonnegative
    rw [evaluate_lraYNonnegative] at yNonnegative
    rw [evaluate_lraNegativeSum] at negativeSum
    linarith

end Stlsat.Tableau.AtomicSupportCounterexamples
