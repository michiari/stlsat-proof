/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.Variable.Support
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Real.Basic

/-!
# Coordinate-local atomic semantics

This module supplies the principal models of the variable-support
amalgamation interface.  A functional atomic theory interprets valuations as
functions on variables and requires atomic truth to be local to a finite
support.  From locality alone we prove the global amalgamation property used
by the variable-aware JUMP rule.
-/

namespace Stlsat.Tableau

universe u v w

/-- Atomic semantics whose valuations are coordinate functions. -/
structure FunctionalAtomicTheory (Atom : Type u) (Var : Type w) (Value : Type v)
    [DecidableEq Var] [Nonempty Value] where
  holds : (Var → Value) → Atom → Prop
  atomSupport : Atom → Finset Var
  locality : ∀ atom left right,
    (∀ coordinate ∈ atomSupport atom, left coordinate = right coordinate) →
      (holds left atom ↔ holds right atom)

namespace FunctionalAtomicTheory

variable {Atom : Type u} {Var : Type w} {Value : Type v}
  [DecidableEq Var] [Nonempty Value]

def semantics (theory : FunctionalAtomicTheory Atom Var Value) :
    Stlsat.AtomicSemantics Atom where
  Valuation := Var → Value
  nonempty := inferInstance
  holds := theory.holds

private theorem signed_local (theory : FunctionalAtomicTheory Atom Var Value)
    (leaf : FormulaValidity.SignedLeaf Atom) (left right : Var → Value)
    (agree : ∀ coordinate ∈ leaf.support theory.atomSupport,
      left coordinate = right coordinate) :
    leaf.Holds theory.semantics left ↔ leaf.Holds theory.semantics right := by
  cases leaf with
  | truth => simp [FormulaValidity.SignedLeaf.Holds]
  | falsity => simp [FormulaValidity.SignedLeaf.Holds]
  | positive atom =>
      exact theory.locality atom left right (by simpa using agree)
  | negative atom =>
      change (¬theory.holds left atom) ↔ ¬theory.holds right atom
      exact not_congr (theory.locality atom left right (by simpa using agree))

/-- Coordinate locality implies the global amalgamation property.  The proof
first chooses one source valuation for every distinct signed leaf.  At a
coordinate shared by two distinct leaves, the compatibility hypothesis forces
their representative valuations to be equal; coordinates belonging to
different leaves may therefore be combined consistently. -/
noncomputable def atomicSupport (theory : FunctionalAtomicTheory Atom Var Value) :
    AtomicSupport theory.semantics Var where
  atomSupport := theory.atomSupport
  amalgamate := by
    classical
    intro Index leaf valuation holds compatible
    let PresentLeaf :=
      { candidate : FormulaValidity.SignedLeaf Atom // ∃ index, leaf index = candidate }
    let representative (candidate : PresentLeaf) : Index :=
      Classical.choose candidate.2
    have representativeLeaf (candidate : PresentLeaf) :
        leaf (representative candidate) = candidate :=
      Classical.choose_spec candidate.2
    let hasVariable (coordinate : Var) : Prop :=
      ∃ candidate : PresentLeaf,
        coordinate ∈ candidate.1.support theory.atomSupport
    let selectedLeaf (coordinate : Var) (present : hasVariable coordinate) : PresentLeaf :=
      Classical.choose present
    let combined : Var → Value := fun coordinate ↦
      if present : hasVariable coordinate then
        valuation (representative (selectedLeaf coordinate present)) coordinate
      else Classical.choice inferInstance
    refine ⟨combined, ?_⟩
    intro index
    let current : PresentLeaf := ⟨leaf index, index, rfl⟩
    have representativeHolds :
        current.1.Holds theory.semantics (valuation (representative current)) := by
      rw [← representativeLeaf current]
      exact holds (representative current)
    apply (theory.signed_local current.1 (valuation (representative current)) combined ?_).mp
      representativeHolds
    intro coordinate coordinateMem
    have coordinatePresent : hasVariable coordinate := ⟨current, coordinateMem⟩
    simp only [combined, dif_pos coordinatePresent]
    let selected := selectedLeaf coordinate coordinatePresent
    have selectedMem : coordinate ∈ selected.1.support theory.atomSupport :=
      Classical.choose_spec coordinatePresent
    have notDisjoint : ¬Disjoint
        (selected.1.support theory.atomSupport) (current.1.support theory.atomSupport) := by
      exact Finset.not_disjoint_iff.mpr ⟨coordinate, selectedMem, coordinateMem⟩
    rcases compatible (representative selected) (representative current) with
      sameValuation | sameLeaf | disjoint
    · exact (congrFun sameValuation coordinate).symm
    · have selectedEq : selected.1 = current.1 := by
        rw [← representativeLeaf selected, ← representativeLeaf current]
        exact sameLeaf
      have subtypeEq : selectedLeaf coordinate coordinatePresent = current :=
        Subtype.ext selectedEq
      rw [subtypeEq]
    · apply False.elim
      apply notDisjoint
      simpa only [representativeLeaf selected, representativeLeaf current] using disjoint

end FunctionalAtomicTheory

/-! ## Boolean atoms -/

/-- Propositional atoms are individual Boolean variables. -/
def booleanTheory (Var : Type w) [DecidableEq Var] :
    FunctionalAtomicTheory Var Var Bool where
  holds valuation coordinate := valuation coordinate = true
  atomSupport coordinate := {coordinate}
  locality coordinate left right agree := by
    rw [agree coordinate (by simp)]

abbrev BooleanSemantics (Var : Type w) [DecidableEq Var] :=
  (booleanTheory Var).semantics

noncomputable def booleanAtomicSupport (Var : Type w) [DecidableEq Var] :
    AtomicSupport (BooleanSemantics Var) Var :=
  (booleanTheory Var).atomicSupport

/-! ## Linear real arithmetic atoms -/

/-- A (non-strict) linear real-arithmetic inequality
`sum coefficients·variables ≤ bound`.  Negated STL atoms provide the strict
opposite inequality. -/
structure LRAAtom (Var : Type w) where
  coefficients : Var →₀ ℝ
  bound : ℝ

noncomputable instance {Var : Type w} : DecidableEq (LRAAtom Var) := Classical.decEq _

namespace LRAAtom

variable {Var : Type w} [DecidableEq Var]

def evaluate (atom : LRAAtom Var) (valuation : Var → ℝ) : ℝ :=
  atom.coefficients.sum fun coordinate coefficient ↦ coefficient * valuation coordinate

omit [DecidableEq Var] in
theorem evaluate_eq_of_eq_on_support (atom : LRAAtom Var)
    {left right : Var → ℝ}
    (agree : ∀ coordinate ∈ atom.coefficients.support,
      left coordinate = right coordinate) :
    atom.evaluate left = atom.evaluate right := by
  apply Finsupp.sum_congr
  intro coordinate coordinateMem
  rw [agree coordinate coordinateMem]

end LRAAtom

def lraTheory (Var : Type w) [DecidableEq Var] :
    FunctionalAtomicTheory (LRAAtom Var) Var ℝ where
  holds valuation atom := atom.evaluate valuation ≤ atom.bound
  atomSupport atom := atom.coefficients.support
  locality atom left right agree := by
    rw [atom.evaluate_eq_of_eq_on_support agree]

abbrev LRASemantics (Var : Type w) [DecidableEq Var] :=
  (lraTheory Var).semantics

noncomputable def lraAtomicSupport (Var : Type w) [DecidableEq Var] :
    AtomicSupport (LRASemantics Var) Var :=
  (lraTheory Var).atomicSupport

end Stlsat.Tableau
