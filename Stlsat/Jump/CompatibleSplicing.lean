/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.Frontier

/-!
# Splicing models with compatible canonical leaves

Different canonical leaves are separated by the JUMP guards.  Instances of
the same canonical leaf may overlap, and must not be treated as disjoint: they
ask for the same signed literal.  This file proves the corresponding semantic
amalgamation lemma for strict-normal formulas.
-/

namespace Stlsat.Jump
universe u

namespace FormulaValidity

variable {Atom : Type u}

/-- The signed atomic test found at the end of a strict-normal formula path. -/
inductive SignedLeaf (Atom : Type u) where
  | truth
  | falsity
  | positive (atom : Atom)
  | negative (atom : Atom)
deriving DecidableEq

namespace SignedLeaf

def negate : SignedLeaf Atom → SignedLeaf Atom
  | .truth => .falsity
  | .falsity => .truth
  | .positive atom => .negative atom
  | .negative atom => .positive atom

def Holds (semantics : Stlsat.AtomicSemantics Atom)
    (valuation : semantics.Valuation) : SignedLeaf Atom → Prop
  | .truth => True
  | .falsity => False
  | .positive atom => semantics.holds valuation atom
  | .negative atom => ¬semantics.holds valuation atom

@[simp] theorem holds_negate {semantics : Stlsat.AtomicSemantics Atom}
    (valuation : semantics.Valuation) (leaf : SignedLeaf Atom) :
    (leaf.negate.Holds semantics valuation) ↔ ¬leaf.Holds semantics valuation := by
  cases leaf <;> simp [negate, Holds]

end SignedLeaf

/-- A validity occurrence together with the signed literal at its path. -/
structure SemanticOccurrence (Atom : Type u) where
  path : FormulaPath
  window : Stlsat.Interval
  leaf : SignedLeaf Atom
deriving DecidableEq

namespace SemanticOccurrence

def toValidity (occurrence : SemanticOccurrence Atom) : ValidityOccurrence where
  path := occurrence.path
  window := occurrence.window

def prefixPath (edge : Nat) (occurrence : SemanticOccurrence Atom) :
    SemanticOccurrence Atom where
  path := edge :: occurrence.path
  window := occurrence.window
  leaf := occurrence.leaf

def negate (occurrence : SemanticOccurrence Atom) : SemanticOccurrence Atom where
  path := occurrence.path
  window := occurrence.window
  leaf := occurrence.leaf.negate

def through (bounds : Stlsat.Interval) (occurrence : SemanticOccurrence Atom) :
    SemanticOccurrence Atom where
  path := occurrence.path
  window := {
    lower := occurrence.window.lower + bounds.lower
    upper := occurrence.window.upper + bounds.upper
    lower_le_upper := Nat.add_le_add occurrence.window.lower_le_upper bounds.lower_le_upper
  }
  leaf := occurrence.leaf

def beforeTarget (bounds : Stlsat.Interval) (nontrivial : bounds.lower < bounds.upper)
    (occurrence : SemanticOccurrence Atom) : SemanticOccurrence Atom where
  path := occurrence.path
  window := {
    lower := occurrence.window.lower + bounds.lower
    upper := occurrence.window.upper + (bounds.upper - 1)
    lower_le_upper := Nat.add_le_add occurrence.window.lower_le_upper (by omega)
  }
  leaf := occurrence.leaf

def shift (offset : Nat) (occurrence : SemanticOccurrence Atom) :
    SemanticOccurrence Atom where
  path := occurrence.path
  window := occurrence.window.shift offset
  leaf := occurrence.leaf

/-- Put the complete canonical root into the semantic path. -/
def reroot (root : OccurrenceId) (occurrence : SemanticOccurrence Atom) :
    SemanticOccurrence Atom where
  path := root ++ occurrence.path
  window := occurrence.window
  leaf := occurrence.leaf

end SemanticOccurrence

/-- Signed version of `validityOccurrences`. -/
def semanticOccurrences : Stlsat.Formula Atom → List (SemanticOccurrence Atom)
  | .truth => [{ path := [], window := ⟨0, 0, le_rfl⟩, leaf := .truth }]
  | .atom atom => [{ path := [], window := ⟨0, 0, le_rfl⟩, leaf := .positive atom }]
  | .neg body =>
      (semanticOccurrences body).map
        (fun occurrence => (occurrence.negate).prefixPath 0)
  | .and left right | .or left right =>
      (semanticOccurrences left).map (SemanticOccurrence.prefixPath 0) ++
        (semanticOccurrences right).map (SemanticOccurrence.prefixPath 1)
  | .eventually bounds body | .always bounds body =>
      (semanticOccurrences body).map
        (fun occurrence => (occurrence.through bounds).prefixPath 0)
  | .strictUntil bounds left right | .strictRelease bounds left right =>
      (if h : bounds.lower < bounds.upper then
        (semanticOccurrences left).map
          (fun occurrence => (occurrence.beforeTarget bounds h).prefixPath 0)
       else []) ++
        (semanticOccurrences right).map
          (fun occurrence => (occurrence.through bounds).prefixPath 1)

theorem toValidity_mem_validityOccurrences (formula : Stlsat.Formula Atom)
    (occurrence : SemanticOccurrence Atom)
    (present : occurrence ∈ semanticOccurrences formula) :
    occurrence.toValidity ∈ validityOccurrences formula := by
  induction formula generalizing occurrence with
  | truth =>
      simp only [semanticOccurrences, List.mem_singleton] at present
      subst occurrence
      simp [validityOccurrences, SemanticOccurrence.toValidity]
  | atom atom =>
      simp only [semanticOccurrences, List.mem_singleton] at present
      subst occurrence
      simp [validityOccurrences, SemanticOccurrence.toValidity]
  | neg body ih =>
      rcases List.mem_map.mp present with ⟨source, sourceMem, rfl⟩
      exact List.mem_map.mpr ⟨source.toValidity, ih source sourceMem, by
        simp [SemanticOccurrence.toValidity, SemanticOccurrence.negate,
          SemanticOccurrence.prefixPath, ValidityOccurrence.prefixPath]⟩
  | and left right ihLeft ihRight =>
      rcases List.mem_append.mp present with leftMem | rightMem
      · rcases List.mem_map.mp leftMem with ⟨source, sourceMem, rfl⟩
        exact List.mem_append.mpr (Or.inl (List.mem_map.mpr
          ⟨source.toValidity, ihLeft source sourceMem, by
            simp [SemanticOccurrence.toValidity, SemanticOccurrence.prefixPath,
              ValidityOccurrence.prefixPath]⟩))
      · rcases List.mem_map.mp rightMem with ⟨source, sourceMem, rfl⟩
        exact List.mem_append.mpr (Or.inr (List.mem_map.mpr
          ⟨source.toValidity, ihRight source sourceMem, by
            simp [SemanticOccurrence.toValidity, SemanticOccurrence.prefixPath,
              ValidityOccurrence.prefixPath]⟩))
  | or left right ihLeft ihRight =>
      rcases List.mem_append.mp present with leftMem | rightMem
      · rcases List.mem_map.mp leftMem with ⟨source, sourceMem, rfl⟩
        exact List.mem_append.mpr (Or.inl (List.mem_map.mpr
          ⟨source.toValidity, ihLeft source sourceMem, by
            simp [SemanticOccurrence.toValidity, SemanticOccurrence.prefixPath,
              ValidityOccurrence.prefixPath]⟩))
      · rcases List.mem_map.mp rightMem with ⟨source, sourceMem, rfl⟩
        exact List.mem_append.mpr (Or.inr (List.mem_map.mpr
          ⟨source.toValidity, ihRight source sourceMem, by
            simp [SemanticOccurrence.toValidity, SemanticOccurrence.prefixPath,
              ValidityOccurrence.prefixPath]⟩))
  | eventually interval body ih =>
      rcases List.mem_map.mp present with ⟨source, sourceMem, rfl⟩
      exact List.mem_map.mpr ⟨source.toValidity, ih source sourceMem, by
        simp [SemanticOccurrence.toValidity, SemanticOccurrence.prefixPath,
          SemanticOccurrence.through, ValidityOccurrence.prefixPath,
          ValidityOccurrence.through]⟩
  | always interval body ih =>
      rcases List.mem_map.mp present with ⟨source, sourceMem, rfl⟩
      exact List.mem_map.mpr ⟨source.toValidity, ih source sourceMem, by
        simp [SemanticOccurrence.toValidity, SemanticOccurrence.prefixPath,
          SemanticOccurrence.through, ValidityOccurrence.prefixPath,
          ValidityOccurrence.through]⟩
  | strictUntil interval invariant target ihInvariant ihTarget =>
      by_cases nontrivial : interval.lower < interval.upper
      · simp only [semanticOccurrences, dif_pos nontrivial, List.mem_append,
          List.mem_map] at present
        rcases present with ⟨source, sourceMem, rfl⟩ | ⟨source, sourceMem, rfl⟩
        · simp only [validityOccurrences, dif_pos nontrivial, List.mem_append]
          exact Or.inl (List.mem_map.mpr ⟨source.toValidity,
            ihInvariant source sourceMem, by
            simp [SemanticOccurrence.toValidity, SemanticOccurrence.prefixPath,
              SemanticOccurrence.beforeTarget, ValidityOccurrence.prefixPath,
              ValidityOccurrence.beforeTarget]⟩)
        · simp only [validityOccurrences, List.mem_append]
          exact Or.inr (List.mem_map.mpr ⟨source.toValidity, ihTarget source sourceMem, by
            simp [SemanticOccurrence.toValidity, SemanticOccurrence.prefixPath,
              SemanticOccurrence.through, ValidityOccurrence.prefixPath,
              ValidityOccurrence.through]⟩)
      · simp only [semanticOccurrences, dif_neg nontrivial, List.nil_append,
          List.mem_map] at present
        rcases present with ⟨source, sourceMem, rfl⟩
        simp only [validityOccurrences, dif_neg nontrivial, List.nil_append]
        exact List.mem_map.mpr ⟨source.toValidity, ihTarget source sourceMem, by
          simp [SemanticOccurrence.toValidity, SemanticOccurrence.prefixPath,
            SemanticOccurrence.through, ValidityOccurrence.prefixPath,
            ValidityOccurrence.through]⟩
  | strictRelease interval target invariant ihTarget ihInvariant =>
      by_cases nontrivial : interval.lower < interval.upper
      · simp only [semanticOccurrences, dif_pos nontrivial, List.mem_append,
          List.mem_map] at present
        rcases present with ⟨source, sourceMem, rfl⟩ | ⟨source, sourceMem, rfl⟩
        · simp only [validityOccurrences, dif_pos nontrivial, List.mem_append]
          exact Or.inl (List.mem_map.mpr ⟨source.toValidity, ihTarget source sourceMem, by
            simp [SemanticOccurrence.toValidity, SemanticOccurrence.prefixPath,
              SemanticOccurrence.beforeTarget, ValidityOccurrence.prefixPath,
              ValidityOccurrence.beforeTarget]⟩)
        · simp only [validityOccurrences, List.mem_append]
          exact Or.inr (List.mem_map.mpr ⟨source.toValidity,
            ihInvariant source sourceMem, by
            simp [SemanticOccurrence.toValidity, SemanticOccurrence.prefixPath,
              SemanticOccurrence.through, ValidityOccurrence.prefixPath,
              ValidityOccurrence.through]⟩)
      · simp only [semanticOccurrences, dif_neg nontrivial, List.nil_append,
          List.mem_map] at present
        rcases present with ⟨source, sourceMem, rfl⟩
        simp only [validityOccurrences, dif_neg nontrivial, List.nil_append]
        exact List.mem_map.mpr ⟨source.toValidity, ihInvariant source sourceMem, by
          simp [SemanticOccurrence.toValidity, SemanticOccurrence.prefixPath,
            SemanticOccurrence.through, ValidityOccurrence.prefixPath,
            ValidityOccurrence.through]⟩

def SemanticOccurrence.Supports (start instant : Nat)
    (occurrence : SemanticOccurrence Atom) : Prop :=
  start + occurrence.window.lower ≤ instant ∧
    instant ≤ start + occurrence.window.upper

/-- Atomic truth is only required to be preserved on the validity windows of
the corresponding signed leaf. -/
def AtomicallyPreserves (formula : Stlsat.Formula Atom) (start : Nat)
    (semantics : Stlsat.AtomicSemantics Atom)
    (left right : Stlsat.Signal semantics) : Prop :=
  ∀ occurrence ∈ semanticOccurrences formula, ∀ instant,
    occurrence.Supports start instant →
      occurrence.leaf.Holds semantics (left instant) →
        occurrence.leaf.Holds semantics (right instant)

/-- Strict-normal satisfaction is monotone under preservation of all signed
leaf tests on their validity windows. -/
theorem satisfies_of_atomicallyPreserves (formula : Stlsat.Formula Atom)
    (normal : formula.InStrictNormalForm)
    (semantics : Stlsat.AtomicSemantics Atom) {left right : Stlsat.Signal semantics}
    {start : Nat} (holds : formula.Satisfies semantics left start)
    (preserves : AtomicallyPreserves formula start semantics left right) :
    formula.Satisfies semantics right start := by
  induction formula generalizing start with
  | truth => simp [Stlsat.Formula.Satisfies]
  | atom atom =>
      simp only [Stlsat.Formula.Satisfies]
      apply preserves { path := [], window := ⟨0, 0, le_rfl⟩, leaf := .positive atom }
        (instant := start)
      · simp [semanticOccurrences]
      · simp [SemanticOccurrence.Supports]
      · simpa [Stlsat.Formula.Satisfies, SignedLeaf.Holds] using holds
  | neg body ih =>
      cases body with
      | truth =>
          simp [Stlsat.Formula.Satisfies] at holds
      | atom atom =>
          simp only [Stlsat.Formula.Satisfies] at holds ⊢
          apply preserves
            { path := [0], window := ⟨0, 0, le_rfl⟩, leaf := .negative atom }
            (instant := start)
          · simp [semanticOccurrences, SemanticOccurrence.negate,
              SemanticOccurrence.prefixPath, SignedLeaf.negate]
          · simp [SemanticOccurrence.Supports]
          · simpa [Stlsat.Formula.Satisfies, SignedLeaf.Holds] using holds
      | neg body => simp [Stlsat.Formula.InStrictNormalForm] at normal
      | and left right => simp [Stlsat.Formula.InStrictNormalForm] at normal
      | or left right => simp [Stlsat.Formula.InStrictNormalForm] at normal
      | eventually interval body => simp [Stlsat.Formula.InStrictNormalForm] at normal
      | always interval body => simp [Stlsat.Formula.InStrictNormalForm] at normal
      | strictUntil interval left right =>
          simp [Stlsat.Formula.InStrictNormalForm] at normal
      | strictRelease interval left right =>
          simp [Stlsat.Formula.InStrictNormalForm] at normal
  | and left right ihLeft ihRight =>
      simp only [Stlsat.Formula.Satisfies] at holds ⊢
      rcases holds with ⟨leftHolds, rightHolds⟩
      exact ⟨ihLeft normal.1 leftHolds (by
        intro occurrence occurrenceMem instant supported leafHolds
        apply preserves (occurrence.prefixPath 0)
        · exact List.mem_append.mpr (Or.inl
            (List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩))
        · exact supported
        · exact leafHolds),
        ihRight normal.2 rightHolds (by
          intro occurrence occurrenceMem instant supported leafHolds
          apply preserves (occurrence.prefixPath 1)
          · exact List.mem_append.mpr (Or.inr
              (List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩))
          · exact supported
          · exact leafHolds)⟩
  | or left right ihLeft ihRight =>
      simp only [Stlsat.Formula.Satisfies] at holds ⊢
      rcases holds with leftHolds | rightHolds
      · exact Or.inl (ihLeft normal.1 leftHolds (by
          intro occurrence occurrenceMem instant supported leafHolds
          apply preserves (occurrence.prefixPath 0)
          · exact List.mem_append.mpr (Or.inl
              (List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩))
          · exact supported
          · exact leafHolds))
      · exact Or.inr (ihRight normal.2 rightHolds (by
          intro occurrence occurrenceMem instant supported leafHolds
          apply preserves (occurrence.prefixPath 1)
          · exact List.mem_append.mpr (Or.inr
              (List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩))
          · exact supported
          · exact leafHolds))
  | eventually interval body ih =>
      simp only [Stlsat.Formula.Satisfies] at holds ⊢
      rcases holds with ⟨offset, contained, bodyHolds⟩
      refine ⟨offset, contained, ih normal bodyHolds ?_⟩
      intro occurrence occurrenceMem instant supported leafHolds
      apply preserves ((occurrence.through interval).prefixPath 0)
      · exact List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩
      · rcases contained with ⟨offsetLower, offsetUpper⟩
        rcases supported with ⟨supportLower, supportUpper⟩
        simp only [SemanticOccurrence.Supports, SemanticOccurrence.prefixPath,
          SemanticOccurrence.through] at supportLower supportUpper ⊢
        omega
      · exact leafHolds
  | always interval body ih =>
      simp only [Stlsat.Formula.Satisfies] at holds ⊢
      intro offset contained
      apply ih normal (holds offset contained)
      intro occurrence occurrenceMem instant supported leafHolds
      apply preserves ((occurrence.through interval).prefixPath 0)
      · exact List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩
      · rcases contained with ⟨offsetLower, offsetUpper⟩
        rcases supported with ⟨supportLower, supportUpper⟩
        simp only [SemanticOccurrence.Supports, SemanticOccurrence.prefixPath,
          SemanticOccurrence.through] at supportLower supportUpper ⊢
        omega
      · exact leafHolds
  | strictUntil interval invariant target ihInvariant ihTarget =>
      simp only [Stlsat.Formula.Satisfies] at holds ⊢
      rcases holds with ⟨targetOffset, contained, targetHolds, invariantsHold⟩
      refine ⟨targetOffset, contained, ihTarget normal.2 targetHolds ?_, ?_⟩
      · intro occurrence occurrenceMem instant supported leafHolds
        apply preserves ((occurrence.through interval).prefixPath 1)
        · apply List.mem_append.mpr
          exact Or.inr (List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩)
        · rcases contained with ⟨targetLower, targetUpper⟩
          rcases supported with ⟨supportLower, supportUpper⟩
          simp only [SemanticOccurrence.Supports, SemanticOccurrence.prefixPath,
            SemanticOccurrence.through] at supportLower supportUpper ⊢
          omega
        · exact leafHolds
      · intro invariantOffset lower beforeTarget
        apply ihInvariant normal.1 (invariantsHold invariantOffset lower beforeTarget)
        intro occurrence occurrenceMem instant supported leafHolds
        have nontrivial : interval.lower < interval.upper := by
          rcases contained with ⟨_, targetUpper⟩
          omega
        apply preserves ((occurrence.beforeTarget interval nontrivial).prefixPath 0)
        · simp only [semanticOccurrences, dif_pos nontrivial]
          apply List.mem_append.mpr
          exact Or.inl (List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩)
        · rcases supported with ⟨supportLower, supportUpper⟩
          have invariantLe : invariantOffset ≤ interval.upper - 1 :=
            Nat.le_sub_one_of_lt (beforeTarget.trans_le contained.2)
          simp only [SemanticOccurrence.Supports, SemanticOccurrence.prefixPath,
            SemanticOccurrence.beforeTarget] at supportLower supportUpper ⊢
          omega
        · exact leafHolds
  | strictRelease interval target invariant ihTarget ihInvariant =>
      simp only [Stlsat.Formula.Satisfies] at holds ⊢
      intro violation
      apply holds
      rcases violation with ⟨violatingOffset, contained, invariantFails, targetsFail⟩
      refine ⟨violatingOffset, contained, ?_, ?_⟩
      · intro invariantLeft
        apply invariantFails
        apply ihInvariant normal.2 invariantLeft
        intro occurrence occurrenceMem instant supported leafHolds
        apply preserves ((occurrence.through interval).prefixPath 1)
        · apply List.mem_append.mpr
          exact Or.inr (List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩)
        · rcases contained with ⟨violatingLower, violatingUpper⟩
          rcases supported with ⟨supportLower, supportUpper⟩
          simp only [SemanticOccurrence.Supports, SemanticOccurrence.prefixPath,
            SemanticOccurrence.through] at supportLower supportUpper ⊢
          omega
        · exact leafHolds
      · intro targetOffset lower beforeViolation targetLeft
        apply targetsFail targetOffset lower beforeViolation
        apply ihTarget normal.1 targetLeft
        intro occurrence occurrenceMem instant supported leafHolds
        have nontrivial : interval.lower < interval.upper := by
          rcases contained with ⟨_, violatingUpper⟩
          omega
        apply preserves ((occurrence.beforeTarget interval nontrivial).prefixPath 0)
        · simp only [semanticOccurrences, dif_pos nontrivial]
          apply List.mem_append.mpr
          exact Or.inl (List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩)
        · rcases supported with ⟨supportLower, supportUpper⟩
          have targetLe : targetOffset ≤ interval.upper - 1 :=
            Nat.le_sub_one_of_lt (beforeViolation.trans_le contained.2)
          simp only [SemanticOccurrence.Supports, SemanticOccurrence.prefixPath,
            SemanticOccurrence.beforeTarget] at supportLower supportUpper ⊢
          omega
        · exact leafHolds

variable {semantics : Stlsat.AtomicSemantics Atom}

/-- A modeled formula together with its canonical formula-root identifier. -/
structure RootedRequirement (semantics : Stlsat.AtomicSemantics Atom) where
  root : OccurrenceId
  formula : Stlsat.Formula Atom
  start : Nat
  signal : Stlsat.Signal semantics
  holds : formula.Satisfies semantics signal start
  normal : formula.InStrictNormalForm

namespace RootedRequirement

def Compatible (left right : RootedRequirement semantics) : Prop :=
  ∀ leftOccurrence ∈ semanticOccurrences left.formula,
    ∀ rightOccurrence ∈ semanticOccurrences right.formula,
      ∀ instant,
        leftOccurrence.Supports left.start instant →
        rightOccurrence.Supports right.start instant →
          left.root ++ leftOccurrence.path = right.root ++ rightOccurrence.path ∧
            leftOccurrence.leaf = rightOccurrence.leaf

theorem Compatible.symm {left right : RootedRequirement semantics}
    (compatible : left.Compatible right) : right.Compatible left := by
  intro rightOccurrence rightMem leftOccurrence leftMem instant rightSupport leftSupport
  rcases compatible leftOccurrence leftMem rightOccurrence rightMem instant leftSupport
      rightSupport with ⟨id, leaf⟩
  exact ⟨id.symm, leaf.symm⟩

end RootedRequirement

variable {Atom : Type u} {semantics : Stlsat.AtomicSemantics Atom}

/-- Pairwise compatible modeled requirements admit a common signal.  At each
instant the construction chooses one valuation witnessing a demanded signed
leaf; compatibility guarantees that it witnesses every other demand there. -/
theorem exists_signal_satisfying_compatible
    (requirements : List (RootedRequirement semantics))
    (compatible : ∀ left ∈ requirements, ∀ right ∈ requirements,
      left ≠ right → left.signal = right.signal ∨ left.Compatible right) :
    ∃ signal : Stlsat.Signal semantics, ∀ requirement ∈ requirements,
      requirement.formula.Satisfies semantics signal requirement.start := by
  classical
  let DemandAt (instant : Nat) (requirement : RootedRequirement semantics)
      (occurrence : SemanticOccurrence Atom) : Prop :=
    requirement ∈ requirements ∧ occurrence ∈ semanticOccurrences requirement.formula ∧
      occurrence.Supports requirement.start instant ∧
        occurrence.leaf.Holds semantics (requirement.signal instant)
  let demanded (instant : Nat) : Prop :=
    ∃ requirement occurrence, DemandAt instant requirement occurrence
  let combined : Stlsat.Signal semantics := fun instant =>
    if existsDemand : demanded instant then
      (Classical.choose existsDemand).signal instant
    else Classical.choice semantics.nonempty
  refine ⟨combined, ?_⟩
  intro requirement requirementMem
  apply satisfies_of_atomicallyPreserves requirement.formula requirement.normal semantics
    requirement.holds
  intro occurrence occurrenceMem instant supported leafHolds
  have existsDemand : demanded instant := by
    refine ⟨requirement, occurrence, requirementMem, occurrenceMem, supported, leafHolds⟩
  let chosenRequirement : RootedRequirement semantics := Classical.choose existsDemand
  let chosenOccurrence : SemanticOccurrence Atom := Classical.choose (Classical.choose_spec existsDemand)
  have chosenDemand : DemandAt instant chosenRequirement chosenOccurrence :=
    Classical.choose_spec (Classical.choose_spec existsDemand)
  have combinedEq : combined instant = chosenRequirement.signal instant := by
    simp only [combined, dif_pos existsDemand, chosenRequirement]
  rw [combinedEq]
  by_cases equal : chosenRequirement = requirement
  · rw [equal]
    exact leafHolds
  · rcases compatible chosenRequirement chosenDemand.1 requirement requirementMem equal with
      sameSignal | relation
    · rw [sameSignal]
      exact leafHolds
    · have related := relation chosenOccurrence chosenDemand.2.1 occurrence occurrenceMem
          instant chosenDemand.2.2.1 supported
      rw [← related.2]
      exact chosenDemand.2.2.2

/-- Signed validity occurrences for absolute tableau satisfaction. -/
def semanticFrom (time : Nat) : Stlsat.Formula Atom →
    List (SemanticOccurrence Atom)
  | .truth => [{ path := [], window := ⟨time, time, le_rfl⟩, leaf := .truth }]
  | .atom atom =>
      [{ path := [], window := ⟨time, time, le_rfl⟩, leaf := .positive atom }]
  | .neg body =>
      (semanticFrom time body).map (fun occurrence => occurrence.negate.prefixPath 0)
  | .and left right | .or left right =>
      (semanticFrom time left).map (SemanticOccurrence.prefixPath 0) ++
        (semanticFrom time right).map (SemanticOccurrence.prefixPath 1)
  | formula@(.eventually _ _) | formula@(.always _ _) |
      formula@(.strictUntil _ _ _) | formula@(.strictRelease _ _ _) =>
      semanticOccurrences formula

/-- Absolute and relative validity use the same canonical paths and signed
leaves; only propositional windows are translated to the supplied instant. -/
theorem semanticFrom_source (formula : Stlsat.Formula Atom) (time : Nat)
    (occurrence : SemanticOccurrence Atom)
    (present : occurrence ∈ semanticFrom time formula) :
    ∃ source ∈ semanticOccurrences formula,
      source.path = occurrence.path ∧ source.leaf = occurrence.leaf := by
  induction formula generalizing occurrence with
  | truth =>
      simp only [semanticFrom, List.mem_singleton] at present
      subst occurrence
      exact ⟨{ path := [], window := ⟨0, 0, le_rfl⟩, leaf := .truth }, by
        simp [semanticOccurrences], rfl, rfl⟩
  | atom atom =>
      simp only [semanticFrom, List.mem_singleton] at present
      subst occurrence
      exact ⟨{ path := [], window := ⟨0, 0, le_rfl⟩, leaf := .positive atom }, by
        simp [semanticOccurrences], rfl, rfl⟩
  | neg body ih =>
      rcases List.mem_map.mp present with ⟨child, childMem, rfl⟩
      rcases ih child childMem with ⟨source, sourceMem, path, leaf⟩
      refine ⟨source.negate.prefixPath 0, List.mem_map.mpr ⟨source, sourceMem, rfl⟩,
        ?_, ?_⟩ <;> simp [SemanticOccurrence.negate, SemanticOccurrence.prefixPath,
          path, leaf]
  | and left right ihLeft ihRight =>
      simp only [semanticFrom, List.mem_append, List.mem_map] at present
      rcases present with ⟨child, childMem, rfl⟩ | ⟨child, childMem, rfl⟩
      · rcases ihLeft child childMem with ⟨source, sourceMem, path, leaf⟩
        exact ⟨source.prefixPath 0, List.mem_append.mpr
          (Or.inl (List.mem_map.mpr ⟨source, sourceMem, rfl⟩)), by
            simp [SemanticOccurrence.prefixPath, path], by
            simp [SemanticOccurrence.prefixPath, leaf]⟩
      · rcases ihRight child childMem with ⟨source, sourceMem, path, leaf⟩
        exact ⟨source.prefixPath 1, List.mem_append.mpr
          (Or.inr (List.mem_map.mpr ⟨source, sourceMem, rfl⟩)), by
            simp [SemanticOccurrence.prefixPath, path], by
            simp [SemanticOccurrence.prefixPath, leaf]⟩
  | or left right ihLeft ihRight =>
      simp only [semanticFrom, List.mem_append, List.mem_map] at present
      rcases present with ⟨child, childMem, rfl⟩ | ⟨child, childMem, rfl⟩
      · rcases ihLeft child childMem with ⟨source, sourceMem, path, leaf⟩
        exact ⟨source.prefixPath 0, List.mem_append.mpr
          (Or.inl (List.mem_map.mpr ⟨source, sourceMem, rfl⟩)), by
            simp [SemanticOccurrence.prefixPath, path], by
            simp [SemanticOccurrence.prefixPath, leaf]⟩
      · rcases ihRight child childMem with ⟨source, sourceMem, path, leaf⟩
        exact ⟨source.prefixPath 1, List.mem_append.mpr
          (Or.inr (List.mem_map.mpr ⟨source, sourceMem, rfl⟩)), by
            simp [SemanticOccurrence.prefixPath, path], by
            simp [SemanticOccurrence.prefixPath, leaf]⟩
  | eventually interval body => exact ⟨occurrence, present, rfl, rfl⟩
  | always interval body => exact ⟨occurrence, present, rfl, rfl⟩
  | strictUntil interval invariant target => exact ⟨occurrence, present, rfl, rfl⟩
  | strictRelease interval target invariant => exact ⟨occurrence, present, rfl, rfl⟩

theorem semanticFrom_eq_of_temporal (formula : Stlsat.Formula Atom)
    (temporal : formula.isTemporal = true) (first second : Nat) :
    semanticFrom first formula = semanticFrom second formula := by
  cases formula <;> simp_all [Stlsat.Formula.isTemporal, semanticFrom]

theorem semanticFrom_eq_semanticOccurrences_of_temporal
    (formula : Stlsat.Formula Atom) (temporal : formula.isTemporal = true)
    (time : Nat) : semanticFrom time formula = semanticOccurrences formula := by
  cases formula <;> simp_all [Stlsat.Formula.isTemporal, semanticFrom]

def AbsoluteAtomicallyPreserves (formula : Stlsat.Formula Atom) (time : Nat)
    (semantics : Stlsat.AtomicSemantics Atom)
    (left right : Stlsat.Signal semantics) : Prop :=
  ∀ occurrence ∈ semanticFrom time formula, ∀ instant,
    occurrence.window.lower ≤ instant → instant ≤ occurrence.window.upper →
      occurrence.leaf.Holds semantics (left instant) →
        occurrence.leaf.Holds semantics (right instant)

/-- Absolute tableau satisfaction has the same signed-leaf monotonicity as
relative STL satisfaction. -/
theorem satisfiesFrom_of_absoluteAtomicallyPreserves
    (formula : Stlsat.Formula Atom) (normal : formula.InStrictNormalForm)
    (semantics : Stlsat.AtomicSemantics Atom) {left right : Stlsat.Signal semantics}
    {time : Nat} (holds : formula.SatisfiesFrom semantics left time)
    (preserves : AbsoluteAtomicallyPreserves formula time semantics left right) :
    formula.SatisfiesFrom semantics right time := by
  cases formula with
  | truth => simp [Stlsat.Formula.SatisfiesFrom]
  | atom atom =>
      simp only [Stlsat.Formula.SatisfiesFrom] at holds ⊢
      apply preserves
        { path := [], window := ⟨time, time, le_rfl⟩, leaf := .positive atom }
        (by simp [semanticFrom]) time le_rfl le_rfl
      simpa [Stlsat.Formula.SatisfiesFrom, SignedLeaf.Holds] using holds
  | neg body =>
      cases body with
      | truth => simp [Stlsat.Formula.SatisfiesFrom] at holds
      | atom atom =>
          simp only [Stlsat.Formula.SatisfiesFrom] at holds ⊢
          apply preserves
            { path := [0], window := ⟨time, time, le_rfl⟩, leaf := .negative atom }
            (by simp [semanticFrom, SemanticOccurrence.negate,
              SemanticOccurrence.prefixPath, SignedLeaf.negate]) time le_rfl le_rfl
          simpa [Stlsat.Formula.SatisfiesFrom, SignedLeaf.Holds] using holds
      | neg body => simp [Stlsat.Formula.InStrictNormalForm] at normal
      | and left right => simp [Stlsat.Formula.InStrictNormalForm] at normal
      | or left right => simp [Stlsat.Formula.InStrictNormalForm] at normal
      | eventually interval body => simp [Stlsat.Formula.InStrictNormalForm] at normal
      | always interval body => simp [Stlsat.Formula.InStrictNormalForm] at normal
      | strictUntil interval left right =>
          simp [Stlsat.Formula.InStrictNormalForm] at normal
      | strictRelease interval left right =>
          simp [Stlsat.Formula.InStrictNormalForm] at normal
  | and leftFormula rightFormula =>
      simp only [Stlsat.Formula.SatisfiesFrom] at holds ⊢
      refine ⟨satisfiesFrom_of_absoluteAtomicallyPreserves leftFormula normal.1 semantics
        holds.1 ?_, satisfiesFrom_of_absoluteAtomicallyPreserves rightFormula normal.2
        semantics holds.2 ?_⟩
      · intro occurrence occurrenceMem instant lower upper leafHolds
        apply preserves (occurrence.prefixPath 0)
        · exact List.mem_append.mpr (Or.inl
            (List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩))
        · exact lower
        · exact upper
        · exact leafHolds
      · intro occurrence occurrenceMem instant lower upper leafHolds
        apply preserves (occurrence.prefixPath 1)
        · exact List.mem_append.mpr (Or.inr
            (List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩))
        · exact lower
        · exact upper
        · exact leafHolds
  | or leftFormula rightFormula =>
      simp only [Stlsat.Formula.SatisfiesFrom] at holds ⊢
      rcases holds with leftHolds | rightHolds
      · exact Or.inl (satisfiesFrom_of_absoluteAtomicallyPreserves leftFormula normal.1
          semantics leftHolds (by
            intro occurrence occurrenceMem instant lower upper leafHolds
            apply preserves (occurrence.prefixPath 0)
            · exact List.mem_append.mpr (Or.inl
                (List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩))
            · exact lower
            · exact upper
            · exact leafHolds))
      · exact Or.inr (satisfiesFrom_of_absoluteAtomicallyPreserves rightFormula normal.2
          semantics rightHolds (by
            intro occurrence occurrenceMem instant lower upper leafHolds
            apply preserves (occurrence.prefixPath 1)
            · exact List.mem_append.mpr (Or.inr
                (List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩))
            · exact lower
            · exact upper
            · exact leafHolds))
  | eventually interval body =>
      simp only [Stlsat.Formula.SatisfiesFrom] at holds ⊢
      rcases holds with ⟨offset, contained, bodyHolds⟩
      refine ⟨offset, contained,
        satisfies_of_atomicallyPreserves body normal semantics bodyHolds ?_⟩
      intro occurrence occurrenceMem instant supported leafHolds
      apply preserves ((occurrence.through interval).prefixPath 0)
      · exact List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩
      · rcases contained with ⟨containedLower, containedUpper⟩
        rcases supported with ⟨supportLower, supportUpper⟩
        simp only [SemanticOccurrence.prefixPath, SemanticOccurrence.through]
        omega
      · rcases contained with ⟨containedLower, containedUpper⟩
        rcases supported with ⟨supportLower, supportUpper⟩
        simp only [SemanticOccurrence.prefixPath, SemanticOccurrence.through]
        omega
      · exact leafHolds
  | always interval body =>
      simp only [Stlsat.Formula.SatisfiesFrom] at holds ⊢
      intro offset contained
      apply satisfies_of_atomicallyPreserves body normal semantics (holds offset contained)
      intro occurrence occurrenceMem instant supported leafHolds
      apply preserves ((occurrence.through interval).prefixPath 0)
      · exact List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩
      · rcases contained with ⟨containedLower, containedUpper⟩
        rcases supported with ⟨supportLower, supportUpper⟩
        simp only [SemanticOccurrence.prefixPath, SemanticOccurrence.through]
        omega
      · rcases contained with ⟨containedLower, containedUpper⟩
        rcases supported with ⟨supportLower, supportUpper⟩
        simp only [SemanticOccurrence.prefixPath, SemanticOccurrence.through]
        omega
      · exact leafHolds
  | strictUntil interval invariant target =>
      simp only [Stlsat.Formula.SatisfiesFrom] at holds ⊢
      rcases holds with ⟨targetOffset, contained, targetHolds, invariantsHold⟩
      refine ⟨targetOffset, contained,
        satisfies_of_atomicallyPreserves target normal.2 semantics targetHolds ?_, ?_⟩
      · intro occurrence occurrenceMem instant supported leafHolds
        apply preserves ((occurrence.through interval).prefixPath 1)
        · exact List.mem_append.mpr (Or.inr
            (List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩))
        · rcases contained with ⟨containedLower, containedUpper⟩
          rcases supported with ⟨supportLower, supportUpper⟩
          simp only [SemanticOccurrence.prefixPath, SemanticOccurrence.through]
          omega
        · rcases contained with ⟨containedLower, containedUpper⟩
          rcases supported with ⟨supportLower, supportUpper⟩
          simp only [SemanticOccurrence.prefixPath, SemanticOccurrence.through]
          omega
        · exact leafHolds
      · intro invariantOffset lower beforeTarget
        apply satisfies_of_atomicallyPreserves invariant normal.1 semantics
          (invariantsHold invariantOffset lower beforeTarget)
        intro occurrence occurrenceMem instant supported leafHolds
        have nontrivial : interval.lower < interval.upper := by
          rcases contained with ⟨_, upper⟩
          omega
        apply preserves ((occurrence.beforeTarget interval nontrivial).prefixPath 0)
        · simp only [semanticFrom, semanticOccurrences, dif_pos nontrivial,
            List.mem_append]
          exact Or.inl (List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩)
        · rcases supported with ⟨supportLower, supportUpper⟩
          simp only [SemanticOccurrence.prefixPath, SemanticOccurrence.beforeTarget]
          omega
        · rcases supported with ⟨supportLower, supportUpper⟩
          have targetUpper : time + targetOffset ≤ interval.upper := contained.2
          have invariantLe : time + invariantOffset ≤ interval.upper - 1 :=
            Nat.le_sub_one_of_lt (by omega)
          simp only [SemanticOccurrence.prefixPath, SemanticOccurrence.beforeTarget]
          omega
        · exact leafHolds
  | strictRelease interval target invariant =>
      simp only [Stlsat.Formula.SatisfiesFrom] at holds ⊢
      intro violation
      apply holds
      rcases violation with ⟨violatingOffset, contained, invariantFails, targetsFail⟩
      refine ⟨violatingOffset, contained, ?_, ?_⟩
      · intro invariantLeft
        apply invariantFails
        apply satisfies_of_atomicallyPreserves invariant normal.2 semantics invariantLeft
        intro occurrence occurrenceMem instant supported leafHolds
        apply preserves ((occurrence.through interval).prefixPath 1)
        · exact List.mem_append.mpr (Or.inr
            (List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩))
        · rcases contained with ⟨containedLower, containedUpper⟩
          rcases supported with ⟨supportLower, supportUpper⟩
          simp only [SemanticOccurrence.prefixPath, SemanticOccurrence.through]
          omega
        · rcases contained with ⟨containedLower, containedUpper⟩
          rcases supported with ⟨supportLower, supportUpper⟩
          simp only [SemanticOccurrence.prefixPath, SemanticOccurrence.through]
          omega
        · exact leafHolds
      · intro targetOffset lower beforeViolation targetLeft
        apply targetsFail targetOffset lower beforeViolation
        apply satisfies_of_atomicallyPreserves target normal.1 semantics targetLeft
        intro occurrence occurrenceMem instant supported leafHolds
        have nontrivial : interval.lower < interval.upper := by
          rcases contained with ⟨_, upper⟩
          omega
        apply preserves ((occurrence.beforeTarget interval nontrivial).prefixPath 0)
        · simp only [semanticFrom, semanticOccurrences, dif_pos nontrivial,
            List.mem_append]
          exact Or.inl (List.mem_map.mpr ⟨occurrence, occurrenceMem, rfl⟩)
        · rcases supported with ⟨supportLower, supportUpper⟩
          simp only [SemanticOccurrence.prefixPath, SemanticOccurrence.beforeTarget]
          omega
        · rcases supported with ⟨supportLower, supportUpper⟩
          have violatingUpper : time + violatingOffset ≤ interval.upper := contained.2
          have targetLe : time + targetOffset ≤ interval.upper - 1 :=
            Nat.le_sub_one_of_lt (by omega)
          simp only [SemanticOccurrence.prefixPath, SemanticOccurrence.beforeTarget]
          omega
        · exact leafHolds

structure AbsoluteRootedRequirement (semantics : Stlsat.AtomicSemantics Atom) where
  root : OccurrenceId
  formula : Stlsat.Formula Atom
  time : Nat
  signal : Stlsat.Signal semantics
  holds : formula.SatisfiesFrom semantics signal time
  normal : formula.InStrictNormalForm

namespace AbsoluteRootedRequirement

def Compatible (left right : AbsoluteRootedRequirement semantics) : Prop :=
  ∀ leftOccurrence ∈ semanticFrom left.time left.formula,
    ∀ rightOccurrence ∈ semanticFrom right.time right.formula,
      ∀ instant,
        leftOccurrence.window.lower ≤ instant → instant ≤ leftOccurrence.window.upper →
        rightOccurrence.window.lower ≤ instant → instant ≤ rightOccurrence.window.upper →
          left.root ++ leftOccurrence.path = right.root ++ rightOccurrence.path ∧
            leftOccurrence.leaf = rightOccurrence.leaf

end AbsoluteRootedRequirement

theorem exists_signal_satisfying_absolute_compatible
    (requirements : List (AbsoluteRootedRequirement semantics))
    (compatible : ∀ left ∈ requirements, ∀ right ∈ requirements,
      left ≠ right → left.signal = right.signal ∨ left.Compatible right) :
    ∃ signal : Stlsat.Signal semantics, ∀ requirement ∈ requirements,
      requirement.formula.SatisfiesFrom semantics signal requirement.time := by
  classical
  let DemandAt (instant : Nat) (requirement : AbsoluteRootedRequirement semantics)
      (occurrence : SemanticOccurrence Atom) : Prop :=
    requirement ∈ requirements ∧ occurrence ∈ semanticFrom requirement.time requirement.formula ∧
      occurrence.window.lower ≤ instant ∧ instant ≤ occurrence.window.upper ∧
        occurrence.leaf.Holds semantics (requirement.signal instant)
  let demanded (instant : Nat) : Prop :=
    ∃ requirement occurrence, DemandAt instant requirement occurrence
  let combined : Stlsat.Signal semantics := fun instant =>
    if existsDemand : demanded instant then
      (Classical.choose existsDemand).signal instant
    else Classical.choice semantics.nonempty
  refine ⟨combined, ?_⟩
  intro requirement requirementMem
  apply satisfiesFrom_of_absoluteAtomicallyPreserves requirement.formula requirement.normal
    semantics requirement.holds
  intro occurrence occurrenceMem instant lower upper leafHolds
  have existsDemand : demanded instant := by
    exact ⟨requirement, occurrence, requirementMem, occurrenceMem, lower, upper, leafHolds⟩
  let chosenRequirement : AbsoluteRootedRequirement semantics := Classical.choose existsDemand
  let chosenOccurrence : SemanticOccurrence Atom :=
    Classical.choose (Classical.choose_spec existsDemand)
  have chosenDemand : DemandAt instant chosenRequirement chosenOccurrence :=
    Classical.choose_spec (Classical.choose_spec existsDemand)
  have combinedEq : combined instant = chosenRequirement.signal instant := by
    simp only [combined, dif_pos existsDemand, chosenRequirement]
  rw [combinedEq]
  by_cases equal : chosenRequirement = requirement
  · rw [equal]
    exact leafHolds
  · rcases compatible chosenRequirement chosenDemand.1 requirement requirementMem equal with
      sameSignal | relation
    · rw [sameSignal]
      exact leafHolds
    · have related := relation chosenOccurrence chosenDemand.2.1 occurrence occurrenceMem
          instant chosenDemand.2.2.1 chosenDemand.2.2.2.1 lower upper
      rw [← related.2]
      exact chosenDemand.2.2.2.2

/-- A heterogeneous semantic obligation described solely by absolute signed
leaf windows and a monotonicity proof.  This common interface accommodates
both relative STL satisfaction and absolute tableau satisfaction. -/
structure SemanticRequirement (semantics : Stlsat.AtomicSemantics Atom) where
  root : OccurrenceId
  leaves : List (SemanticOccurrence Atom)
  signal : Stlsat.Signal semantics
  Accepts : Stlsat.Signal semantics → Prop
  holds : Accepts signal
  preserves : ∀ right : Stlsat.Signal semantics,
    (∀ occurrence ∈ leaves, ∀ instant,
      occurrence.window.lower ≤ instant → instant ≤ occurrence.window.upper →
        occurrence.leaf.Holds semantics (signal instant) →
          occurrence.leaf.Holds semantics (right instant)) → Accepts right

namespace SemanticRequirement

def Compatible (left right : SemanticRequirement semantics) : Prop :=
  ∀ leftOccurrence ∈ left.leaves, ∀ rightOccurrence ∈ right.leaves, ∀ instant,
    leftOccurrence.window.lower ≤ instant → instant ≤ leftOccurrence.window.upper →
    rightOccurrence.window.lower ≤ instant → instant ≤ rightOccurrence.window.upper →
      left.root ++ leftOccurrence.path = right.root ++ rightOccurrence.path ∧
        leftOccurrence.leaf = rightOccurrence.leaf

theorem Compatible.symm {left right : SemanticRequirement semantics}
    (compatible : left.Compatible right) : right.Compatible left := by
  intro rightOccurrence rightMem leftOccurrence leftMem instant
    rightLower rightUpper leftLower leftUpper
  rcases compatible leftOccurrence leftMem rightOccurrence rightMem instant
    leftLower leftUpper rightLower rightUpper with ⟨path, leaf⟩
  exact ⟨path.symm, leaf.symm⟩

end SemanticRequirement

/-- Heterogeneous compatible semantic obligations admit one common signal. -/
theorem exists_signal_accepting_semanticRequirements
    (requirements : List (SemanticRequirement semantics))
    (compatible : ∀ left ∈ requirements, ∀ right ∈ requirements,
      left ≠ right → left.signal = right.signal ∨ left.Compatible right) :
    ∃ signal : Stlsat.Signal semantics, ∀ requirement ∈ requirements,
      requirement.Accepts signal := by
  classical
  let DemandAt (instant : Nat) (requirement : SemanticRequirement semantics)
      (occurrence : SemanticOccurrence Atom) : Prop :=
    requirement ∈ requirements ∧ occurrence ∈ requirement.leaves ∧
      occurrence.window.lower ≤ instant ∧ instant ≤ occurrence.window.upper ∧
        occurrence.leaf.Holds semantics (requirement.signal instant)
  let demanded (instant : Nat) : Prop :=
    ∃ requirement occurrence, DemandAt instant requirement occurrence
  let combined : Stlsat.Signal semantics := fun instant =>
    if existsDemand : demanded instant then
      (Classical.choose existsDemand).signal instant
    else Classical.choice semantics.nonempty
  refine ⟨combined, ?_⟩
  intro requirement requirementMem
  apply requirement.preserves combined
  intro occurrence occurrenceMem instant lower upper leafHolds
  have existsDemand : demanded instant := by
    exact ⟨requirement, occurrence, requirementMem, occurrenceMem, lower, upper, leafHolds⟩
  let chosenRequirement : SemanticRequirement semantics := Classical.choose existsDemand
  let chosenOccurrence : SemanticOccurrence Atom :=
    Classical.choose (Classical.choose_spec existsDemand)
  have chosenDemand : DemandAt instant chosenRequirement chosenOccurrence :=
    Classical.choose_spec (Classical.choose_spec existsDemand)
  have combinedEq : combined instant = chosenRequirement.signal instant := by
    simp only [combined, dif_pos existsDemand, chosenRequirement]
  rw [combinedEq]
  by_cases equal : chosenRequirement = requirement
  · rw [equal]
    exact leafHolds
  · rcases compatible chosenRequirement chosenDemand.1 requirement requirementMem equal with
      sameSignal | relation
    · rw [sameSignal]
      exact leafHolds
    · have related := relation chosenOccurrence chosenDemand.2.1 occurrence occurrenceMem
          instant chosenDemand.2.2.1 chosenDemand.2.2.2.1 lower upper
      rw [← related.2]
      exact chosenDemand.2.2.2.2

/-- The choice construction used for finite lists in fact works for an
arbitrary indexed family.  No compactness argument is involved: at each
instant one of the requirements which places a signed demand there is chosen. -/
theorem exists_signal_accepting_semanticRequirement_family
    {Index : Type*} (requirement : Index → SemanticRequirement semantics)
    (compatible : ∀ left right,
      (requirement left).signal = (requirement right).signal ∨
        (requirement left).Compatible (requirement right)) :
    ∃ signal : Stlsat.Signal semantics, ∀ index, (requirement index).Accepts signal := by
  classical
  let DemandAt (instant : Nat) (index : Index)
      (occurrence : SemanticOccurrence Atom) : Prop :=
    occurrence ∈ (requirement index).leaves ∧
      occurrence.window.lower ≤ instant ∧ instant ≤ occurrence.window.upper ∧
        occurrence.leaf.Holds semantics ((requirement index).signal instant)
  let demanded (instant : Nat) : Prop :=
    ∃ index occurrence, DemandAt instant index occurrence
  let combined : Stlsat.Signal semantics := fun instant =>
    if existsDemand : demanded instant then
      (requirement (Classical.choose existsDemand)).signal instant
    else Classical.choice semantics.nonempty
  refine ⟨combined, ?_⟩
  intro index
  apply (requirement index).preserves combined
  intro occurrence occurrenceMem instant lower upper leafHolds
  have existsDemand : demanded instant :=
    ⟨index, occurrence, occurrenceMem, lower, upper, leafHolds⟩
  let chosenIndex : Index := Classical.choose existsDemand
  let chosenOccurrence : SemanticOccurrence Atom :=
    Classical.choose (Classical.choose_spec existsDemand)
  have chosenDemand : DemandAt instant chosenIndex chosenOccurrence :=
    Classical.choose_spec (Classical.choose_spec existsDemand)
  have combinedEq : combined instant = (requirement chosenIndex).signal instant := by
    simp only [combined, dif_pos existsDemand, chosenIndex]
  rw [combinedEq]
  rcases compatible chosenIndex index with sameSignal | relation
  · rw [sameSignal]
    exact leafHolds
  · have related := relation chosenOccurrence chosenDemand.1 occurrence occurrenceMem instant
        chosenDemand.2.1 chosenDemand.2.2.1 lower upper
    rw [← related.2]
    exact chosenDemand.2.2.2

end FormulaValidity
end Stlsat.Jump
