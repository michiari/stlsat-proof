/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Tableau.Termination
import Stlsat.Jump.Semantics
import Mathlib.Order.WellFounded

/-!
# Termination of the STL tableau with JUMP

This file proves accessibility of the initial annotated node for the relation
which chooses one child of a JUMP-tableau rule.  The proof uses the same
lexicographic measure as the basic tableau: remaining global horizon, followed
by the amount of propositional/temporal expansion work at the current time.

Identifiers and parent annotations require the secondary measure to count
annotated occurrences directly.  `STEP` advances by one, while a computed
`JUMP` advances by a strictly positive amount (`Node.jumpSize_pos`).
-/

namespace Stlsat.Tableau

universe u
namespace Node

variable {Atom : Type u} [DecidableEq Atom]

theorem jump_horizonBounded {bound size : Nat} {node : Node Atom}
    (bounded : node.HorizonBounded bound) :
    (node.jump size).HorizonBounded bound := by
  intro occurrence occurrenceMem
  change occurrence ∈ node.jumpLabel size at occurrenceMem
  rcases Finset.mem_image.mp occurrenceMem with ⟨source, sourceMem, rfl⟩
  rw [AnnotatedOccurrence.horizon_unmark]
  exact bounded source (Finset.mem_filter.mp sourceMem).1
end Node
/-- The shared child relation instantiated with JUMP rules. -/
abbrev JumpChild {Atom : Type u} [DecidableEq Atom]
    (semantics : Stlsat.AtomicSemantics Atom) :=
  Child (Jump.Rule semantics)

namespace JumpChild

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom}

theorem horizonBounded {bound : Nat} {parent child : Node Atom}
    (childOf : JumpChild semantics child parent)
    (parentBounded : parent.HorizonBounded bound) :
    child.HorizonBounded bound := by
  rcases childOf with ⟨children, rule, childMem⟩
  cases rule with
  | expand notRejected expansion =>
      exact expansion.child_horizonBounded parentBounded childMem
  | step notRejected poised hasTemporal jumpDisabled =>
      simp only [List.mem_singleton] at childMem
      subst child
      exact Node.step_horizonBounded parentBounded
  | jump notRejected poised hasTemporal sound complete size computed =>
      simp only [List.mem_singleton] at childMem
      subst child
      exact Node.jump_horizonBounded parentBounded

theorem timely {parent child : Node Atom}
    (childOf : JumpChild semantics child parent) (parentTimely : parent.Timely) :
    child.Timely := by
  rcases childOf with ⟨children, rule, childMem⟩
  exact rule.child_timely parentTimely childMem

theorem terminationMeasure_decreases {bound : Nat} {parent child : Node Atom}
    (childOf : JumpChild semantics child parent)
    (parentBounded : parent.HorizonBounded bound)
    (parentTimely : parent.Timely) :
    Prod.Lex (fun left right : Nat ↦ left < right)
      (fun left right : Nat ↦ left < right)
      (child.terminationMeasure bound) (parent.terminationMeasure bound) := by
  rcases childOf with ⟨children, rule, childMem⟩
  cases rule with
  | expand notRejected expansion =>
      rw [Node.terminationMeasure, Node.terminationMeasure,
        expansion.child_time childMem]
      exact Prod.Lex.right _ (expansion.child_expansionWeight_lt childMem)
  | step notRejected poised hasTemporal jumpDisabled =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Prod.Lex.left _ _
      have timeLe := Node.time_le_of_horizonBounded_of_timely_of_containsTemporal
        parentBounded parentTimely hasTemporal
      simp only [Node.step]
      omega
  | jump notRejected poised hasTemporal sound complete size computed =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Prod.Lex.left _ _
      have timeLe := Node.time_le_of_horizonBounded_of_timely_of_containsTemporal
        parentBounded parentTimely hasTemporal
      have sizePositive := parent.jumpSize_pos computed
      simp only [Node.jump]
      omega

end JumpChild

private theorem terminationMeasure_wellFounded {Atom : Type u} (bound : Nat) :
    WellFounded
      (InvImage
        (Prod.Lex (fun left right : Nat ↦ left < right)
          (fun left right : Nat ↦ left < right))
        (Node.terminationMeasure (Atom := Atom) bound)) :=
  InvImage.wf _ (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf)

/-- Every horizon-bounded, timely annotated node is accessible for child
steps of the tableau with JUMP. -/
theorem jumpChild_accessible_of_invariants {Atom : Type u} [DecidableEq Atom]
    {semantics : Stlsat.AtomicSemantics Atom} {bound : Nat} {node : Node Atom}
    (bounded : node.HorizonBounded bound) (timely : node.Timely) :
    Acc (JumpChild semantics) node := by
  let relation :=
    InvImage
      (Prod.Lex (fun left right : Nat ↦ left < right)
        (fun left right : Nat ↦ left < right))
      (Node.terminationMeasure (Atom := Atom) bound)
  have relationWf : WellFounded relation := terminationMeasure_wellFounded bound
  refine relationWf.induction node (C := fun current ↦
    current.HorizonBounded bound → current.Timely →
      Acc (JumpChild semantics) current) ?_ bounded timely
  intro parent ih parentBounded parentTimely
  apply Acc.intro parent
  intro child childOf
  exact ih child
    (JumpChild.terminationMeasure_decreases childOf parentBounded parentTimely)
    (JumpChild.horizonBounded childOf parentBounded)
    (JumpChild.timely childOf parentTimely)

/-- The initial annotated node is accessible for all tableau rules, including
JUMP. -/
theorem jumpChild_initial_accessible {Atom : Type u} [DecidableEq Atom]
    (semantics : Stlsat.AtomicSemantics Atom) (formula : Stlsat.Formula Atom) :
    Acc (JumpChild semantics) (Node.initial formula) :=
  jumpChild_accessible_of_invariants
    (Node.initial_horizonBounded formula) (Node.initial_timely formula)

/-- No infinite branch of JUMP-tableau rules starts at the initial node. -/
theorem no_infinite_jump_tableau_branch {Atom : Type u} [DecidableEq Atom]
    (semantics : Stlsat.AtomicSemantics Atom) (formula : Stlsat.Formula Atom) :
    ¬∃ branch : Nat → Node Atom,
      branch 0 = Node.initial formula ∧
        ∀ index, JumpChild semantics (branch (index + 1)) (branch index) := by
  intro infiniteBranch
  have noChain := acc_iff_isEmpty_descending_chain.mp
    (jumpChild_initial_accessible semantics formula)
  rcases infiniteBranch with ⟨branch, startsAt, followsRules⟩
  exact noChain.false ⟨branch, startsAt, followsRules⟩

end Stlsat.Tableau
