/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.Termination
import Stlsat.Jump.Variable.Soundness

/-!
# Termination of the variable-aware JUMP configuration

Changing the window-conflict guard does not change the shape of successors.
Consequently the shared horizon/expansion-weight measure proves termination
exactly as for the conservative JUMP configuration.
-/

namespace Stlsat.Tableau

universe u w

namespace VariableJump

/-- The shared child relation instantiated with variable-aware JUMP rules. -/
abbrev Child {Atom : Type u} {Var : Type w} [DecidableEq Atom]
    (semantics : Stlsat.AtomicSemantics Atom) (atomSupport : Atom → Finset Var) :=
  Stlsat.Tableau.Child (Rule semantics atomSupport)

namespace Child

variable {Atom : Type u} {Var : Type w} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom} {atomSupport : Atom → Finset Var}

theorem horizonBounded {bound : Nat} {parent child : Node Atom}
    (childOf : Child semantics atomSupport child parent)
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
    (childOf : Child semantics atomSupport child parent)
    (parentTimely : parent.Timely) : child.Timely := by
  rcases childOf with ⟨children, rule, childMem⟩
  exact rule.child_timely parentTimely childMem

theorem terminationMeasure_decreases {bound : Nat}
    {parent child : Node Atom}
    (childOf : Child semantics atomSupport child parent)
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
      have sizePositive := parent.variableJumpSize_pos atomSupport computed
      simp only [Node.jump]
      omega

end Child

private theorem terminationMeasure_wellFounded {Atom : Type u} (bound : Nat) :
    WellFounded
      (InvImage
        (Prod.Lex (fun left right : Nat ↦ left < right)
          (fun left right : Nat ↦ left < right))
        (Node.terminationMeasure (Atom := Atom) bound)) :=
  InvImage.wf _ (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf)

/-- Every bounded timely node is accessible for variable-aware rules. -/
theorem child_accessible_of_invariants
    {Atom : Type u} {Var : Type w} [DecidableEq Atom]
    {semantics : Stlsat.AtomicSemantics Atom} {atomSupport : Atom → Finset Var}
    {bound : Nat} {node : Node Atom}
    (bounded : node.HorizonBounded bound) (timely : node.Timely) :
    Acc (Child semantics atomSupport) node := by
  let relation :=
    InvImage
      (Prod.Lex (fun left right : Nat ↦ left < right)
        (fun left right : Nat ↦ left < right))
      (Node.terminationMeasure (Atom := Atom) bound)
  have relationWf : WellFounded relation := terminationMeasure_wellFounded bound
  refine relationWf.induction node (C := fun current ↦
    current.HorizonBounded bound → current.Timely →
      Acc (Child semantics atomSupport) current) ?_ bounded timely
  intro parent ih parentBounded parentTimely
  apply Acc.intro parent
  intro child childOf
  exact ih child
    (Child.terminationMeasure_decreases childOf parentBounded parentTimely)
    (Child.horizonBounded childOf parentBounded)
    (Child.timely childOf parentTimely)

/-- The initial node is accessible for variable-aware rules. -/
theorem child_initial_accessible
    {Atom : Type u} {Var : Type w} [DecidableEq Atom]
    (semantics : Stlsat.AtomicSemantics Atom) (atomSupport : Atom → Finset Var)
    (formula : Stlsat.Formula Atom) :
    Acc (Child semantics atomSupport) (Node.initial formula) :=
  child_accessible_of_invariants
    (Node.initial_horizonBounded formula) (Node.initial_timely formula)

/-- No infinite variable-aware JUMP branch starts at the initial node. -/
theorem no_infinite_branch
    {Atom : Type u} {Var : Type w} [DecidableEq Atom]
    (semantics : Stlsat.AtomicSemantics Atom) (atomSupport : Atom → Finset Var)
    (formula : Stlsat.Formula Atom) :
    ¬∃ branch : Nat → Node Atom,
      branch 0 = Node.initial formula ∧
        ∀ index, Child semantics atomSupport (branch (index + 1)) (branch index) := by
  intro infiniteBranch
  have noChain := acc_iff_isEmpty_descending_chain.mp
    (child_initial_accessible semantics atomSupport formula)
  rcases infiniteBranch with ⟨branch, startsAt, followsRules⟩
  exact noChain.false ⟨branch, startsAt, followsRules⟩

end VariableJump
end Stlsat.Tableau
