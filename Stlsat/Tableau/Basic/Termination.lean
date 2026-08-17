/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Tableau.Basic
import Stlsat.Tableau.Termination
import Mathlib.Order.WellFounded

/-!
# Termination of the basic rule configuration

The basic and JUMP configurations use the same horizon bound and
lexicographic node measure.  This module supplies only the two ordinary-rule
cases; the canonical measure and expansion lemmas are shared with JUMP.
-/

namespace Stlsat.Tableau.Basic

universe u

open Stlsat.Tableau

/-- The shared child relation instantiated with ordinary basic rules. -/
abbrev Child {Atom : Type u} [DecidableEq Atom]
    (semantics : Stlsat.AtomicSemantics Atom) :=
  Stlsat.Tableau.Child (Rule semantics)

namespace Child

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom}

theorem horizonBounded {bound : Nat} {parent child : Stlsat.Tableau.Node Atom}
    (childOf : Child semantics child parent)
    (parentBounded : parent.HorizonBounded bound) :
    child.HorizonBounded bound := by
  rcases childOf with ⟨children, rule, childMem⟩
  cases rule with
  | expand _ expansion =>
      exact expansion.child_horizonBounded parentBounded childMem
  | step _ _ _ =>
      simp only [List.mem_singleton] at childMem
      subst child
      exact Stlsat.Tableau.Node.step_horizonBounded parentBounded

theorem timely {parent child : Stlsat.Tableau.Node Atom}
    (childOf : Child semantics child parent) (parentTimely : parent.Timely) :
    child.Timely := by
  rcases childOf with ⟨children, rule, childMem⟩
  cases rule with
  | expand _ expansion => exact expansion.child_timely parentTimely childMem
  | step _ poised _ =>
      simp only [List.mem_singleton] at childMem
      subst child
      exact Stlsat.Tableau.Node.step_timely parentTimely poised

theorem terminationMeasure_decreases {bound : Nat} {parent child : Stlsat.Tableau.Node Atom}
    (childOf : Child semantics child parent)
    (parentBounded : parent.HorizonBounded bound)
    (parentTimely : parent.Timely) :
    Prod.Lex (fun left right : Nat ↦ left < right)
      (fun left right : Nat ↦ left < right)
      (child.terminationMeasure bound) (parent.terminationMeasure bound) := by
  rcases childOf with ⟨children, rule, childMem⟩
  cases rule with
  | expand _ expansion =>
      rw [Stlsat.Tableau.Node.terminationMeasure, Stlsat.Tableau.Node.terminationMeasure,
        expansion.child_time childMem]
      exact Prod.Lex.right _ (expansion.child_expansionWeight_lt childMem)
  | step _ _ hasTemporal =>
      simp only [List.mem_singleton] at childMem
      subst child
      apply Prod.Lex.left _ _
      have timeLe := Stlsat.Tableau.Node.time_le_of_horizonBounded_of_timely_of_containsTemporal
        parentBounded parentTimely hasTemporal
      simp only [Stlsat.Tableau.Node.step]
      omega

end Child

private theorem measure_wellFounded {Atom : Type u} (bound : Nat) :
    WellFounded
      (InvImage
        (Prod.Lex (fun left right : Nat ↦ left < right)
          (fun left right : Nat ↦ left < right))
        (Stlsat.Tableau.Node.terminationMeasure (Atom := Atom) bound)) :=
  InvImage.wf _ (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf)

theorem child_accessible_of_invariants {Atom : Type u} [DecidableEq Atom]
    {semantics : Stlsat.AtomicSemantics Atom} {bound : Nat}
    {node : Stlsat.Tableau.Node Atom}
    (bounded : node.HorizonBounded bound) (timely : node.Timely) :
    Acc (Child semantics) node := by
  let relation :=
    InvImage
      (Prod.Lex (fun left right : Nat ↦ left < right)
        (fun left right : Nat ↦ left < right))
      (Stlsat.Tableau.Node.terminationMeasure (Atom := Atom) bound)
  have relationWf : WellFounded relation := measure_wellFounded bound
  refine relationWf.induction node (C := fun current ↦
    current.HorizonBounded bound → current.Timely →
      Acc (Child semantics) current) ?_ bounded timely
  intro parent ih parentBounded parentTimely
  apply Acc.intro parent
  intro child childOf
  exact ih child
    (Child.terminationMeasure_decreases childOf parentBounded parentTimely)
    (Child.horizonBounded childOf parentBounded)
    (Child.timely childOf parentTimely)

theorem child_initial_accessible {Atom : Type u} [DecidableEq Atom]
    (semantics : Stlsat.AtomicSemantics Atom) (formula : Stlsat.Formula Atom) :
    Acc (Child semantics) (Stlsat.Tableau.Node.initial formula) :=
  child_accessible_of_invariants
    (Stlsat.Tableau.Node.initial_horizonBounded formula)
    (Stlsat.Tableau.Node.initial_timely formula)

theorem no_infinite_branch {Atom : Type u} [DecidableEq Atom]
    (semantics : Stlsat.AtomicSemantics Atom) (formula : Stlsat.Formula Atom) :
    ¬∃ branch : Nat → Stlsat.Tableau.Node Atom,
      branch 0 = Stlsat.Tableau.Node.initial formula ∧
        ∀ index, Child semantics (branch (index + 1)) (branch index) := by
  intro infiniteBranch
  have noChain := acc_iff_isEmpty_descending_chain.mp
    (child_initial_accessible semantics formula)
  rcases infiniteBranch with ⟨branch, startsAt, followsRules⟩
  exact noChain.false ⟨branch, startsAt, followsRules⟩

end Stlsat.Tableau.Basic
