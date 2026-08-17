/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Tableau.Basic.Termination
import Stlsat.Tableau.Construction

/-!
# Construction of the basic tableau

This module instantiates the shared accessibility-to-finite-tree construction
with ordinary expansion and one-instant `STEP`.
-/

namespace Stlsat.Tableau.Basic

universe u

variable {Atom : Type u} [DecidableEq Atom]

/-- A basic node is terminal or has an ordinary rule application. -/
theorem terminal_or_rule (semantics : Stlsat.AtomicSemantics Atom)
    (node : Stlsat.Tableau.Node Atom) :
    node.Terminal semantics ∨ ∃ children, Rule semantics node children := by
  classical
  by_cases rejected : node.Rejected semantics
  · exact Or.inl (Or.inl rejected)
  by_cases expandable : ∃ children, Stlsat.Tableau.Expansion node children
  · rcases expandable with ⟨children, expansion⟩
    exact Or.inr ⟨children, Rule.expand rejected expansion⟩
  have poised : node.Poised := expandable
  by_cases temporal : node.ContainsTemporal
  · exact Or.inr ⟨[node.step], Rule.step rejected poised temporal⟩
  · exact Or.inl (Or.inr ⟨poised, rejected,
      node.stepLabel_eq_empty_of_not_containsTemporal temporal⟩)

namespace Rule

variable {semantics : Stlsat.AtomicSemantics Atom}

theorem children_shape {node : Stlsat.Tableau.Node Atom}
    {children : List (Stlsat.Tableau.Node Atom)}
    (rule : Rule semantics node children) :
    (∃ child, children = [child]) ∨
      (∃ left right, children = [left, right]) := by
  cases rule with
  | expand _ expansion =>
      cases expansion with
      | disjunction => exact Or.inr ⟨_, _, rfl⟩
      | conjunction => exact Or.inl ⟨_, rfl⟩
      | eventuallyBeforeEnd => exact Or.inr ⟨_, _, rfl⟩
      | eventuallyAtEnd => exact Or.inl ⟨_, rfl⟩
      | alwaysBeforeEnd => exact Or.inl ⟨_, rfl⟩
      | alwaysAtEnd => exact Or.inl ⟨_, rfl⟩
      | strictUntilBeforeEnd => exact Or.inr ⟨_, _, rfl⟩
      | strictUntilAtEnd => exact Or.inl ⟨_, rfl⟩
      | strictReleaseBeforeEnd => exact Or.inr ⟨_, _, rfl⟩
      | strictReleaseAtEnd => exact Or.inl ⟨_, rfl⟩
  | step => exact Or.inl ⟨_, rfl⟩

end Rule

namespace Development

variable {semantics : Stlsat.AtomicSemantics Atom}
  {formula : Stlsat.Formula Atom}

/-- Every strict-normal-form formula has a finite fully developed basic
tableau in the shared representation. -/
theorem exists_of_strictNormalForm (normal : formula.InStrictNormalForm) :
    Nonempty (Development semantics formula) := by
  rcases Stlsat.Tableau.TableauTree.exists_wellFormed_terminal_of_accessible_with
      (Rule semantics) (terminal_or_rule semantics)
      (fun rule => rule.children_shape)
      (child_initial_accessible semantics formula) with
    ⟨tree, rooted, wellFormed, terminal⟩
  exact ⟨⟨tree, normal, rooted, wellFormed, terminal⟩⟩

end Development

end Stlsat.Tableau.Basic
