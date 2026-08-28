/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.Variable.Completeness
import Stlsat.Jump.Variable.Termination
import Stlsat.Tableau.Basic.Completeness
import Stlsat.Tableau.Construction

/-!
# Finite construction of variable-aware JUMP tableaux

The construction uses the shared raw node/tree framework.  At a poised
temporal node it selects a variable-aware JUMP exactly when its two guards and
the common positive jump size are available; otherwise it selects `STEP`.
-/

namespace Stlsat.Tableau

universe u w

namespace VariableJump

variable {Atom : Type u} {Var : Type w} [DecidableEq Atom]

/-- A node is terminal or a variable-aware tableau rule applies. -/
theorem terminal_or_rule
    (semantics : Stlsat.AtomicSemantics Atom)
    (atomSupport : Atom → Finset Var) (node : Node Atom) :
    node.Terminal semantics ∨
      ∃ children, VariableJump.Rule semantics atomSupport node children := by
  classical
  by_cases rejected : node.Rejected semantics
  · exact Or.inl (Or.inl rejected)
  by_cases expandable : ∃ children, Expansion node children
  · rcases expandable with ⟨children, expansion⟩
    exact Or.inr ⟨children, VariableJump.Rule.expand rejected expansion⟩
  have poised : node.Poised := expandable
  by_cases temporal : node.ContainsTemporal
  · by_cases canJump : node.CanVariableJump atomSupport
    · rcases canJump with ⟨sound, complete, size, computed⟩
      exact Or.inr ⟨[node.jump size],
        VariableJump.Rule.jump rejected poised temporal sound complete size computed⟩
    · exact Or.inr ⟨[node.step],
        VariableJump.Rule.step rejected poised temporal canJump⟩
  · exact Or.inl (Or.inr ⟨poised, rejected,
      node.stepLabel_eq_empty_of_not_containsTemporal temporal⟩)

end VariableJump

namespace VariableJump.Rule

variable {Atom : Type u} {Var : Type w} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom} {atomSupport : Atom → Finset Var}

/-- Every variable-aware rule has the unary/binary shape of `TableauTree`. -/
theorem children_shape {node : Node Atom} {children : List (Node Atom)}
    (rule : VariableJump.Rule semantics atomSupport node children) :
    (∃ child, children = [child]) ∨
      (∃ left right, children = [left, right]) := by
  cases rule with
  | expand notRejected expansion =>
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
  | jump => exact Or.inl ⟨_, rfl⟩

end VariableJump.Rule

namespace VariableJump

variable {Atom : Type u} {Var : Type w} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom} {atomSupport : Atom → Finset Var}

/-- Accessibility constructs a finite fully developed variable-aware tree. -/
theorem exists_wellFormed_terminal_of_accessible {node : Node Atom}
    (accessible : Acc (VariableJump.Child semantics atomSupport) node) :
    ∃ tree : TableauTree Atom,
      tree.root = node ∧
        VariableJump.TreeWellFormed semantics atomSupport tree ∧
          tree.FrontierTerminal semantics :=
  TableauTree.exists_wellFormed_terminal_of_accessible_with
    (VariableJump.Rule semantics atomSupport)
    (VariableJump.terminal_or_rule semantics atomSupport)
    (fun rule ↦ rule.children_shape) accessible

end VariableJump

namespace VariableJump.Development

variable {Atom : Type u} {Var : Type w} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom} {formula : Stlsat.Formula Atom}

/-- Every strict-normal formula has a finite variable-aware JUMP tableau. -/
theorem exists_of_strictNormalForm
    (atomSupport : Atom → Finset Var)
    (normal : formula.InStrictNormalForm) :
    Nonempty (VariableJump.Development semantics atomSupport formula) := by
  rcases VariableJump.exists_wellFormed_terminal_of_accessible
      (VariableJump.child_initial_accessible semantics atomSupport formula) with
    ⟨tree, rooted, wellFormed, terminal⟩
  exact ⟨⟨tree, normal, rooted, wellFormed, terminal⟩⟩

/-- Existence of a finite optimized tableau whose acceptance is exactly STL
satisfiability. -/
theorem exists_hasAcceptingBranch_iff_satisfiable
    [DecidableEq Var]
    (support : AtomicSupport semantics Var)
    (normal : formula.InStrictNormalForm) :
    ∃ tableau : VariableJump.Development semantics support.atomSupport formula,
      tableau.HasAcceptingBranch ↔ formula.Satisfiable semantics := by
  rcases exists_of_strictNormalForm support.atomSupport normal with ⟨tableau⟩
  exact ⟨tableau, tableau.soundness support, tableau.completeness support⟩

/-- Conservative and variable-aware developed JUMP tableaux agree on
acceptance through their common semantic specification. -/
theorem hasAcceptingBranch_iff_conservative
    [DecidableEq Var]
    (support : AtomicSupport semantics Var)
    (tableau : VariableJump.Development semantics support.atomSupport formula)
    (conservative : Jump.Development semantics formula) :
    tableau.HasAcceptingBranch ↔ conservative.HasAcceptingBranch := by
  constructor
  · intro optimizedAccepts
    exact conservative.completeness (tableau.soundness support optimizedAccepts)
  · intro conservativeAccepts
    exact tableau.completeness support (conservative.soundness conservativeAccepts)

/-- Basic and variable-aware JUMP tableaux agree on acceptance. -/
theorem hasAcceptingBranch_iff_basic
    [DecidableEq Var]
    (support : AtomicSupport semantics Var)
    (tableau : VariableJump.Development semantics support.atomSupport formula)
    (basic : Basic.Development semantics formula) :
    tableau.HasAcceptingBranch ↔ basic.HasAcceptingBranch := by
  constructor
  · intro optimizedAccepts
    exact basic.completeness (tableau.soundness support optimizedAccepts)
  · intro basicAccepts
    exact tableau.completeness support (basic.soundness basicAccepts)

end VariableJump.Development

end Stlsat.Tableau
