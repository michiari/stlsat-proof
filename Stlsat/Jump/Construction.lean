/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.Completeness
import Stlsat.Jump.Soundness
import Stlsat.Jump.Termination
import Stlsat.Tableau.Basic.Completeness
import Stlsat.Tableau.Construction

/-!
# Existence of the STL tableau with JUMP

Every strict-normal-form input has a finite, fully developed tableau.  The
construction is classical only because the atomic semantics exposes its
satisfaction relation as a proposition without a decidability assumption.

The `Rule` type makes the scheduling policy intrinsic: at a poised temporal
node, `STEP` requires `¬CanJump`, whereas `JUMP` carries all three components
of `CanJump`.  Thus the constructed tableau uses JUMP whenever it is
applicable according to the formalized guards.
-/

namespace Stlsat.Tableau

universe u

namespace Jump

variable {Atom : Type u} [DecidableEq Atom]

/-- A node is terminal, or one of the formal tableau rules is applicable.
The JUMP case is selected precisely when `CanJump` holds. -/
theorem terminal_or_rule (semantics : Stlsat.AtomicSemantics Atom)
    (node : Node Atom) :
    node.Terminal semantics ∨ ∃ children, Jump.Rule semantics node children := by
  classical
  by_cases rejected : node.Rejected semantics
  · exact Or.inl (Or.inl rejected)
  by_cases expandable : ∃ children, Expansion node children
  · rcases expandable with ⟨children, expansion⟩
    exact Or.inr ⟨children, Jump.Rule.expand rejected expansion⟩
  have poised : node.Poised := expandable
  by_cases temporal : node.ContainsTemporal
  · by_cases canJump : node.CanJump
    · rcases canJump with ⟨sound, complete, size, computed⟩
      exact Or.inr ⟨[node.jump size],
        Jump.Rule.jump rejected poised temporal sound complete size computed⟩
    · exact Or.inr ⟨[node.step], Jump.Rule.step rejected poised temporal canJump⟩
  · exact Or.inl (Or.inr ⟨poised, rejected,
      node.stepLabel_eq_empty_of_not_containsTemporal temporal⟩)

end Jump

namespace Jump.Rule

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom}

/-- Every rule has exactly one or two children, matching `TableauTree`. -/
theorem children_shape {node : Node Atom} {children : List (Node Atom)}
    (rule : Jump.Rule semantics node children) :
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

end Jump.Rule

namespace Jump

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom}

/-- Accessibility for the full rule relation constructs a finite tree whose
frontier is completely developed. -/
theorem exists_wellFormed_terminal_of_accessible {node : Node Atom}
    (accessible : Acc (Jump.Child semantics) node) :
    ∃ tree : TableauTree Atom,
      tree.root = node ∧ Jump.TreeWellFormed semantics tree ∧
        tree.FrontierTerminal semantics :=
  TableauTree.exists_wellFormed_terminal_of_accessible_with
    (Jump.Rule semantics) (Jump.terminal_or_rule semantics)
    (fun rule => rule.children_shape) accessible

end Jump

namespace Jump.Development

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom} {formula : Stlsat.Formula Atom}

/-- Every strict-normal-form STL formula has a finite, fully developed tableau
which employs JUMP whenever the formal rule permits it. -/
theorem exists_of_strictNormalForm (normal : formula.InStrictNormalForm) :
    Nonempty (Jump.Development semantics formula) := by
  rcases Jump.exists_wellFormed_terminal_of_accessible
      (Jump.child_initial_accessible semantics formula) with
    ⟨tree, rooted, wellFormed, terminal⟩
  exact ⟨⟨tree, normal, rooted, wellFormed, terminal⟩⟩

/-- Every strict-normal-form formula has a fully developed JUMP tableau whose
acceptance is equivalent to satisfiability. -/
theorem exists_hasAcceptingBranch_iff_satisfiable
    (normal : formula.InStrictNormalForm) :
    ∃ tableau : Jump.Development semantics formula,
      tableau.HasAcceptingBranch ↔ formula.Satisfiable semantics := by
  rcases exists_of_strictNormalForm normal with ⟨tableau⟩
  exact ⟨tableau, Jump.Development.soundness tableau,
    Jump.Development.completeness tableau⟩

/-- Any fully developed basic and JUMP tableaux for the same input agree on
acceptance.  This is the formal correspondence stated in the paper, obtained
through their shared semantic specification. -/
theorem hasAcceptingBranch_iff_basic
    (tableau : Jump.Development semantics formula)
    (basic : Basic.Development semantics formula) :
    tableau.HasAcceptingBranch ↔ basic.HasAcceptingBranch := by
  constructor
  · intro jumpAccepts
    exact basic.completeness (Jump.Development.soundness tableau jumpAccepts)
  · intro basicAccepts
    exact Jump.Development.completeness tableau (basic.soundness basicAccepts)

/-- For every fully developed basic tableau, there is a fully developed JUMP
tableau which accepts exactly when the basic tableau accepts. -/
theorem exists_hasAcceptingBranch_iff_basic
    (basic : Basic.Development semantics formula) :
    ∃ tableau : Jump.Development semantics formula,
      tableau.HasAcceptingBranch ↔ basic.HasAcceptingBranch := by
  rcases exists_of_strictNormalForm basic.root_normal with ⟨tableau⟩
  exact ⟨tableau, tableau.hasAcceptingBranch_iff_basic basic⟩

end Jump.Development

end Stlsat.Tableau
