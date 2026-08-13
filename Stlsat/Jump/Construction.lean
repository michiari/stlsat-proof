/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.Termination

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

namespace Stlsat.Jump

universe u

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

/-- Every occurrence retained by `STEP` comes from a temporal occurrence in
the source label. -/
theorem containsTemporal_of_mem_stepLabel {node : Node Atom}
    {occurrence : AnnotatedOccurrence Atom} (present : occurrence ∈ node.stepLabel) :
    node.ContainsTemporal := by
  rcases Finset.mem_union.mp present with unchanged | continued
  · rcases Finset.mem_filter.mp unchanged with ⟨sourceMem, temporal⟩
    refine ⟨occurrence, sourceMem, ?_⟩
    cases occurrence with
    | mk id payload parent =>
        cases payload <;>
          simp_all [AnnotatedOccurrence.isUnmarkedTemporal,
            Stlsat.Occurrence.isUnmarkedTemporal,
            AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal,
            Stlsat.Formula.isTemporal]
  · rcases Finset.mem_image.mp continued with ⟨source, sourceFiltered, rfl⟩
    rcases Finset.mem_filter.mp sourceFiltered with ⟨sourceMem, continues⟩
    refine ⟨source, sourceMem, ?_⟩
    cases source with
    | mk id payload parent =>
        cases payload <;>
          simp_all [AnnotatedOccurrence.markedContinuesAt,
            Stlsat.Occurrence.markedContinuesAt,
            AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal]

theorem stepLabel_eq_empty_of_not_containsTemporal {node : Node Atom}
    (absent : ¬node.ContainsTemporal) : node.stepLabel = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro occurrence present
  exact absent (containsTemporal_of_mem_stepLabel present)

/-- A node is terminal, or one of the formal tableau rules is applicable.
The JUMP case is selected precisely when `CanJump` holds. -/
theorem terminal_or_rule (semantics : Stlsat.AtomicSemantics Atom)
    (node : Node Atom) :
    node.Terminal semantics ∨ ∃ children, Rule semantics node children := by
  classical
  by_cases rejected : node.Rejected semantics
  · exact Or.inl (Or.inl rejected)
  by_cases expandable : ∃ children, Expansion node children
  · rcases expandable with ⟨children, expansion⟩
    exact Or.inr ⟨children, Rule.expand rejected expansion⟩
  have poised : node.Poised := expandable
  by_cases temporal : node.ContainsTemporal
  · by_cases canJump : node.CanJump
    · rcases canJump with ⟨sound, complete, size, computed⟩
      exact Or.inr ⟨[node.jump size],
        Rule.jump rejected poised temporal sound complete size computed⟩
    · exact Or.inr ⟨[node.step], Rule.step rejected poised temporal canJump⟩
  · exact Or.inl (Or.inr ⟨poised, rejected,
      node.stepLabel_eq_empty_of_not_containsTemporal temporal⟩)

end Node

namespace Rule

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom}

/-- Every rule has exactly one or two children, matching `TableauTree`. -/
theorem children_shape {node : Node Atom} {children : List (Node Atom)}
    (rule : Rule semantics node children) :
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

end Rule

namespace TableauTree

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom}

/-- Accessibility for the full rule relation constructs a finite tree whose
frontier is completely developed. -/
theorem exists_wellFormed_terminal_of_accessible {node : Node Atom}
    (accessible : Acc (JumpChild semantics) node) :
    ∃ tree : TableauTree Atom,
      tree.root = node ∧ tree.WellFormed semantics ∧
        tree.FrontierTerminal semantics := by
  induction accessible with
  | intro node predecessors ih =>
      rcases node.terminal_or_rule semantics with terminal | ⟨children, rule⟩
      · exact ⟨.leaf node, rfl, trivial, terminal⟩
      · rcases rule.children_shape with ⟨child, rfl⟩ | ⟨left, right, rfl⟩
        · have childOf : JumpChild semantics child node :=
            ⟨[child], rule, by simp⟩
          rcases ih child childOf with
            ⟨childTree, childRoot, childWellFormed, childTerminal⟩
          refine ⟨.unary node childTree, rfl, ?_, childTerminal⟩
          exact ⟨by simpa [childRoot] using rule, childWellFormed⟩
        · have leftOf : JumpChild semantics left node :=
            ⟨[left, right], rule, by simp⟩
          have rightOf : JumpChild semantics right node :=
            ⟨[left, right], rule, by simp⟩
          rcases ih left leftOf with
            ⟨leftTree, leftRoot, leftWellFormed, leftTerminal⟩
          rcases ih right rightOf with
            ⟨rightTree, rightRoot, rightWellFormed, rightTerminal⟩
          refine ⟨.binary node leftTree rightTree, rfl, ?_,
            ⟨leftTerminal, rightTerminal⟩⟩
          exact ⟨by simpa [leftRoot, rightRoot] using rule,
            leftWellFormed, rightWellFormed⟩

end TableauTree

namespace Tableau

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom} {formula : Stlsat.Formula Atom}

/-- Every strict-normal-form STL formula has a finite, fully developed tableau
which employs JUMP whenever the formal rule permits it. -/
theorem exists_of_strictNormalForm (normal : formula.InStrictNormalForm) :
    Nonempty (Tableau semantics formula) := by
  rcases TableauTree.exists_wellFormed_terminal_of_accessible
      (jumpChild_initial_accessible semantics formula) with
    ⟨tree, rooted, wellFormed, terminal⟩
  exact ⟨⟨tree, normal, rooted, wellFormed, terminal⟩⟩

end Tableau

end Stlsat.Jump
