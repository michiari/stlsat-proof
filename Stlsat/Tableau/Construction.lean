/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Tableau.Core

/-!
# Shared finite tableau construction

Given a rule configuration with terminal-or-successor progress, unary/binary
branching, and accessibility of its child relation, this module constructs a
finite fully developed tree.  Basic and JUMP tableaux instantiate the same
induction with their respective advancement rules.
-/

namespace Stlsat.Tableau.TableauTree

universe u

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom}

/-- Construct a fully developed finite tree for any accessible configured
rule relation whose applications have the raw tree's unary/binary shape. -/
theorem exists_wellFormed_terminal_of_accessible_with
    (rules : Node Atom → List (Node Atom) → Prop)
    (progress : ∀ node, node.Terminal semantics ∨ ∃ children, rules node children)
    (childrenShape : ∀ {node children}, rules node children →
      (∃ child, children = [child]) ∨
        (∃ left right, children = [left, right]))
    {node : Node Atom} (accessible : Acc (Child rules) node) :
    ∃ tree : TableauTree Atom,
      tree.root = node ∧ tree.WellFormedWith rules ∧
        tree.FrontierTerminal semantics := by
  induction accessible with
  | intro node predecessors ih =>
      rcases progress node with terminal | ⟨children, rule⟩
      · exact ⟨.leaf node, rfl, trivial, terminal⟩
      · rcases childrenShape rule with ⟨child, rfl⟩ | ⟨left, right, rfl⟩
        · have childOf : Child rules child node :=
            ⟨[child], rule, by simp⟩
          rcases ih child childOf with
            ⟨childTree, childRoot, childWellFormed, childTerminal⟩
          refine ⟨.unary node childTree, rfl, ?_, childTerminal⟩
          exact ⟨by simpa [childRoot] using rule, childWellFormed⟩
        · have leftOf : Child rules left node :=
            ⟨[left, right], rule, by simp⟩
          have rightOf : Child rules right node :=
            ⟨[left, right], rule, by simp⟩
          rcases ih left leftOf with
            ⟨leftTree, leftRoot, leftWellFormed, leftTerminal⟩
          rcases ih right rightOf with
            ⟨rightTree, rightRoot, rightWellFormed, rightTerminal⟩
          refine ⟨.binary node leftTree rightTree, rfl, ?_,
            ⟨leftTerminal, rightTerminal⟩⟩
          exact ⟨by simpa [leftRoot, rightRoot] using rule,
            leftWellFormed, rightWellFormed⟩

end Stlsat.Tableau.TableauTree
