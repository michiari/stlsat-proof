/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.Completeness
import Stlsat.Jump.Variable.CompletenessSplicing

/-!
# Completeness of the variable-aware JUMP tableau

Ordinary expansion choices and target-escape routing are shared with the
conservative JUMP tableau.  The only new case is a JUMP edge: the
variable-aware completeness guard and `AtomicSupport.amalgamate` splice a
skipped target into the current model.
-/

namespace Stlsat.Tableau

universe u w

namespace VariableJump.Rule

variable {Atom : Type u} [DecidableEq Atom]
  {Var : Type w} [DecidableEq Var]
  {semantics : Stlsat.AtomicSemantics Atom}

/-- Model-guided progress through a unary variable-aware rule. -/
theorem unaryProgress
    (support : AtomicSupport semantics Var)
    {node child : Node Atom}
    (rule : VariableJump.Rule semantics support.atomSupport node [child])
    (derivation : node.FullDerivationValid) (timely : node.Timely)
    (normal : node.InStrictNormalForm) (model : node.HasModel semantics) :
    Nonempty (node.TargetEscape semantics) ∨
      Jump.Rule.UnaryProgress semantics node child := by
  have childMem : child ∈ [child] := by simp
  cases rule with
  | expand notRejected expansion =>
      rcases expansion.exists_child_hasModel model with
        ⟨modeled, modeledMem, childModel⟩
      simp only [List.mem_singleton] at modeledMem
      subst modeled
      right
      refine ⟨childModel, ?_⟩
      intro escape
      rcases expansion.targetEscape_parent_or_alternate childMem escape with
        parentEscape | sibling
      · exact parentEscape
      · cases sibling
  | step notRejected poised hasTemporal jumpDisabled =>
      right
      refine ⟨node.hasModel_step_of_hasModel poised timely model, ?_⟩
      intro escape
      exact False.elim (node.no_targetEscape_step semantics ⟨escape⟩)
  | jump notRejected poised hasTemporal sound complete size computed =>
      rcases model with ⟨sourceModel⟩
      rcases node.hasModel_variableJump_or_targetEscape support computed derivation timely
          poised normal complete sourceModel with childModel | parentEscape
      · right
        refine ⟨childModel, ?_⟩
        intro escape
        exact False.elim (node.no_targetEscape_jump size semantics ⟨escape⟩)
      · exact Or.inl parentEscape

/-- Model-guided progress through a binary variable-aware rule.  Binary
rules are ordinary formula expansions, so this is the shared argument. -/
theorem binaryProgress
    (support : AtomicSupport semantics Var)
    {node left right : Node Atom}
    (rule : VariableJump.Rule semantics support.atomSupport node [left, right])
    (model : node.HasModel semantics) :
    Jump.Rule.BinaryProgress semantics node left right := by
  cases rule with
  | expand notRejected expansion =>
      rcases expansion.exists_child_hasModel model with
        ⟨modeled, modeledMem, childModel⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at modeledMem
      rcases modeledMem with rfl | rfl
      · exact .left childModel
          (fun escape => expansion.targetEscape_parent_or_alternate (by simp) escape)
      · exact .right childModel
          (fun escape => expansion.targetEscape_parent_or_alternate (by simp) escape)

end VariableJump.Rule

namespace TableauTree

variable {Atom : Type u} [DecidableEq Atom]
  {Var : Type w} [DecidableEq Var]
  {semantics : Stlsat.AtomicSemantics Atom}

/-- Model-guided completeness for a finite variable-aware tableau tree,
with the same phase-local target-escape alternative as the conservative
development. -/
theorem accepting_or_variableTargetEscape
    (support : AtomicSupport semantics Var)
    (tree : TableauTree Atom)
    (wellFormed : VariableJump.TreeWellFormed semantics support.atomSupport tree)
    (frontierTerminal : tree.FrontierTerminal semantics)
    (timely : tree.root.Timely) (normal : tree.root.InStrictNormalForm)
    (derivation : tree.root.FullDerivationValid)
    (model : tree.root.HasModel semantics) :
    tree.HasAcceptingLeaf semantics ∨
      Nonempty (tree.root.TargetEscape semantics) := by
  induction tree with
  | leaf node =>
      left
      simp only [HasAcceptingLeaf]
      simp only [FrontierTerminal] at frontierTerminal
      rcases frontierTerminal with rejected | accepting
      · exact False.elim
          (Stlsat.ObligationSet.notRejected_of_hasModel model rejected)
      · exact accepting
  | unary node child ih =>
      rcases wellFormed with ⟨rule, childWellFormed⟩
      have childMem : child.root ∈ [child.root] := by simp
      have childTimely := rule.child_timely timely childMem
      have childNormal := rule.child_normal normal childMem
      have childDerivation := rule.child_fullDerivationValid derivation childMem
      rcases rule.unaryProgress support derivation timely normal model with
        parentEscape | progress
      · exact Or.inr parentEscape
      · rcases ih childWellFormed frontierTerminal childTimely childNormal
            childDerivation progress.model with accepting | childEscape
        · exact Or.inl accepting
        · rcases childEscape with ⟨childEscape⟩
          exact Or.inr (progress.escapeLifts childEscape)
  | binary node satisfy postpone ihSatisfy ihPostpone =>
      rcases wellFormed with
        ⟨rule, satisfyWellFormed, postponeWellFormed⟩
      rcases frontierTerminal with ⟨satisfyTerminal, postponeTerminal⟩
      have satisfyMem : satisfy.root ∈ [satisfy.root, postpone.root] := by simp
      have postponeMem : postpone.root ∈ [satisfy.root, postpone.root] := by simp
      have satisfyTimely := rule.child_timely timely satisfyMem
      have satisfyNormal := rule.child_normal normal satisfyMem
      have satisfyDerivation := rule.child_fullDerivationValid derivation satisfyMem
      have postponeTimely := rule.child_timely timely postponeMem
      have postponeNormal := rule.child_normal normal postponeMem
      have postponeDerivation := rule.child_fullDerivationValid derivation postponeMem
      cases rule.binaryProgress support model with
      | left childModel route =>
          rcases ihSatisfy satisfyWellFormed satisfyTerminal satisfyTimely
              satisfyNormal satisfyDerivation childModel with accepting | childEscape
          · exact Or.inl (Or.inl accepting)
          · rcases childEscape with ⟨childEscape⟩
            rcases route childEscape with parentEscape | sibling
            · exact Or.inr parentEscape
            · rcases sibling.other_of_left with ⟨siblingModel, escapeLifts⟩
              rcases ihPostpone postponeWellFormed postponeTerminal postponeTimely
                  postponeNormal postponeDerivation siblingModel with
                siblingAccepting | siblingEscape
              · exact Or.inl (Or.inr siblingAccepting)
              · rcases siblingEscape with ⟨siblingEscape⟩
                exact Or.inr (escapeLifts siblingEscape)
      | right childModel route =>
          rcases ihPostpone postponeWellFormed postponeTerminal postponeTimely
              postponeNormal postponeDerivation childModel with accepting | childEscape
          · exact Or.inl (Or.inr accepting)
          · rcases childEscape with ⟨childEscape⟩
            rcases route childEscape with parentEscape | sibling
            · exact Or.inr parentEscape
            · rcases sibling.other_of_right with ⟨siblingModel, escapeLifts⟩
              rcases ihSatisfy satisfyWellFormed satisfyTerminal satisfyTimely
                  satisfyNormal satisfyDerivation siblingModel with
                siblingAccepting | siblingEscape
              · exact Or.inl (Or.inl siblingAccepting)
              · rcases siblingEscape with ⟨siblingEscape⟩
                exact Or.inr (escapeLifts siblingEscape)

end TableauTree

namespace VariableJump.Development

variable {Atom : Type u} [DecidableEq Atom]
  {Var : Type w} [DecidableEq Var]
  {semantics : Stlsat.AtomicSemantics Atom}
  {formula : Stlsat.Formula Atom}

/-- A model of the input selects an accepting branch in every fully
developed variable-aware JUMP tableau. -/
theorem hasAcceptingBranch_of_hasModel
    (support : AtomicSupport semantics Var)
    (tableau : VariableJump.Development semantics support.atomSupport formula)
    (model : formula.HasModel semantics) : tableau.HasAcceptingBranch := by
  have rootTimely : tableau.tree.root.Timely := by
    rw [tableau.rooted_at]
    exact Node.initial_timely formula
  have rootNormal : tableau.tree.root.InStrictNormalForm := by
    rw [tableau.rooted_at]
    exact Node.initial_normal tableau.root_normal
  have rootDerivation : tableau.tree.root.FullDerivationValid := by
    rw [tableau.rooted_at]
    exact Node.initial_fullDerivationValid formula
  have rootModel : tableau.tree.root.HasModel semantics := by
    change tableau.tree.root.erase.HasModel semantics
    rw [tableau.rooted_at, Node.erase_initial]
    exact model
  rcases TableauTree.accepting_or_variableTargetEscape support tableau.tree
      tableau.wellFormed tableau.frontier_terminal rootTimely rootNormal
      rootDerivation rootModel with accepted | escape
  · exact accepted
  · rw [tableau.rooted_at] at escape
    exact False.elim (Node.no_targetEscape_initial formula semantics escape)

/-- Completeness of the variable-aware JUMP tableau.  `AtomicSupport` is the
genuine semantic hypothesis permitting models over disjoint variable
supports to be combined. -/
theorem completeness
    (support : AtomicSupport semantics Var)
    (tableau : VariableJump.Development semantics support.atomSupport formula)
    (satisfiable : formula.Satisfiable semantics) :
    tableau.HasAcceptingBranch :=
  tableau.hasAcceptingBranch_of_hasModel support
    ((Stlsat.Formula.satisfiable_iff_hasModel formula semantics).mp satisfiable)

end VariableJump.Development

end Stlsat.Tableau
