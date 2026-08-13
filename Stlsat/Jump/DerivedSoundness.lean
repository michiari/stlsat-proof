/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.Canonical

/-!
# Derivation-aware JUMP soundness

The model argument for a JUMP is needed only at nodes derived from the initial
formula.  This file threads the corresponding provenance/activity invariant
through the global tableau induction and isolates the remaining semantic
signal-construction statement.
-/

namespace Stlsat.Jump
universe u

/-- The window guards provide a successor model whose signal also realizes
every strictly skipped invariant instance.  Unlike `JumpModelPreserving`, this
statement is restricted to nodes carrying the rule-generated provenance
invariant. -/
def WindowGuardsProvideSkippedModel {Atom : Type u} [DecidableEq Atom]
    (semantics : Stlsat.AtomicSemantics Atom) : Prop :=
  ∀ {node : Node Atom} {size : Nat},
    node.FullDerivationValid →
      ¬node.Rejected semantics → node.Poised → node.ContainsTemporal →
        node.SoundSafe → node.CompleteSafe → node.jumpSize? = some size →
          node.Timely → node.InStrictNormalForm →
            (node.jump size).HasModel semantics →
              ∃ model : (node.jump size).Model semantics,
                node.SkippedInvariantsHold size semantics model.signal

/-- Once the guarded signal has been constructed, the local semantic
transport theorem discharges a derived JUMP. -/
theorem derivedJumpModelPreserving_of_windowGuardsProvideSkippedModel
    {Atom : Type u} [DecidableEq Atom]
    {semantics : Stlsat.AtomicSemantics Atom}
    (provides : WindowGuardsProvideSkippedModel semantics)
    {node : Node Atom} {size : Nat} (derivation : node.FullDerivationValid)
    (notRejected : ¬node.Rejected semantics) (poised : node.Poised)
    (hasTemporal : node.ContainsTemporal) (sound : node.SoundSafe)
    (complete : node.CompleteSafe) (computed : node.jumpSize? = some size)
    (timely : node.Timely) (normal : node.InStrictNormalForm)
    (childModel : (node.jump size).HasModel semantics) : node.HasModel semantics := by
  rcases provides derivation notRejected poised hasTemporal sound complete computed timely
      normal childModel with ⟨model, skipped⟩
  exact Node.hasModel_of_jump_of_model_of_skippedInvariants notRejected poised computed timely
    normal model skipped

namespace Rule

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom}

theorem hasModel_parent_of_child_of_windowGuardsProvideSkippedModel
    (provides : WindowGuardsProvideSkippedModel semantics)
    {node child : Node Atom} {children : List (Node Atom)}
    (rule : Rule semantics node children) (derivation : node.FullDerivationValid)
    (timely : node.Timely) (normal : node.InStrictNormalForm)
    (childMem : child ∈ children) (childModel : child.HasModel semantics) :
    node.HasModel semantics := by
  cases rule with
  | expand notRejected expansion =>
      rcases childModel with ⟨⟨signal, childSatisfied⟩⟩
      exact ⟨⟨signal, expansion.satisfiedBy_parent childMem childSatisfied⟩⟩
  | step notRejected poised hasTemporal jumpDisabled =>
      simp only [List.mem_singleton] at childMem
      subst child
      exact Node.hasModel_of_step notRejected poised timely normal childModel
  | jump notRejected poised hasTemporal sound complete size computed =>
      simp only [List.mem_singleton] at childMem
      subst child
      exact derivedJumpModelPreserving_of_windowGuardsProvideSkippedModel provides derivation
        notRejected poised hasTemporal sound complete computed timely normal childModel

end Rule

namespace TableauTree

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom}

/-- Backward model construction on an accepted branch, while a simultaneous
forward induction carries the derivation invariant to every JUMP node. -/
theorem root_hasModel_of_acceptingLeaf_of_windowGuardsProvideSkippedModel
    (provides : WindowGuardsProvideSkippedModel semantics)
    (tree : TableauTree Atom) (wellFormed : tree.WellFormed semantics)
    (accepting : tree.HasAcceptingLeaf semantics)
    (timely : tree.root.Timely) (normal : tree.root.InStrictNormalForm)
    (derivation : tree.root.FullDerivationValid) : tree.root.HasModel semantics := by
  induction tree with
  | leaf node => exact Node.hasModel_of_accepting accepting timely normal
  | unary node child ih =>
      rcases wellFormed with ⟨rule, childWellFormed⟩
      have childMem : child.root ∈ [child.root] := by simp
      have childTimely := rule.child_timely timely childMem
      have childNormal := rule.child_normal normal childMem
      have childDerivation := rule.child_fullDerivationValid derivation childMem
      have childModel := ih childWellFormed accepting childTimely childNormal childDerivation
      exact rule.hasModel_parent_of_child_of_windowGuardsProvideSkippedModel provides derivation
        timely normal childMem childModel
  | binary node satisfy postpone ihSatisfy ihPostpone =>
      rcases wellFormed with ⟨rule, satisfyWellFormed, postponeWellFormed⟩
      rcases accepting with satisfyAccepting | postponeAccepting
      · have childMem : satisfy.root ∈ [satisfy.root, postpone.root] := by simp
        have childTimely := rule.child_timely timely childMem
        have childNormal := rule.child_normal normal childMem
        have childDerivation := rule.child_fullDerivationValid derivation childMem
        have childModel := ihSatisfy satisfyWellFormed satisfyAccepting childTimely childNormal
          childDerivation
        exact rule.hasModel_parent_of_child_of_windowGuardsProvideSkippedModel provides derivation
          timely normal childMem childModel
      · have childMem : postpone.root ∈ [satisfy.root, postpone.root] := by simp
        have childTimely := rule.child_timely timely childMem
        have childNormal := rule.child_normal normal childMem
        have childDerivation := rule.child_fullDerivationValid derivation childMem
        have childModel := ihPostpone postponeWellFormed postponeAccepting childTimely childNormal
          childDerivation
        exact rule.hasModel_parent_of_child_of_windowGuardsProvideSkippedModel provides derivation
          timely normal childMem childModel

end TableauTree

namespace Tableau

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom} {formula : Stlsat.Formula Atom}

/-- Global soundness reduced to the concrete guarded signal-construction
statement, with reachability discharged internally. -/
theorem soundness_of_windowGuardsProvideSkippedModel
    (tableau : Tableau semantics formula)
    (provides : WindowGuardsProvideSkippedModel semantics)
    (accepted : tableau.HasAcceptingBranch) : formula.Satisfiable semantics := by
  have rootTimely : tableau.tree.root.Timely := by
    rw [tableau.rooted_at]
    exact Node.initial_timely formula
  have rootNormal : tableau.tree.root.InStrictNormalForm := by
    rw [tableau.rooted_at]
    exact Node.initial_normal tableau.root_normal
  have rootDerivation : tableau.tree.root.FullDerivationValid := by
    rw [tableau.rooted_at]
    exact Node.initial_fullDerivationValid formula
  have rootModel :=
    TableauTree.root_hasModel_of_acceptingLeaf_of_windowGuardsProvideSkippedModel
      provides tableau.tree tableau.wellFormed accepted rootTimely rootNormal rootDerivation
  apply (Stlsat.Formula.satisfiable_iff_hasModel formula semantics).mpr
  change tableau.tree.root.erase.HasModel semantics at rootModel
  rw [tableau.rooted_at, Node.erase_initial] at rootModel
  exact rootModel

end Tableau

/-!
The premise isolated in this module is discharged constructively in
`Stlsat.Jump.UnconditionalSoundness`.  That proof records expansion frontiers,
splices compatible signed-leaf requirements, and iterates the construction by
structural formula rank.
-/

end Stlsat.Jump
