/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.RankedSplicing

/-!
# Soundness of the JUMP tableau

This file assembles the semantic soundness proof for the corrected JUMP rule.
The technical modules below `RankedSplicing` show that the window guards can
splice a signal satisfying every invariant instance skipped by a JUMP.  The
local result is then propagated backwards along an accepting branch.
-/

namespace Stlsat.Jump
universe u

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

/-- The soundness window guard constructs a successor model which realizes every
strictly skipped invariant instance. -/
theorem soundnessGuardProvidesSkippedModel
    (semantics : Stlsat.AtomicSemantics Atom) {node : Node Atom} {size : Nat}
    (derivation : node.FullDerivationValid)
    (notRejected : ¬node.Rejected semantics) (poised : node.Poised)
    (sound : node.SoundSafe) (computed : node.jumpSize? = some size)
    (timely : node.Timely) (normal : node.InStrictNormalForm)
    (childHasModel : (node.jump size).HasModel semantics) :
    ∃ model : (node.jump size).Model semantics,
      node.SkippedInvariantsHold size semantics model.signal := by
  let childModel : (node.jump size).Model semantics := Classical.choice childHasModel
  rcases node.exists_baseSignal notRejected poised computed timely normal childModel with
    ⟨baseSignal, base⟩
  rcases node.exists_fullRankedHolds_with_skipped derivation poised timely normal computed
      sound base with ⟨signal, ranked, allSkipped⟩
  have childSatisfied : (node.jump size).SatisfiedBy semantics signal := by
    apply (satisfiedBy_iff (node.jump size) semantics signal).2
    intro child childMem
    change child ∈ node.jumpLabel size at childMem
    rcases Finset.mem_image.mp childMem with ⟨source, sourceFiltered, sourceEq⟩
    subst child
    rcases Finset.mem_filter.mp sourceFiltered with ⟨sourceMem, survives⟩
    have temporal : source.isTemporal = true := by
      cases source with
      | mk id payload parent =>
          cases payload with
          | unmarked formula =>
              cases formula with
              | truth => simp [Node.survivesJump, AnnotatedOccurrence.interval?] at survives
              | atom atom => simp [Node.survivesJump, AnnotatedOccurrence.interval?] at survives
              | neg body => simp [Node.survivesJump, AnnotatedOccurrence.interval?] at survives
              | and left right =>
                  simp [Node.survivesJump, AnnotatedOccurrence.interval?] at survives
              | or left right =>
                  simp [Node.survivesJump, AnnotatedOccurrence.interval?] at survives
              | eventually interval body =>
                  simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal,
                    Stlsat.Formula.isTemporal]
              | always interval body =>
                  simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal,
                    Stlsat.Formula.isTemporal]
              | strictUntil interval invariant target =>
                  simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal,
                    Stlsat.Formula.isTemporal]
              | strictRelease interval target invariant =>
                  simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal,
                    Stlsat.Formula.isTemporal]
          | markedEventually interval body =>
              simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal]
          | markedAlways interval body =>
              simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal]
          | markedStrictUntil interval invariant target =>
              simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal]
          | markedStrictRelease interval target invariant =>
              simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal]
    have atDestination := ranked.1.2 source sourceMem temporal
    simpa [Node.jump] using atDestination
  let model : (node.jump size).Model semantics := {
    signal := signal
    satisfies := childSatisfied }
  refine ⟨model, ?_⟩
  intro source sourceMem edge invariant shape instant after before
  let origin : node.SkippedOrigin size (node.maxFormulaRank + 1) := {
    source := source
    sourceMem := sourceMem
    edge := edge
    invariant := invariant
    shape := shape
    offset := instant - node.time
    positive := by omega
    skipped := by omega
    bounded := (node.formulaRank_le_maxFormulaRank source sourceMem).trans (by omega) }
  have supplied := allSkipped origin
  have instantEq : node.time + origin.offset = instant := by
    simp only [origin]
    omega
  simpa [model, instantEq] using supplied

/-- Backwards semantic preservation for a rule-generated guarded JUMP. -/
theorem hasModel_of_guardedJump
    (semantics : Stlsat.AtomicSemantics Atom) {node : Node Atom} {size : Nat}
    (derivation : node.FullDerivationValid)
    (notRejected : ¬node.Rejected semantics) (poised : node.Poised)
    (sound : node.SoundSafe) (computed : node.jumpSize? = some size)
    (timely : node.Timely) (normal : node.InStrictNormalForm)
    (childModel : (node.jump size).HasModel semantics) : node.HasModel semantics := by
  rcases node.soundnessGuardProvidesSkippedModel semantics derivation notRejected poised
      sound computed timely normal childModel with ⟨model, skipped⟩
  exact Node.hasModel_of_jump_of_model_of_skippedInvariants notRejected poised computed timely
    normal model skipped

end Node

namespace Rule

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom}

/-- Every tableau rule transports a child model back to its parent.  In the
JUMP case, derivation validity supplies the provenance needed by the window
argument. -/
theorem hasModel_parent_of_child
    {node child : Node Atom} {children : List (Node Atom)}
    (rule : Rule semantics node children) (derivation : node.FullDerivationValid)
    (timely : node.Timely) (normal : node.InStrictNormalForm)
    (childMem : child ∈ children) (childModel : child.HasModel semantics) :
    node.HasModel semantics := by
  cases rule with
  | expand notRejected expansion =>
      rcases childModel with ⟨⟨signal, childSatisfied⟩⟩
      exact ⟨⟨signal, expansion.satisfiedBy_parent childMem childSatisfied⟩⟩
  | step notRejected poised _ jumpDisabled =>
      simp only [List.mem_singleton] at childMem
      subst child
      exact Node.hasModel_of_step notRejected poised timely normal childModel
  | jump notRejected poised _ sound _ size computed =>
      simp only [List.mem_singleton] at childMem
      subst child
      exact Node.hasModel_of_guardedJump semantics derivation notRejected poised sound computed
        timely normal childModel

end Rule

namespace TableauTree

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom}

/-- Backward model construction on an accepted branch.  A simultaneous
forward induction carries derivation validity to every JUMP node. -/
theorem root_hasModel_of_acceptingLeaf
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
      exact rule.hasModel_parent_of_child derivation timely normal childMem childModel
  | binary node satisfy postpone ihSatisfy ihPostpone =>
      rcases wellFormed with ⟨rule, satisfyWellFormed, postponeWellFormed⟩
      rcases accepting with satisfyAccepting | postponeAccepting
      · have childMem : satisfy.root ∈ [satisfy.root, postpone.root] := by simp
        have childTimely := rule.child_timely timely childMem
        have childNormal := rule.child_normal normal childMem
        have childDerivation := rule.child_fullDerivationValid derivation childMem
        have childModel := ihSatisfy satisfyWellFormed satisfyAccepting childTimely childNormal
          childDerivation
        exact rule.hasModel_parent_of_child derivation timely normal childMem childModel
      · have childMem : postpone.root ∈ [satisfy.root, postpone.root] := by simp
        have childTimely := rule.child_timely timely childMem
        have childNormal := rule.child_normal normal childMem
        have childDerivation := rule.child_fullDerivationValid derivation childMem
        have childModel := ihPostpone postponeWellFormed postponeAccepting childTimely childNormal
          childDerivation
        exact rule.hasModel_parent_of_child derivation timely normal childMem childModel

end TableauTree

namespace Tableau

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom} {formula : Stlsat.Formula Atom}

/-- Soundness of the guarded JUMP tableau: every accepting branch yields a
semantic model of the input formula. -/
theorem soundness (tableau : Tableau semantics formula)
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
  have rootModel := TableauTree.root_hasModel_of_acceptingLeaf tableau.tree
    tableau.wellFormed accepted rootTimely rootNormal rootDerivation
  apply (Stlsat.Formula.satisfiable_iff_hasModel formula semantics).mpr
  change tableau.tree.root.erase.HasModel semantics at rootModel
  rw [tableau.rooted_at, Node.erase_initial] at rootModel
  exact rootModel

end Tableau
end Stlsat.Jump
