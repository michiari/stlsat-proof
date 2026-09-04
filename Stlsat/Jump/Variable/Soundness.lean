/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.Variable.Splicing
import Stlsat.Jump.Soundness

/-! # Soundness of variable-aware JUMP -/

namespace Stlsat.Tableau

universe u w

namespace Node

variable {Atom : Type u} [DecidableEq Atom]
  {Var : Type w} [DecidableEq Var]

/-- Variable-aware support splicing constructs a successor model realizing
every invariant instance skipped by the JUMP. -/
theorem variableSoundnessGuardProvidesSkippedModel
    (semantics : Stlsat.AtomicSemantics Atom)
    (support : AtomicSupport semantics Var)
    {node : Node Atom} {size : Nat}
    (derivation : node.FullDerivationValid)
    (notRejected : ¬node.Rejected semantics) (poised : node.Poised)
    (sound : node.VariableSoundSafe support.atomSupport)
    (computed : node.variableJumpSize? support.atomSupport = some size)
    (timely : node.Timely) (normal : node.InStrictNormalForm)
    (childHasModel : (node.jump size).HasModel semantics) :
    ∃ model : (node.jump size).Model semantics,
      node.SkippedInvariantsHold size semantics model.signal := by
  let childModel : (node.jump size).Model semantics := Classical.choice childHasModel
  rcases node.exists_baseSignal_of_admissible notRejected poised
      (node.variableJumpSizeAdmissible support.atomSupport computed) timely normal childModel with
    ⟨baseSignal, base⟩
  rcases node.exists_fullVariableRankedHolds_with_skipped support derivation poised timely
      normal computed sound base with ⟨signal, ranked, allSkipped⟩
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

/-- Backward semantic preservation for one variable-aware JUMP. -/
theorem hasModel_of_variableGuardedJump
    (semantics : Stlsat.AtomicSemantics Atom)
    (support : AtomicSupport semantics Var)
    {node : Node Atom} {size : Nat}
    (derivation : node.FullDerivationValid)
    (notRejected : ¬node.Rejected semantics) (poised : node.Poised)
    (sound : node.VariableSoundSafe support.atomSupport)
    (computed : node.variableJumpSize? support.atomSupport = some size)
    (timely : node.Timely) (normal : node.InStrictNormalForm)
    (childModel : (node.jump size).HasModel semantics) : node.HasModel semantics := by
  rcases node.variableSoundnessGuardProvidesSkippedModel semantics support derivation
      notRejected poised sound computed timely normal childModel with ⟨model, skipped⟩
  exact Node.hasModel_of_jump_of_model_of_skippedInvariants_of_admissible notRejected poised
    (node.variableJumpSizeAdmissible support.atomSupport computed) timely normal model skipped

end Node

namespace VariableJump.Rule

variable {Atom : Type u} [DecidableEq Atom]
  {Var : Type w} [DecidableEq Var]
  {semantics : Stlsat.AtomicSemantics Atom} {atomSupport : Atom → Finset Var}

omit [DecidableEq Var] in
theorem child_normal {node child : Node Atom} {children : List (Node Atom)}
    (rule : VariableJump.Rule semantics atomSupport node children)
    (normal : node.InStrictNormalForm) (childMem : child ∈ children) :
    child.InStrictNormalForm := by
  cases rule with
  | expand notRejected expansion => exact expansion.child_normal normal childMem
  | step notRejected poised hasTemporal jumpDisabled =>
      simp only [List.mem_singleton] at childMem
      subst child
      exact Node.step_normal normal
  | jump notRejected poised hasTemporal sound complete size computed =>
      simp only [List.mem_singleton] at childMem
      subst child
      exact Node.jump_normal node size normal

omit [DecidableEq Var] in
theorem child_timely {node child : Node Atom} {children : List (Node Atom)}
    (rule : VariableJump.Rule semantics atomSupport node children)
    (timely : node.Timely) (childMem : child ∈ children) : child.Timely := by
  cases rule with
  | expand notRejected expansion => exact expansion.child_timely timely childMem
  | step notRejected poised hasTemporal jumpDisabled =>
      simp only [List.mem_singleton] at childMem
      subst child
      exact Node.step_timely timely poised
  | jump notRejected poised hasTemporal sound complete size computed =>
      simp only [List.mem_singleton] at childMem
      subst child
      exact Node.jump_timely node size

omit [DecidableEq Var] in
theorem child_fullDerivationValid {node child : Node Atom}
    {children : List (Node Atom)}
    (rule : VariableJump.Rule semantics atomSupport node children)
    (valid : node.FullDerivationValid) (childMem : child ∈ children) :
    child.FullDerivationValid := by
  cases rule with
  | expand notRejected expansion =>
      exact (Jump.Rule.expand notRejected expansion).child_fullDerivationValid valid childMem
  | step notRejected poised hasTemporal jumpDisabled =>
      have baselineDisabled : ¬node.CanJump := by
        intro canJump
        exact jumpDisabled (node.canVariableJump_of_canJump atomSupport canJump)
      let baselineRule :=
        Jump.Rule.step notRejected poised hasTemporal baselineDisabled
      exact baselineRule.child_fullDerivationValid valid childMem
  | jump notRejected poised hasTemporal sound complete size computed =>
      simp only [List.mem_singleton] at childMem
      subst child
      have provenance := Node.jump_provenanceValid size valid.1.1.1
      have marked := Node.jump_markedActive (node := node) size
      have planned := Node.jump_emissionsPlanned node size
      have canonical := Node.jump_canonicalLeavesValid size valid.2
      exact ⟨⟨⟨provenance, marked⟩, planned⟩, canonical⟩

/-- Every variable-aware tableau rule transports a child model back to its
parent. -/
theorem hasModel_parent_of_child
    (support : AtomicSupport semantics Var)
    {node child : Node Atom} {children : List (Node Atom)}
    (rule : VariableJump.Rule semantics support.atomSupport node children)
    (derivation : node.FullDerivationValid)
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
      exact Node.hasModel_of_variableGuardedJump semantics support derivation notRejected
        poised sound computed timely normal childModel

end VariableJump.Rule

namespace TableauTree

variable {Atom : Type u} [DecidableEq Atom]
  {Var : Type w} [DecidableEq Var]
  {semantics : Stlsat.AtomicSemantics Atom}

/-- Backward model construction along an accepting variable-aware branch. -/
theorem root_hasModel_of_variableAcceptingLeaf
    (support : AtomicSupport semantics Var)
    (tree : TableauTree Atom)
    (wellFormed : VariableJump.TreeWellFormed semantics support.atomSupport tree)
    (accepting : tree.HasAcceptingLeaf semantics)
    (timely : tree.root.Timely) (normal : tree.root.InStrictNormalForm)
    (derivation : tree.root.FullDerivationValid) : tree.root.HasModel semantics := by
  apply root_hasModel_of_acceptingLeaf_with
    (VariableJump.Rule semantics support.atomSupport)
    (fun node ↦ node.Timely ∧ node.InStrictNormalForm ∧ node.FullDerivationValid)
    tree wellFormed accepting ⟨timely, normal, derivation⟩
  · intro node accepting invariant
    exact Node.hasModel_of_accepting accepting invariant.1 invariant.2.1
  · intro node child children rule invariant childMem
    exact ⟨rule.child_timely invariant.1 childMem,
      rule.child_normal invariant.2.1 childMem,
      rule.child_fullDerivationValid invariant.2.2 childMem⟩
  · intro node child children rule invariant childMem childModel
    exact rule.hasModel_parent_of_child support invariant.2.2 invariant.1 invariant.2.1
      childMem childModel

end TableauTree

namespace VariableJump.Development

variable {Atom : Type u} [DecidableEq Atom]
  {Var : Type w} [DecidableEq Var]
  {semantics : Stlsat.AtomicSemantics Atom} {formula : Stlsat.Formula Atom}

/-- Soundness of the variable-aware JUMP tableau. -/
theorem soundness (support : AtomicSupport semantics Var)
    (tableau : VariableJump.Development semantics support.atomSupport formula)
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
  have rootModel := TableauTree.root_hasModel_of_variableAcceptingLeaf support tableau.tree
    tableau.wellFormed accepted rootTimely rootNormal rootDerivation
  apply (Stlsat.Formula.satisfiable_iff_hasModel formula semantics).mpr
  change tableau.tree.root.erase.HasModel semantics at rootModel
  rw [tableau.rooted_at, Node.erase_initial] at rootModel
  exact rootModel

end VariableJump.Development
end Stlsat.Tableau
