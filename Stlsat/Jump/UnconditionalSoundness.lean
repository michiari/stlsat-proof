/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.RankedSplicing

/-! # Unconditional soundness of the JUMP tableau -/

namespace Stlsat.Jump
universe u

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

/-- The window guards construct a successor model which realizes every
strictly skipped invariant instance. -/
theorem windowGuardsProvideSkippedModel
    (semantics : Stlsat.AtomicSemantics Atom) :
    WindowGuardsProvideSkippedModel semantics := by
  intro node size derivation notRejected poised hasTemporal sound complete computed timely
    normal childHasModel
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
              cases formula <;> simp_all [Node.survivesJump,
                AnnotatedOccurrence.interval?, AnnotatedOccurrence.isTemporal,
                Stlsat.Occurrence.isTemporal, Stlsat.Formula.isTemporal]
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

end Node

namespace Tableau

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom} {formula : Stlsat.Formula Atom}

/-- An accepted branch of the guarded JUMP tableau yields a model of its root
formula, with no additional semantic preservation hypothesis. -/
theorem soundness (tableau : Tableau semantics formula)
    (accepted : tableau.HasAcceptingBranch) : formula.Satisfiable semantics :=
  tableau.soundness_of_windowGuardsProvideSkippedModel
    (Node.windowGuardsProvideSkippedModel semantics) accepted

end Tableau
end Stlsat.Jump
