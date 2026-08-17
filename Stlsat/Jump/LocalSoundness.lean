/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.Validity

/-!
# Local semantic transport across JUMP

This module separates the semantic part of a JUMP from the combinatorial
window argument.  `Node.hasModel_of_jump_of_skippedInvariants` proves that a
model of the successor reconstructs a model of the source as soon as every
invariant instance at a strictly skipped instant is realized by that model.
-/

namespace Stlsat.Tableau
universe u

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

/-- Every invariant emitted by a marked obligation holds at each instant which
the JUMP skips strictly. -/
def SkippedInvariantsHold (node : Node Atom) (size : Nat)
    (semantics : Stlsat.AtomicSemantics Atom) (signal : Stlsat.Signal semantics) : Prop :=
  ∀ occurrence ∈ node.label, ∀ edge invariant,
    occurrence.postponedInvariant? = some (edge, invariant) →
      ∀ instant, node.time < instant → instant < node.time + size →
        invariant.Satisfies semantics signal instant

/-- Backward model preservation for a computed JUMP, factored through the
precise semantic obligation imposed at its skipped instants. -/
theorem hasModel_of_jump_of_model_of_skippedInvariants {node : Node Atom} {size : Nat}
    {semantics : Stlsat.AtomicSemantics Atom}
    (notRejected : ¬node.Rejected semantics) (poised : node.Poised)
    (computed : node.jumpSize? = some size) (timely : node.Timely)
    (normal : node.InStrictNormalForm)
    (model : (node.jump size).Model semantics)
    (skipped : node.SkippedInvariantsHold size semantics model.signal) :
    node.HasModel semantics := by
  let signal := model.signal
  have childSatisfied : (node.jump size).SatisfiedBy semantics signal := model.satisfies
  have positive := node.jumpSize_pos computed
  have locallyConsistent : node.erase.LocallyConsistent semantics := by
    by_contra inconsistent
    exact notRejected (Or.inr inconsistent)
  rcases locallyConsistent with ⟨valuation, valuationSatisfies⟩
  let updatedSignal : Stlsat.Signal semantics := Function.update signal node.time valuation
  have childSatisfiedUpdated :
      (node.jump size).SatisfiedBy semantics updatedSignal := by
    apply (satisfiedBy_iff (node.jump size) semantics updatedSignal).2
    intro occurrence occurrenceMem
    have old := (satisfiedBy_iff (node.jump size) semantics signal).1 childSatisfied
      occurrence occurrenceMem
    apply (Stlsat.Occurrence.satisfiedBy_congr_of_eqOn_ge occurrence.payload semantics
      (time := node.time + size) ?_).mp old
    intro instant instantGe
    simp only [updatedSignal]
    simp [Function.update, show instant ≠ node.time by omega]
  have skippedUpdated : node.SkippedInvariantsHold size semantics updatedSignal := by
    intro occurrence occurrenceMem edge invariant invariantShape instant after before
    have old := skipped occurrence occurrenceMem edge invariant invariantShape instant after before
    change invariant.Satisfies semantics signal instant at old
    apply (Stlsat.Formula.satisfies_congr_of_eqOn_ge invariant semantics ?_).mp old
    intro later laterGe
    simp only [updatedSignal]
    simp [Function.update, show later ≠ node.time by omega]
  have childHolds (occurrence : AnnotatedOccurrence Atom) (present : occurrence ∈ node.label)
      (temporal : occurrence.isTemporal = true) :
      occurrence.unmark.SatisfiedBy semantics updatedSignal (node.time + size) := by
    have survives := node.temporal_survives_computed_jump poised timely computed occurrence
      present temporal
    have childMem : occurrence.unmark ∈ (node.jump size).label := by
      change occurrence.unmark ∈ node.jumpLabel size
      apply Finset.mem_image.mpr
      exact ⟨occurrence, Finset.mem_filter.mpr ⟨present, survives⟩, rfl⟩
    have holds := (satisfiedBy_iff (node.jump size) semantics updatedSignal).1
      childSatisfiedUpdated occurrence.unmark childMem
    simpa [Node.jump] using holds
  refine ⟨⟨updatedSignal, (satisfiedBy_iff node semantics updatedSignal).2 ?_⟩⟩
  intro occurrence present
  have occurrenceNormal := (normal_iff node).mp normal occurrence present
  cases occurrence with
  | mk id payload parent =>
      cases payload with
      | unmarked formula =>
          cases formula with
          | truth => simp [AnnotatedOccurrence.SatisfiedBy, Stlsat.Occurrence.SatisfiedBy,
              Stlsat.Formula.SatisfiesFrom]
          | atom proposition =>
              have erasedMem : Stlsat.Occurrence.unmarked (.atom proposition) ∈
                  node.erase.label := Finset.mem_image.mpr ⟨_, present, rfl⟩
              have literal := valuationSatisfies _ erasedMem
              simpa [AnnotatedOccurrence.SatisfiedBy, Stlsat.Occurrence.SatisfiedBy,
                Stlsat.Formula.SatisfiesFrom, Stlsat.Occurrence.LiteralSatisfied,
                updatedSignal] using literal
          | neg body =>
              cases body with
              | truth =>
                  exfalso
                  apply notRejected
                  left
                  exact Finset.mem_image.mpr ⟨_, present, rfl⟩
              | atom proposition =>
                  have erasedMem : Stlsat.Occurrence.unmarked (.neg (.atom proposition)) ∈
                      node.erase.label := Finset.mem_image.mpr ⟨_, present, rfl⟩
                  have literal := valuationSatisfies _ erasedMem
                  simpa [AnnotatedOccurrence.SatisfiedBy, Stlsat.Occurrence.SatisfiedBy,
                    Stlsat.Formula.SatisfiesFrom, Stlsat.Occurrence.LiteralSatisfied,
                    updatedSignal] using literal
              | neg body =>
                  simp [AnnotatedOccurrence.InStrictNormalForm,
                    Stlsat.Occurrence.InStrictNormalForm,
                    Stlsat.Formula.InStrictNormalForm] at occurrenceNormal
              | and left right =>
                  simp [AnnotatedOccurrence.InStrictNormalForm,
                    Stlsat.Occurrence.InStrictNormalForm,
                    Stlsat.Formula.InStrictNormalForm] at occurrenceNormal
              | or left right =>
                  simp [AnnotatedOccurrence.InStrictNormalForm,
                    Stlsat.Occurrence.InStrictNormalForm,
                    Stlsat.Formula.InStrictNormalForm] at occurrenceNormal
              | eventually interval body =>
                  simp [AnnotatedOccurrence.InStrictNormalForm,
                    Stlsat.Occurrence.InStrictNormalForm,
                    Stlsat.Formula.InStrictNormalForm] at occurrenceNormal
              | always interval body =>
                  simp [AnnotatedOccurrence.InStrictNormalForm,
                    Stlsat.Occurrence.InStrictNormalForm,
                    Stlsat.Formula.InStrictNormalForm] at occurrenceNormal
              | strictUntil interval invariant target =>
                  simp [AnnotatedOccurrence.InStrictNormalForm,
                    Stlsat.Occurrence.InStrictNormalForm,
                    Stlsat.Formula.InStrictNormalForm] at occurrenceNormal
              | strictRelease interval target invariant =>
                  simp [AnnotatedOccurrence.InStrictNormalForm,
                    Stlsat.Occurrence.InStrictNormalForm,
                    Stlsat.Formula.InStrictNormalForm] at occurrenceNormal
          | and left right =>
              exfalso
              apply poised
              exact ⟨_, Expansion.conjunction _ left right rfl present⟩
          | or left right =>
              exfalso
              apply poised
              exact ⟨_, Expansion.disjunction _ left right rfl present⟩
          | eventually interval body =>
              have beforeLower := beforeLower_of_unmarked_temporal poised timely _ present
                interval (.eventually interval body) rfl rfl
              have destinationLe := node.jump_destination_le_lower _ interval present rfl
                computed beforeLower
              have later := childHolds _ present (by
                simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal,
                  Stlsat.Formula.isTemporal])
              exact eventually_satisfiedFrom_earlier (by omega) later
          | always interval body =>
              have beforeLower := beforeLower_of_unmarked_temporal poised timely _ present
                interval (.always interval body) rfl rfl
              have destinationLe := node.jump_destination_le_lower _ interval present rfl
                computed beforeLower
              have later := childHolds _ present (by
                simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal,
                  Stlsat.Formula.isTemporal])
              exact always_satisfiedFrom_earlier_beforeLower (by omega) destinationLe later
          | strictUntil interval invariant target =>
              have beforeLower := beforeLower_of_unmarked_temporal poised timely _ present
                interval (.strictUntil interval invariant target) rfl rfl
              have destinationLe := node.jump_destination_le_lower _ interval present rfl
                computed beforeLower
              have later := childHolds _ present (by
                simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal,
                  Stlsat.Formula.isTemporal])
              exact strictUntil_satisfiedFrom_earlier_beforeLower (by omega)
                destinationLe later
          | strictRelease interval target invariant =>
              have beforeLower := beforeLower_of_unmarked_temporal poised timely _ present
                interval (.strictRelease interval target invariant) rfl rfl
              have destinationLe := node.jump_destination_le_lower _ interval present rfl
                computed beforeLower
              have later := childHolds _ present (by
                simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal,
                  Stlsat.Formula.isTemporal])
              exact strictRelease_satisfiedFrom_earlier_beforeLower (by omega)
                destinationLe later
      | markedEventually interval body =>
          have later := childHolds _ present (by
            simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal])
          exact eventually_satisfiedFrom_earlier (by omega) later
      | markedAlways interval body =>
          have later := childHolds _ present (by
            simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal])
          apply always_satisfiedFrom_earlier
            (start := node.time + 1) (finish := node.time + size) (by omega)
          · intro instant after before
            exact skippedUpdated _ present 0 body rfl instant (by omega) before
          · exact later
      | markedStrictUntil interval invariant target =>
          have later := childHolds _ present (by
            simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal])
          apply strictUntil_satisfiedFrom_earlier
            (start := node.time + 1) (finish := node.time + size) (by omega)
          · intro instant after before
            exact skippedUpdated _ present 0 invariant rfl instant (by omega) before
          · exact later
      | markedStrictRelease interval target invariant =>
          have later := childHolds _ present (by
            simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal])
          apply strictRelease_satisfiedFrom_earlier
            (start := node.time + 1) (finish := node.time + size) (by omega)
          · intro instant after before
            exact skippedUpdated _ present 1 invariant rfl instant (by omega) before
          · exact later

/-- Backward model preservation in the convenient `HasModel` form. -/
theorem hasModel_of_jump_of_skippedInvariants {node : Node Atom} {size : Nat}
    {semantics : Stlsat.AtomicSemantics Atom}
    (notRejected : ¬node.Rejected semantics) (poised : node.Poised)
    (computed : node.jumpSize? = some size) (timely : node.Timely)
    (normal : node.InStrictNormalForm)
    (childModel : (node.jump size).HasModel semantics)
    (skipped : node.SkippedInvariantsHold size semantics
      (Classical.choice childModel).signal) :
    node.HasModel semantics :=
  node.hasModel_of_jump_of_model_of_skippedInvariants notRejected poised computed timely normal
    (Classical.choice childModel) skipped

end Node
end Stlsat.Tableau
