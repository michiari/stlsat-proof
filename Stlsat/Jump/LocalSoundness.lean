/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.Splicing

/-!
# Local semantic transport across JUMP

This module separates the semantic part of a JUMP from the combinatorial
window argument.  `Node.hasModel_of_jump_of_skippedInvariants` proves that a
model of the successor reconstructs a model of the source as soon as every
invariant instance at a strictly skipped instant is realized by that model.
-/

namespace Stlsat.Jump
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

omit [DecidableEq Atom] in
/-- A signal instant inspected by a skipped invariant instance lies in the
corresponding `N(u)` window translated by the skipped offset. -/
theorem skippedInvariant_support (node : Node Atom)
    (occurrence : AnnotatedOccurrence Atom) (present : occurrence ∈ node.label)
    (edge : Nat) (invariant : Stlsat.Formula Atom)
    (shape : occurrence.postponedInvariant? = some (edge, invariant))
    (validity : ValidityOccurrence)
    (validityMem : validity ∈ FormulaValidity.validityOccurrences invariant)
    (offset instant : Nat)
    (lower : node.time + offset + validity.window.lower ≤ instant)
    (upper : instant ≤ node.time + offset + validity.window.upper) :
    let window :=
      (WindowOccurrence.ofValidity (occurrence.id ++ [edge]) validity).shift node.time
    window ∈ node.invariantWindows ∧
      (window.shift offset).window.lower ≤ instant ∧
      instant ≤ (window.shift offset).window.upper := by
  dsimp only
  refine ⟨node.invariantWindow_mem occurrence present edge invariant shape validity validityMem,
    ?_, ?_⟩ <;>
    simp only [WindowOccurrence.shift, WindowOccurrence.ofValidity,
      Stlsat.Interval.shift] <;>
    omega

omit [DecidableEq Atom] in
/-- A signal instant inspected by an independent temporal formula lies in its
corresponding `O(u)` window. -/
theorem independent_support (node : Node Atom)
    (occurrence : AnnotatedOccurrence Atom) (present : occurrence ∈ node.label)
    (temporal : occurrence.isTemporal = true)
    (notParentActive : ¬node.ParentActive occurrence)
    (validity : ValidityOccurrence)
    (validityMem : validity ∈ FormulaValidity.validityOccurrences occurrence.formula)
    (instant : Nat) (lower : validity.window.lower ≤ instant)
    (upper : instant ≤ validity.window.upper) :
    let window := WindowOccurrence.ofValidity occurrence.id validity
    window ∈ node.independentWindows ∧ window.window.lower ≤ instant ∧
      instant ≤ window.window.upper := by
  dsimp only
  exact ⟨node.independentWindow_mem occurrence present temporal notParentActive validity
    validityMem, lower, upper⟩

omit [DecidableEq Atom] in
/-- The soundness guard rules out every common signal instant between a
strictly skipped invariant instance and a distinct independent leaf. -/
theorem skippedInvariant_disjoint_from_independent (node : Node Atom) {size offset : Nat}
    (computed : node.jumpSize? = some size) (sound : node.SoundSafe)
    (strictlySkipped : offset < size)
    (source : AnnotatedOccurrence Atom) (sourceMem : source ∈ node.label)
    (edge : Nat) (invariant : Stlsat.Formula Atom)
    (sourceShape : source.postponedInvariant? = some (edge, invariant))
    (invariantValidity : ValidityOccurrence)
    (invariantMem : invariantValidity ∈ FormulaValidity.validityOccurrences invariant)
    (other : AnnotatedOccurrence Atom) (otherMem : other ∈ node.label)
    (otherTemporal : other.isTemporal = true)
    (otherIndependent : ¬node.ParentActive other)
    (otherValidity : ValidityOccurrence)
    (otherValidityMem : otherValidity ∈
      FormulaValidity.validityOccurrences other.formula)
    (distinct : source.id ++ [edge] ++ invariantValidity.path ≠
      other.id ++ otherValidity.path) :
    ¬∃ instant,
      node.time + offset + invariantValidity.window.lower ≤ instant ∧
      instant ≤ node.time + offset + invariantValidity.window.upper ∧
      otherValidity.window.lower ≤ instant ∧ instant ≤ otherValidity.window.upper := by
  rintro ⟨instant, invariantLower, invariantUpper, otherLower, otherUpper⟩
  let invariantWindow :=
    (WindowOccurrence.ofValidity (source.id ++ [edge]) invariantValidity).shift node.time
  let otherWindow := WindowOccurrence.ofValidity other.id otherValidity
  have invariantWindowMem : invariantWindow ∈ node.invariantWindows := by
    exact node.invariantWindow_mem source sourceMem edge invariant sourceShape
      invariantValidity invariantMem
  have otherWindowMem : otherWindow ∈ node.independentWindows := by
    exact node.independentWindow_mem other otherMem otherTemporal otherIndependent
      otherValidity otherValidityMem
  have windowDistinct : invariantWindow.id ≠ otherWindow.id := by
    simpa [invariantWindow, otherWindow, WindowOccurrence.shift,
      WindowOccurrence.ofValidity, List.append_assoc] using distinct
  have disjoint := node.shiftedInvariant_disjoint computed sound strictlySkipped
    invariantWindow otherWindow invariantWindowMem otherWindowMem windowDistinct
  apply disjoint
  constructor <;>
    simp only [invariantWindow, otherWindow, WindowOccurrence.shift,
      WindowOccurrence.ofValidity, Stlsat.Interval.shift] <;>
    omega

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
end Stlsat.Jump
