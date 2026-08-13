/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.Validity

/-!
# Splicing models on disjoint validity windows

This module packages modeled timed formulas as requirements and constructs one
signal satisfying a pairwise-disjoint finite family of them.
-/

namespace Stlsat.Jump
universe u v

namespace FormulaValidity

variable {Atom : Type u} {semantics : Stlsat.AtomicSemantics Atom}

structure ModeledRequirement (semantics : Stlsat.AtomicSemantics Atom) where
  formula : Stlsat.Formula Atom
  start : Nat
  signal : Stlsat.Signal semantics
  holds : formula.Satisfies semantics signal start

namespace ModeledRequirement

def Supports (requirement : ModeledRequirement semantics) (instant : Nat) : Prop :=
  ∃ occurrence ∈ validityOccurrences requirement.formula,
    requirement.start + occurrence.window.lower ≤ instant ∧
      instant ≤ requirement.start + occurrence.window.upper

def Disjoint (left right : ModeledRequirement semantics) : Prop :=
  ∀ instant, left.Supports instant → right.Supports instant → False

end ModeledRequirement

theorem exists_signal_satisfying_pairwise_disjoint
    (requirements : List (ModeledRequirement semantics))
    (pairwise : requirements.Pairwise ModeledRequirement.Disjoint) :
    ∃ signal : Stlsat.Signal semantics, ∀ requirement ∈ requirements,
      requirement.formula.Satisfies semantics signal requirement.start := by
  classical
  induction requirements with
  | nil =>
      exact ⟨fun _ => Classical.choice semantics.nonempty, by simp⟩
  | cons head tail ih =>
      have separated := (List.pairwise_cons.mp pairwise).1
      have tailPairwise := (List.pairwise_cons.mp pairwise).2
      rcases ih tailPairwise with ⟨tailSignal, tailHolds⟩
      let combined : Stlsat.Signal semantics := fun instant =>
        if head.Supports instant then head.signal instant else tailSignal instant
      refine ⟨combined, ?_⟩
      intro requirement requirementMem
      simp only [List.mem_cons] at requirementMem
      rcases requirementMem with equal | requirementMem
      · subst requirement
        apply (satisfies_congr_of_signalsAgree head.formula semantics ?_).mp head.holds
        intro occurrence occurrenceMem instant lower upper
        simp only [combined]
        rw [if_pos]
        exact ⟨occurrence, occurrenceMem, lower, upper⟩
      · have old := tailHolds requirement requirementMem
        apply (satisfies_congr_of_signalsAgree requirement.formula semantics ?_).mp old
        intro occurrence occurrenceMem instant lower upper
        simp only [combined]
        rw [if_neg]
        intro headSupports
        exact separated requirement requirementMem instant headSupports
          ⟨occurrence, occurrenceMem, lower, upper⟩

end FormulaValidity
end Stlsat.Jump

