/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.Canonical

/-! # Semantic reconstruction from an expansion frontier -/

namespace Stlsat.Jump
universe u
namespace ExpansionFrontier

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom}

/-- Frontier reconstruction only needs semantic facts for the live leaves
which actually occur in the frontier. -/
theorem satisfiedBy_of_live {node : Node Atom} {id parent formula}
    (frontier : ExpansionFrontier node id parent formula)
    {signal : Stlsat.Signal semantics}
    (unmarked : ∀ id parent formula,
      AnnotatedOccurrence.mk id (.unmarked formula) parent ∈ node.label →
        formula.SatisfiesFrom semantics signal node.time)
    (marked : ∀ occurrence ∈ node.label,
      match occurrence.payload with
      | .unmarked _ => True
      | _ => occurrence.SatisfiedBy semantics signal node.time) :
    formula.SatisfiesFrom semantics signal node.time := by
  induction frontier with
  | live id parent formula present => exact unmarked id parent formula present
  | disjunctionLeft id parent left right frontier ih =>
      simpa only [Stlsat.Formula.SatisfiesFrom] using Or.inl ih
  | disjunctionRight id parent left right frontier ih =>
      simpa only [Stlsat.Formula.SatisfiesFrom] using Or.inr ih
  | conjunction id parent left right leftFrontier rightFrontier ihLeft ihRight =>
      simpa only [Stlsat.Formula.SatisfiesFrom] using And.intro ihLeft ihRight
  | eventuallyNow id parent interval body active notAfter bodyFrontier ih =>
      have now := (Stlsat.Formula.satisfiesFrom_temporalExpansion body semantics signal
        node.time).mp ih
      by_cases beforeEnd : node.time < interval.upper
      · exact Stlsat.Formula.eventually_now active beforeEnd now
      · exact Stlsat.Formula.eventually_atEnd (by omega) now
  | eventuallyPostpone id parent interval body active beforeEnd present =>
      let occurrence : AnnotatedOccurrence Atom :=
        .mk id (.markedEventually interval body) parent
      have later := marked occurrence present
      simpa [occurrence, AnnotatedOccurrence.SatisfiedBy,
        Stlsat.Occurrence.SatisfiedBy] using Stlsat.Formula.eventually_later later
  | alwaysPostpone id parent interval body active beforeEnd present bodyFrontier ih =>
      let occurrence : AnnotatedOccurrence Atom :=
        .mk id (.markedAlways interval body) parent
      have later := marked occurrence present
      apply Stlsat.Formula.always_now_later active
      · exact (Stlsat.Formula.satisfiesFrom_temporalExpansion body semantics signal
          node.time).mp ih
      · simpa [occurrence, AnnotatedOccurrence.SatisfiedBy,
          Stlsat.Occurrence.SatisfiedBy] using later
  | alwaysAtEnd id parent interval body atEnd bodyFrontier ih =>
      apply Stlsat.Formula.always_atEnd atEnd
      exact (Stlsat.Formula.satisfiesFrom_temporalExpansion body semantics signal
        node.time).mp ih
  | strictUntilNow id parent interval invariant target active notAfter targetFrontier ih =>
      have now := (Stlsat.Formula.satisfiesFrom_temporalExpansion target semantics signal
        node.time).mp ih
      by_cases beforeEnd : node.time < interval.upper
      · exact Stlsat.Formula.strictUntil_now active beforeEnd now
      · exact Stlsat.Formula.strictUntil_atEnd (by omega) now
  | strictUntilPostpone id parent interval invariant target active beforeEnd present
      invariantFrontier ih =>
      let occurrence : AnnotatedOccurrence Atom :=
        .mk id (.markedStrictUntil interval invariant target) parent
      have later := marked occurrence present
      apply Stlsat.Formula.strictUntil_later active
      · exact (Stlsat.Formula.satisfiesFrom_temporalExpansion invariant semantics signal
          node.time).mp ih
      · simpa [occurrence, AnnotatedOccurrence.SatisfiedBy,
          Stlsat.Occurrence.SatisfiedBy] using later
  | strictReleaseNow id parent interval target invariant active beforeEnd targetFrontier
      invariantFrontier ihTarget ihInvariant =>
      apply Stlsat.Formula.strictRelease_now active beforeEnd
      · exact (Stlsat.Formula.satisfiesFrom_temporalExpansion target semantics signal
          node.time).mp ihTarget
      · exact (Stlsat.Formula.satisfiesFrom_temporalExpansion invariant semantics signal
          node.time).mp ihInvariant
  | strictReleasePostpone id parent interval target invariant active beforeEnd present
      invariantFrontier ih =>
      let occurrence : AnnotatedOccurrence Atom :=
        .mk id (.markedStrictRelease interval target invariant) parent
      have later := marked occurrence present
      apply Stlsat.Formula.strictRelease_later
      · exact (Stlsat.Formula.satisfiesFrom_temporalExpansion invariant semantics signal
          node.time).mp ih
      · simpa [occurrence, AnnotatedOccurrence.SatisfiedBy,
          Stlsat.Occurrence.SatisfiedBy] using later
  | strictReleaseAtEnd id parent interval target invariant atEnd invariantFrontier ih =>
      apply Stlsat.Formula.strictRelease_atEnd atEnd
      exact (Stlsat.Formula.satisfiesFrom_temporalExpansion invariant semantics signal
        node.time).mp ih

/-- If a signal satisfies the live label, every deleted internal formula
recorded by an expansion frontier is satisfied as well. -/
theorem satisfiedBy {node : Node Atom} {id parent formula}
    (frontier : ExpansionFrontier node id parent formula)
    {signal : Stlsat.Signal semantics} (nodeHolds : node.SatisfiedBy semantics signal) :
    formula.SatisfiesFrom semantics signal node.time := by
  induction frontier with
  | live id parent formula present =>
      exact (Node.satisfiedBy_iff node semantics signal).1 nodeHolds _ present
  | disjunctionLeft id parent left right frontier ih =>
      simpa only [Stlsat.Formula.SatisfiesFrom] using Or.inl ih
  | disjunctionRight id parent left right frontier ih =>
      simpa only [Stlsat.Formula.SatisfiesFrom] using Or.inr ih
  | conjunction id parent left right leftFrontier rightFrontier ihLeft ihRight =>
      simpa only [Stlsat.Formula.SatisfiesFrom] using And.intro ihLeft ihRight
  | eventuallyNow id parent interval body active notAfter bodyFrontier ih =>
      have now := (Stlsat.Formula.satisfiesFrom_temporalExpansion body semantics signal
        node.time).mp ih
      by_cases beforeEnd : node.time < interval.upper
      · exact Stlsat.Formula.eventually_now active beforeEnd now
      · exact Stlsat.Formula.eventually_atEnd (by omega) now
  | eventuallyPostpone id parent interval body active beforeEnd marked =>
      have later := (Node.satisfiedBy_iff node semantics signal).1 nodeHolds _ marked
      simpa [AnnotatedOccurrence.SatisfiedBy, Stlsat.Occurrence.SatisfiedBy] using
        Stlsat.Formula.eventually_later later
  | alwaysPostpone id parent interval body active beforeEnd marked bodyFrontier ih =>
      have later := (Node.satisfiedBy_iff node semantics signal).1 nodeHolds _ marked
      apply Stlsat.Formula.always_now_later active
      · exact (Stlsat.Formula.satisfiesFrom_temporalExpansion body semantics signal
          node.time).mp ih
      · simpa [AnnotatedOccurrence.SatisfiedBy, Stlsat.Occurrence.SatisfiedBy] using later
  | alwaysAtEnd id parent interval body atEnd bodyFrontier ih =>
      apply Stlsat.Formula.always_atEnd atEnd
      exact (Stlsat.Formula.satisfiesFrom_temporalExpansion body semantics signal
        node.time).mp ih
  | strictUntilNow id parent interval invariant target active notAfter targetFrontier ih =>
      have now := (Stlsat.Formula.satisfiesFrom_temporalExpansion target semantics signal
        node.time).mp ih
      by_cases beforeEnd : node.time < interval.upper
      · exact Stlsat.Formula.strictUntil_now active beforeEnd now
      · exact Stlsat.Formula.strictUntil_atEnd (by omega) now
  | strictUntilPostpone id parent interval invariant target active beforeEnd marked
      invariantFrontier ih =>
      have later := (Node.satisfiedBy_iff node semantics signal).1 nodeHolds _ marked
      apply Stlsat.Formula.strictUntil_later active
      · exact (Stlsat.Formula.satisfiesFrom_temporalExpansion invariant semantics signal
          node.time).mp ih
      · simpa [AnnotatedOccurrence.SatisfiedBy, Stlsat.Occurrence.SatisfiedBy] using later
  | strictReleaseNow id parent interval target invariant active beforeEnd targetFrontier
      invariantFrontier ihTarget ihInvariant =>
      apply Stlsat.Formula.strictRelease_now active beforeEnd
      · exact (Stlsat.Formula.satisfiesFrom_temporalExpansion target semantics signal
          node.time).mp ihTarget
      · exact (Stlsat.Formula.satisfiesFrom_temporalExpansion invariant semantics signal
          node.time).mp ihInvariant
  | strictReleasePostpone id parent interval target invariant active beforeEnd marked
      invariantFrontier ih =>
      have later := (Node.satisfiedBy_iff node semantics signal).1 nodeHolds _ marked
      apply Stlsat.Formula.strictRelease_later
      · exact (Stlsat.Formula.satisfiesFrom_temporalExpansion invariant semantics signal
          node.time).mp ih
      · simpa [AnnotatedOccurrence.SatisfiedBy, Stlsat.Occurrence.SatisfiedBy] using later
  | strictReleaseAtEnd id parent interval target invariant atEnd invariantFrontier ih =>
      apply Stlsat.Formula.strictRelease_atEnd atEnd
      exact (Stlsat.Formula.satisfiesFrom_temporalExpansion invariant semantics signal
        node.time).mp ih

end ExpansionFrontier
end Stlsat.Jump
