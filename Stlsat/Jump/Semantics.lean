/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Tableau.Semantics
import Stlsat.Jump.Tableau

/-!
# Semantic preservation specific to JUMP

The common node semantics and the ordinary expansion/`STEP` cases live in
`Stlsat.Tableau.Semantics`.  This module contains only the additional temporal
transport, survival, normality, and timeliness facts needed by the JUMP rule.
-/

namespace Stlsat.Tableau

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

omit [DecidableEq Atom] in
/-- An eventuality modeled at a later tableau time is modeled at every earlier
tableau time as well. -/
theorem eventually_satisfiedFrom_earlier {interval : Stlsat.Interval}
    {body : Stlsat.Formula Atom} {semantics : Stlsat.AtomicSemantics Atom}
    {signal : Stlsat.Signal semantics} {start finish : Nat}
    (leFinish : start ≤ finish)
    (holds : (Stlsat.Formula.eventually interval body).SatisfiesFrom
      semantics signal finish) :
    (Stlsat.Formula.eventually interval body).SatisfiesFrom semantics signal start := by
  induction finish, leFinish using Nat.le_induction with
  | base => exact holds
  | succ finish _ ih => exact ih (Stlsat.Formula.eventually_later holds)

omit [DecidableEq Atom] in
/-- An always obligation can be transported backwards while its lower endpoint
has not been passed. -/
theorem always_satisfiedFrom_earlier_beforeLower {interval : Stlsat.Interval}
    {body : Stlsat.Formula Atom} {semantics : Stlsat.AtomicSemantics Atom}
    {signal : Stlsat.Signal semantics} {start finish : Nat}
    (leFinish : start ≤ finish) (finishLe : finish ≤ interval.lower)
    (holds : (Stlsat.Formula.always interval body).SatisfiesFrom
      semantics signal finish) :
    (Stlsat.Formula.always interval body).SatisfiesFrom semantics signal start := by
  induction finish, leFinish using Nat.le_induction with
  | base => exact holds
  | succ finish _ ih =>
      exact ih (by omega) (Stlsat.Formula.always_beforeLower (by omega) holds)

omit [DecidableEq Atom] in
/-- A strict-until obligation can be transported backwards while its lower
endpoint has not been passed. -/
theorem strictUntil_satisfiedFrom_earlier_beforeLower {interval : Stlsat.Interval}
    {invariant target : Stlsat.Formula Atom}
    {semantics : Stlsat.AtomicSemantics Atom} {signal : Stlsat.Signal semantics}
    {start finish : Nat} (leFinish : start ≤ finish)
    (finishLe : finish ≤ interval.lower)
    (holds : (Stlsat.Formula.strictUntil interval invariant target).SatisfiesFrom
      semantics signal finish) :
    (Stlsat.Formula.strictUntil interval invariant target).SatisfiesFrom
      semantics signal start := by
  induction finish, leFinish using Nat.le_induction with
  | base => exact holds
  | succ finish _ ih =>
      exact ih (by omega) (Stlsat.Formula.strictUntil_beforeLower (by omega) holds)

omit [DecidableEq Atom] in
/-- A strict-release obligation can be transported backwards while its lower
endpoint has not been passed. -/
theorem strictRelease_satisfiedFrom_earlier_beforeLower {interval : Stlsat.Interval}
    {target invariant : Stlsat.Formula Atom}
    {semantics : Stlsat.AtomicSemantics Atom} {signal : Stlsat.Signal semantics}
    {start finish : Nat} (leFinish : start ≤ finish)
    (finishLe : finish ≤ interval.lower)
    (holds : (Stlsat.Formula.strictRelease interval target invariant).SatisfiesFrom
      semantics signal finish) :
    (Stlsat.Formula.strictRelease interval target invariant).SatisfiesFrom
      semantics signal start := by
  induction finish, leFinish using Nat.le_induction with
  | base => exact holds
  | succ finish _ ih =>
      exact ih (by omega) (Stlsat.Formula.strictRelease_beforeLower (by omega) holds)

omit [DecidableEq Atom] in
/-- Transport an always obligation backwards, supplying its body at precisely
the active instants skipped by the transport. -/
theorem always_satisfiedFrom_earlier {interval : Stlsat.Interval}
    {body : Stlsat.Formula Atom} {semantics : Stlsat.AtomicSemantics Atom}
    {signal : Stlsat.Signal semantics} {start finish : Nat}
    (leFinish : start ≤ finish)
    (bodyHolds : ∀ instant, start ≤ instant → instant < finish →
      body.Satisfies semantics signal instant)
    (holds : (Stlsat.Formula.always interval body).SatisfiesFrom
      semantics signal finish) :
    (Stlsat.Formula.always interval body).SatisfiesFrom semantics signal start := by
  induction finish, leFinish using Nat.le_induction with
  | base => exact holds
  | succ finish startLe ih =>
      apply ih
      · intro instant instantLe instantLt
        exact bodyHolds instant instantLe (by omega)
      · by_cases beforeLower : finish < interval.lower
        · exact Stlsat.Formula.always_beforeLower beforeLower holds
        · exact Stlsat.Formula.always_now_later (by omega)
            (bodyHolds finish startLe (by omega)) holds

omit [DecidableEq Atom] in
/-- Transport strict until backwards, supplying its invariant at the active
instants skipped by the transport. -/
theorem strictUntil_satisfiedFrom_earlier {interval : Stlsat.Interval}
    {invariant target : Stlsat.Formula Atom}
    {semantics : Stlsat.AtomicSemantics Atom} {signal : Stlsat.Signal semantics}
    {start finish : Nat} (leFinish : start ≤ finish)
    (invariantHolds : ∀ instant, start ≤ instant → instant < finish →
      invariant.Satisfies semantics signal instant)
    (holds : (Stlsat.Formula.strictUntil interval invariant target).SatisfiesFrom
      semantics signal finish) :
    (Stlsat.Formula.strictUntil interval invariant target).SatisfiesFrom
      semantics signal start := by
  induction finish, leFinish using Nat.le_induction with
  | base => exact holds
  | succ finish startLe ih =>
      apply ih
      · intro instant instantLe instantLt
        exact invariantHolds instant instantLe (by omega)
      · by_cases beforeLower : finish < interval.lower
        · exact Stlsat.Formula.strictUntil_beforeLower beforeLower holds
        · exact Stlsat.Formula.strictUntil_later (by omega)
            (invariantHolds finish startLe (by omega)) holds

omit [DecidableEq Atom] in
/-- Transport strict release backwards, supplying its invariant at the active
instants skipped by the transport. -/
theorem strictRelease_satisfiedFrom_earlier {interval : Stlsat.Interval}
    {target invariant : Stlsat.Formula Atom}
    {semantics : Stlsat.AtomicSemantics Atom} {signal : Stlsat.Signal semantics}
    {start finish : Nat} (leFinish : start ≤ finish)
    (invariantHolds : ∀ instant, start ≤ instant → instant < finish →
      invariant.Satisfies semantics signal instant)
    (holds : (Stlsat.Formula.strictRelease interval target invariant).SatisfiesFrom
      semantics signal finish) :
    (Stlsat.Formula.strictRelease interval target invariant).SatisfiesFrom
      semantics signal start := by
  induction finish, leFinish using Nat.le_induction with
  | base => exact holds
  | succ finish startLe ih =>
      apply ih
      · intro instant instantLe instantLt
        exact invariantHolds instant instantLe (by omega)
      · by_cases beforeLower : finish < interval.lower
        · exact Stlsat.Formula.strictRelease_beforeLower beforeLower holds
        · exact Stlsat.Formula.strictRelease_later
            (invariantHolds finish startLe (by omega)) holds

/-- With all live endpoints in `K(u)`, no temporal occurrence of a timely
poised node is discarded by a computed JUMP. -/
theorem temporal_survives_computed_jump {node : Node Atom} {size : Nat}
    (poised : node.Poised) (timely : node.Timely)
    (computed : node.jumpSize? = some size)
    (occurrence : AnnotatedOccurrence Atom) (present : occurrence ∈ node.label)
    (temporal : occurrence.isTemporal = true) :
    Node.survivesJump (node.time + size) occurrence = true := by
  cases occurrence with
  | mk id payload parent =>
      cases payload with
      | unmarked formula =>
          cases formula with
          | truth => simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal,
              Stlsat.Formula.isTemporal] at temporal
          | atom proposition => simp [AnnotatedOccurrence.isTemporal,
              Stlsat.Occurrence.isTemporal, Stlsat.Formula.isTemporal] at temporal
          | neg body => simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal,
              Stlsat.Formula.isTemporal] at temporal
          | and left right => simp [AnnotatedOccurrence.isTemporal,
              Stlsat.Occurrence.isTemporal, Stlsat.Formula.isTemporal] at temporal
          | or left right => simp [AnnotatedOccurrence.isTemporal,
              Stlsat.Occurrence.isTemporal, Stlsat.Formula.isTemporal] at temporal
          | eventually interval body =>
              have beforeLower := beforeLower_of_unmarked_temporal poised timely
                { id := id, payload := .unmarked (.eventually interval body), parent := parent }
                present interval (.eventually interval body) rfl rfl
              have destination := node.jump_destination_le_lower _ interval present rfl computed
                beforeLower
              simpa [Node.survivesJump, AnnotatedOccurrence.interval?] using
                destination.trans interval.lower_le_upper
          | always interval body =>
              have beforeLower := beforeLower_of_unmarked_temporal poised timely
                { id := id, payload := .unmarked (.always interval body), parent := parent }
                present interval (.always interval body) rfl rfl
              have destination := node.jump_destination_le_lower _ interval present rfl computed
                beforeLower
              simpa [Node.survivesJump, AnnotatedOccurrence.interval?] using
                destination.trans interval.lower_le_upper
          | strictUntil interval invariant target =>
              have beforeLower := beforeLower_of_unmarked_temporal poised timely
                { id := id,
                  payload := .unmarked (.strictUntil interval invariant target),
                  parent := parent }
                present interval (.strictUntil interval invariant target) rfl rfl
              have destination := node.jump_destination_le_lower _ interval present rfl computed
                beforeLower
              simpa [Node.survivesJump, AnnotatedOccurrence.interval?] using
                destination.trans interval.lower_le_upper
          | strictRelease interval target invariant =>
              have beforeLower := beforeLower_of_unmarked_temporal poised timely
                { id := id,
                  payload := .unmarked (.strictRelease interval target invariant),
                  parent := parent }
                present interval (.strictRelease interval target invariant) rfl rfl
              have destination := node.jump_destination_le_lower _ interval present rfl computed
                beforeLower
              simpa [Node.survivesJump, AnnotatedOccurrence.interval?] using
                destination.trans interval.lower_le_upper
      | markedEventually interval body =>
          have future : node.time < interval.upper := by
            exact (timely_iff node).mp timely _ present
          have destination := node.jump_destination_le_upper _ interval present rfl computed future
          simpa [Node.survivesJump, AnnotatedOccurrence.interval?] using destination
      | markedAlways interval body =>
          have future : node.time < interval.upper := by
            exact (timely_iff node).mp timely _ present
          have destination := node.jump_destination_le_upper _ interval present rfl computed future
          simpa [Node.survivesJump, AnnotatedOccurrence.interval?] using destination
      | markedStrictUntil interval invariant target =>
          have future : node.time < interval.upper := by
            exact (timely_iff node).mp timely _ present
          have destination := node.jump_destination_le_upper _ interval present rfl computed future
          simpa [Node.survivesJump, AnnotatedOccurrence.interval?] using destination
      | markedStrictRelease interval target invariant =>
          have future : node.time < interval.upper := by
            exact (timely_iff node).mp timely _ present
          have destination := node.jump_destination_le_upper _ interval present rfl computed future
          simpa [Node.survivesJump, AnnotatedOccurrence.interval?] using destination

/-- Dropping local constraints and unmarking survivors preserves normality. -/
theorem jump_normal (node : Node Atom) (size : Nat) (normal : node.InStrictNormalForm) :
    (node.jump size).InStrictNormalForm := by
  rw [normal_iff] at normal ⊢
  intro occurrence occurrence_mem
  change occurrence ∈ node.jumpLabel size at occurrence_mem
  rcases Finset.mem_image.mp occurrence_mem with ⟨source, source_mem, rfl⟩
  have source_present := (Finset.mem_filter.mp source_mem).1
  exact (AnnotatedOccurrence.normal_unmark source).mpr (normal source source_present)

/-- Every retained temporal occurrence is timely at the jump destination. -/
theorem jump_timely (node : Node Atom) (size : Nat) : (node.jump size).Timely := by
  rw [timely_iff]
  intro occurrence occurrence_mem
  change occurrence ∈ node.jumpLabel size at occurrence_mem
  rcases Finset.mem_image.mp occurrence_mem with ⟨source, source_mem, rfl⟩
  have survives := (Finset.mem_filter.mp source_mem).2
  change source.unmark.Timely (node.time + size)
  cases source with
  | mk id payload parent =>
      cases payload with
      | unmarked formula =>
          cases formula <;>
            simp_all [Node.jumpLabel, Node.survivesJump,
              AnnotatedOccurrence.interval?, AnnotatedOccurrence.unmark,
              AnnotatedOccurrence.relabel, AnnotatedOccurrence.Timely,
              Stlsat.Occurrence.unmark, Stlsat.Occurrence.Timely,
              Stlsat.Formula.Timely]
      | markedEventually interval body =>
          simp_all [Node.jumpLabel, Node.survivesJump,
            AnnotatedOccurrence.interval?, AnnotatedOccurrence.unmark,
            AnnotatedOccurrence.relabel, AnnotatedOccurrence.Timely,
            Stlsat.Occurrence.unmark, Stlsat.Occurrence.Timely,
            Stlsat.Formula.Timely]
      | markedAlways interval body =>
          simp_all [Node.jumpLabel, Node.survivesJump,
            AnnotatedOccurrence.interval?, AnnotatedOccurrence.unmark,
            AnnotatedOccurrence.relabel, AnnotatedOccurrence.Timely,
            Stlsat.Occurrence.unmark, Stlsat.Occurrence.Timely,
            Stlsat.Formula.Timely]
      | markedStrictUntil interval invariant target =>
          simp_all [Node.jumpLabel, Node.survivesJump,
            AnnotatedOccurrence.interval?, AnnotatedOccurrence.unmark,
            AnnotatedOccurrence.relabel, AnnotatedOccurrence.Timely,
            Stlsat.Occurrence.unmark, Stlsat.Occurrence.Timely,
            Stlsat.Formula.Timely]
      | markedStrictRelease interval target invariant =>
          simp_all [Node.jumpLabel, Node.survivesJump,
            AnnotatedOccurrence.interval?, AnnotatedOccurrence.unmark,
            AnnotatedOccurrence.relabel, AnnotatedOccurrence.Timely,
            Stlsat.Occurrence.unmark, Stlsat.Occurrence.Timely,
            Stlsat.Formula.Timely]

end Node

namespace Jump.Rule

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom}

/-- Every child of a JUMP-tableau rule preserves strict normal form. -/
theorem child_normal {node child : Node Atom} {children : List (Node Atom)}
    (rule : Jump.Rule semantics node children) (normal : node.InStrictNormalForm)
    (child_mem : child ∈ children) : child.InStrictNormalForm := by
  cases rule with
  | expand notRejected expansion => exact expansion.child_normal normal child_mem
  | step notRejected poised hasTemporal jumpDisabled =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      exact Node.step_normal normal
  | jump notRejected poised hasTemporal sound complete size computed =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      exact Node.jump_normal node size normal

/-- Every child of a JUMP-tableau rule is timely when its parent is timely. -/
theorem child_timely {node child : Node Atom} {children : List (Node Atom)}
    (rule : Jump.Rule semantics node children) (timely : node.Timely)
    (child_mem : child ∈ children) : child.Timely := by
  cases rule with
  | expand notRejected expansion => exact expansion.child_timely timely child_mem
  | step notRejected poised hasTemporal jumpDisabled =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      exact Node.step_timely timely poised
  | jump notRejected poised hasTemporal sound complete size computed =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      exact Node.jump_timely node size

end Jump.Rule

end Stlsat.Tableau
