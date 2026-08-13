/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Basic.Tableau
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.WellFounded

/-!
# Termination of the basic STL tableau

This file proves that the initial node of the basic tableau is accessible for
the relation which chooses one child of a basic-tableau rule.  In particular,
there is no infinite branch starting at an initial node.

The rule relation is not well-founded on arbitrary nodes: an unmarked temporal
formula whose interval has already expired would be propagated forever by
`STEP`.  We therefore establish accessibility from nodes satisfying the two
invariants enjoyed by every initial node and preserved by every rule:

* all absolute temporal horizons are bounded by the horizon of the input;
* every temporal formula exposed through propositional structure is timely.

`JUMP` is deliberately outside the basic tableau and is not considered here.
-/

namespace Stlsat

universe u

namespace Formula

variable {Atom : Type u}

/-- The paper's time horizon: the maximum accumulated temporal deadline. -/
def horizon : Formula Atom → ℕ
  | .truth | .atom _ => 0
  | .neg body => body.horizon
  | .and left right | .or left right => max left.horizon right.horizon
  | .eventually interval body | .always interval body => interval.upper + body.horizon
  | .strictUntil interval left right | .strictRelease interval left right =>
      interval.upper + max left.horizon right.horizon

/-- Syntactic work left for expansion rules; interval endpoints are ignored. -/
def expansionWeight : Formula Atom → ℕ
  | .truth | .atom _ => 0
  | .neg body => body.expansionWeight
  | .and left right | .or left right =>
      left.expansionWeight + right.expansionWeight + 1
  | .eventually _ body | .always _ body => body.expansionWeight + 1
  | .strictUntil _ left right | .strictRelease _ left right =>
      left.expansionWeight + right.expansionWeight + 1

/--
Every temporal operator exposed through propositional structure is still in
time.  Recursion stops at a temporal operator because intervals in its
arguments remain relative until `temporalExpansion` extracts those arguments.
-/
def Timely (time : ℕ) : Formula Atom → Prop
  | .truth | .atom _ => True
  | .neg body => body.Timely time
  | .and left right | .or left right => left.Timely time ∧ right.Timely time
  | .eventually interval _ | .always interval _ => time ≤ interval.upper
  | .strictUntil interval _ _ | .strictRelease interval _ _ => time ≤ interval.upper

@[simp]
theorem expansionWeight_temporalExpansion (formula : Formula Atom) (time : ℕ) :
    (formula.temporalExpansion time).expansionWeight = formula.expansionWeight := by
  induction formula <;> simp_all [expansionWeight, temporalExpansion]

theorem horizon_temporalExpansion_le (formula : Formula Atom) (time : ℕ) :
    (formula.temporalExpansion time).horizon ≤ time + formula.horizon := by
  induction formula with
  | truth => simp [horizon, temporalExpansion]
  | atom => simp [horizon, temporalExpansion]
  | neg body ih => simpa [horizon, temporalExpansion] using ih
  | and left right ihLeft ihRight =>
      simp only [temporalExpansion, horizon]
      apply max_le
      · exact ihLeft.trans (Nat.add_le_add_left (Nat.le_max_left _ _) _)
      · exact ihRight.trans (Nat.add_le_add_left (Nat.le_max_right _ _) _)
  | or left right ihLeft ihRight =>
      simp only [temporalExpansion, horizon]
      apply max_le
      · exact ihLeft.trans (Nat.add_le_add_left (Nat.le_max_left _ _) _)
      · exact ihRight.trans (Nat.add_le_add_left (Nat.le_max_right _ _) _)
  | eventually interval body ih =>
      simp [temporalExpansion, horizon, Interval.shift]
      omega
  | always interval body ih =>
      simp [temporalExpansion, horizon, Interval.shift]
      omega
  | strictUntil interval left right ihLeft ihRight =>
      simp [temporalExpansion, horizon, Interval.shift]
      omega
  | strictRelease interval left right ihLeft ihRight =>
      simp [temporalExpansion, horizon, Interval.shift]
      omega

@[simp]
theorem timely_zero (formula : Formula Atom) : formula.Timely 0 := by
  induction formula <;> simp_all [Timely]

@[simp]
theorem timely_temporalExpansion (formula : Formula Atom) (time : ℕ) :
    (formula.temporalExpansion time).Timely time := by
  induction formula <;> simp_all [Timely, temporalExpansion, Interval.shift]

end Formula

namespace Occurrence

variable {Atom : Type u}

/-- The horizon of the underlying (possibly marked) formula occurrence. -/
def horizon : Occurrence Atom → ℕ
  | .unmarked formula => formula.horizon
  | .markedEventually interval body | .markedAlways interval body =>
      interval.upper + body.horizon
  | .markedStrictUntil interval left right | .markedStrictRelease interval left right =>
      interval.upper + max left.horizon right.horizon

/-- Marked occurrences require no further expansion at the current instant. -/
def expansionWeight : Occurrence Atom → ℕ
  | .unmarked formula => formula.expansionWeight
  | _ => 0

/-- Timeliness of a marked or unmarked occurrence at a node time. -/
def Timely (time : ℕ) : Occurrence Atom → Prop
  | .unmarked formula => formula.Timely time
  | .markedEventually interval _ | .markedAlways interval _ => time < interval.upper
  | .markedStrictUntil interval _ _ | .markedStrictRelease interval _ _ =>
      time < interval.upper

@[simp]
theorem horizon_unmark (occurrence : Occurrence Atom) :
    occurrence.unmark.horizon = occurrence.horizon := by
  cases occurrence <;> rfl

theorem time_le_horizon_of_timely_of_temporal {occurrence : Occurrence Atom} {time : ℕ}
    (timely : occurrence.Timely time) (temporal : occurrence.isTemporal = true) :
    time ≤ occurrence.horizon := by
  cases occurrence with
  | unmarked formula =>
      cases formula <;>
        simp_all [Timely, horizon, Occurrence.isTemporal, Formula.isTemporal,
          Formula.Timely, Formula.horizon] <;> omega
  | markedEventually interval body =>
      simp only [Timely] at timely
      simp only [horizon]
      omega
  | markedAlways interval body =>
      simp only [Timely] at timely
      simp only [horizon]
      omega
  | markedStrictUntil interval left right =>
      simp only [Timely] at timely
      simp only [horizon]
      omega
  | markedStrictRelease interval left right =>
      simp only [Timely] at timely
      simp only [horizon]
      omega

end Occurrence

namespace Node

variable {Atom : Type u}

open scoped BigOperators

/-- Total expansion work in a finite node label. -/
def expansionWeight (node : Node Atom) : ℕ :=
  ∑ occurrence ∈ node.label, occurrence.expansionWeight

/-- Every formula occurrence has horizon at most `bound`. -/
def HorizonBounded (bound : ℕ) (node : Node Atom) : Prop :=
  ∀ occurrence ∈ node.label, occurrence.horizon ≤ bound

/-- Every exposed temporal occurrence is timely at the node's counter. -/
def Timely (node : Node Atom) : Prop :=
  ∀ occurrence ∈ node.label, occurrence.Timely node.time

@[simp]
theorem initial_horizonBounded (formula : Formula Atom) :
    (initial formula).HorizonBounded formula.horizon := by
  simp [HorizonBounded, initial, Occurrence.horizon]

@[simp]
theorem initial_timely (formula : Formula Atom) : (initial formula).Timely := by
  simp [Timely, initial, Occurrence.Timely]

private theorem sum_union_le [DecidableEq Atom]
    (left right : Finset (Occurrence Atom)) :
    ∑ occurrence ∈ left ∪ right, occurrence.expansionWeight ≤
      (∑ occurrence ∈ left, occurrence.expansionWeight) +
        ∑ occurrence ∈ right, occurrence.expansionWeight := by
  induction right using Finset.induction with
  | empty => simp
  | @insert occurrence right notMem ih =>
      by_cases inLeft : occurrence ∈ left
      · have inUnion : occurrence ∈ left ∪ right := Finset.mem_union_left right inLeft
        rw [Finset.sum_insert notMem]
        simp only [Finset.union_insert]
        simp [inUnion]
        omega
      · have notInUnion : occurrence ∉ left ∪ right := by simp [inLeft, notMem]
        rw [Finset.sum_insert notMem]
        simp only [Finset.union_insert, Finset.sum_insert notInUnion]
        omega

private theorem sum_toFinset_le [DecidableEq Atom] (occurrences : List (Occurrence Atom)) :
    ∑ occurrence ∈ occurrences.toFinset, occurrence.expansionWeight ≤
      (occurrences.map Occurrence.expansionWeight).sum := by
  induction occurrences with
  | nil => simp
  | cons occurrence occurrences ih =>
      simp only [List.toFinset_cons, List.map_cons, List.sum_cons]
      by_cases present : occurrence ∈ occurrences
      · rw [Finset.insert_eq_of_mem (by simpa using present)]
        exact Nat.le_add_left_of_le ih
      · rw [Finset.sum_insert (by simpa using present)]
        exact Nat.add_le_add_left ih _

theorem expansionWeight_replace_lt [DecidableEq Atom]
    (node : Node Atom) (selected : Occurrence Atom)
    (replacement : List (Occurrence Atom)) (present : selected ∈ node.label)
    (replacement_lt :
      (replacement.map Occurrence.expansionWeight).sum < selected.expansionWeight) :
    (node.replace selected replacement).expansionWeight < node.expansionWeight := by
  unfold expansionWeight replace
  simp only
  have union_le := sum_union_le (node.label.erase selected) replacement.toFinset
  have toFinset_le := sum_toFinset_le replacement
  rw [← Finset.sum_erase_add node.label Occurrence.expansionWeight present]
  omega

theorem horizonBounded_replace [DecidableEq Atom] {bound : ℕ} {node : Node Atom}
    {selected : Occurrence Atom} {replacement : List (Occurrence Atom)}
    (node_bounded : node.HorizonBounded bound)
    (replacement_bounded : ∀ occurrence ∈ replacement, occurrence.horizon ≤ bound) :
    (node.replace selected replacement).HorizonBounded bound := by
  intro occurrence occurrence_mem
  change occurrence ∈ node.label.erase selected ∪ replacement.toFinset at occurrence_mem
  rw [Finset.mem_union] at occurrence_mem
  rcases occurrence_mem with old_mem | replacement_mem
  · exact node_bounded occurrence (Finset.mem_of_mem_erase old_mem)
  · exact replacement_bounded occurrence (by simpa using replacement_mem)

theorem horizonBounded_replace_of_le [DecidableEq Atom] {bound : ℕ} {node : Node Atom}
    {selected : Occurrence Atom} {replacement : List (Occurrence Atom)}
    (node_bounded : node.HorizonBounded bound) (selected_mem : selected ∈ node.label)
    (replacement_le : ∀ occurrence ∈ replacement,
      occurrence.horizon ≤ selected.horizon) :
    (node.replace selected replacement).HorizonBounded bound := by
  apply horizonBounded_replace node_bounded
  intro occurrence occurrence_mem
  exact (replacement_le occurrence occurrence_mem).trans (node_bounded selected selected_mem)

theorem timely_replace [DecidableEq Atom] {node : Node Atom}
    {selected : Occurrence Atom} {replacement : List (Occurrence Atom)}
    (node_timely : node.Timely)
    (replacement_timely : ∀ occurrence ∈ replacement,
      occurrence.Timely node.time) :
    (node.replace selected replacement).Timely := by
  intro occurrence occurrence_mem
  change occurrence ∈ node.label.erase selected ∪ replacement.toFinset at occurrence_mem
  rw [Finset.mem_union] at occurrence_mem
  rcases occurrence_mem with old_mem | replacement_mem
  · exact node_timely occurrence (Finset.mem_of_mem_erase old_mem)
  · exact replacement_timely occurrence (by simpa using replacement_mem)

end Node

namespace Expansion

variable {Atom : Type u} [DecidableEq Atom]

theorem child_time {node child : Node Atom} {children : List (Node Atom)}
    (expansion : Expansion node children) (child_mem : child ∈ children) :
    child.time = node.time := by
  cases expansion with
  | disjunction =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl <;> rfl
  | conjunction =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      rfl
  | eventuallyBeforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl <;> rfl
  | eventuallyAtEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      rfl
  | alwaysBeforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      rfl
  | alwaysAtEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      rfl
  | strictUntilBeforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl <;> rfl
  | strictUntilAtEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      rfl
  | strictReleaseBeforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl <;> rfl
  | strictReleaseAtEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      rfl

theorem child_expansionWeight_lt {node child : Node Atom} {children : List (Node Atom)}
    (expansion : Expansion node children) (child_mem : child ∈ children) :
    child.expansionWeight < node.expansionWeight := by
  cases expansion with
  | disjunction left right present =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.expansionWeight_replace_lt _ _ _ present
        simp [Occurrence.expansionWeight, Formula.expansionWeight]
        omega
      · apply Node.expansionWeight_replace_lt _ _ _ present
        simp [Occurrence.expansionWeight, Formula.expansionWeight]
        omega
  | conjunction left right present =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.expansionWeight_replace_lt _ _ _ present
      simp [Occurrence.expansionWeight, Formula.expansionWeight]
  | eventuallyBeforeEnd interval body present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.expansionWeight_replace_lt _ _ _ present
        simp [Occurrence.expansionWeight, Formula.expansionWeight]
      · apply Node.expansionWeight_replace_lt _ _ _ present
        simp [Occurrence.expansionWeight, Formula.expansionWeight]
  | eventuallyAtEnd interval body present atEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.expansionWeight_replace_lt _ _ _ present
      simp [Occurrence.expansionWeight, Formula.expansionWeight]
  | alwaysBeforeEnd interval body present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.expansionWeight_replace_lt _ _ _ present
      simp [Occurrence.expansionWeight, Formula.expansionWeight]
  | alwaysAtEnd interval body present atEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.expansionWeight_replace_lt _ _ _ present
      simp [Occurrence.expansionWeight, Formula.expansionWeight]
  | strictUntilBeforeEnd interval left right present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.expansionWeight_replace_lt _ _ _ present
        simp [Occurrence.expansionWeight, Formula.expansionWeight]
        omega
      · apply Node.expansionWeight_replace_lt _ _ _ present
        simp [Occurrence.expansionWeight, Formula.expansionWeight]
        omega
  | strictUntilAtEnd interval left right present atEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.expansionWeight_replace_lt _ _ _ present
      simp [Occurrence.expansionWeight, Formula.expansionWeight]
      omega
  | strictReleaseBeforeEnd interval left right present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.expansionWeight_replace_lt _ _ _ present
        simp [Occurrence.expansionWeight, Formula.expansionWeight]
      · apply Node.expansionWeight_replace_lt _ _ _ present
        simp [Occurrence.expansionWeight, Formula.expansionWeight]
        omega
  | strictReleaseAtEnd interval left right present atEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.expansionWeight_replace_lt _ _ _ present
      simp [Occurrence.expansionWeight, Formula.expansionWeight]
      omega

theorem child_horizonBounded {bound : ℕ} {node child : Node Atom}
    {children : List (Node Atom)} (expansion : Expansion node children)
    (node_bounded : node.HorizonBounded bound) (child_mem : child ∈ children) :
    child.HorizonBounded bound := by
  cases expansion with
  | disjunction left right present =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.horizonBounded_replace_of_le node_bounded present
        intro occurrence occurrence_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
        subst occurrence
        exact Nat.le_max_left _ _
      · apply Node.horizonBounded_replace_of_le node_bounded present
        intro occurrence occurrence_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
        subst occurrence
        exact Nat.le_max_right _ _
  | conjunction left right present =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.horizonBounded_replace_of_le node_bounded present
      intro occurrence occurrence_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
      rcases occurrence_mem with rfl | rfl
      · exact Nat.le_max_left _ _
      · exact Nat.le_max_right _ _
  | eventuallyBeforeEnd interval body present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.horizonBounded_replace_of_le node_bounded present
        intro occurrence occurrence_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
        subst occurrence
        simp only [Occurrence.horizon, Formula.horizon]
        exact (Formula.horizon_temporalExpansion_le body node.time).trans
          (Nat.add_le_add_right (Nat.le_of_lt beforeEnd) _)
      · apply Node.horizonBounded_replace_of_le node_bounded present
        intro occurrence occurrence_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
        subst occurrence
        rfl
  | eventuallyAtEnd interval body present atEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.horizonBounded_replace_of_le node_bounded present
      intro occurrence occurrence_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
      subst occurrence
      simp only [Occurrence.horizon, Formula.horizon]
      simpa [atEnd] using Formula.horizon_temporalExpansion_le body node.time
  | alwaysBeforeEnd interval body present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.horizonBounded_replace_of_le node_bounded present
      intro occurrence occurrence_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
      rcases occurrence_mem with rfl | rfl
      · rfl
      · simp only [Occurrence.horizon, Formula.horizon]
        exact (Formula.horizon_temporalExpansion_le body node.time).trans
          (Nat.add_le_add_right (Nat.le_of_lt beforeEnd) _)
  | alwaysAtEnd interval body present atEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.horizonBounded_replace_of_le node_bounded present
      intro occurrence occurrence_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
      subst occurrence
      simp only [Occurrence.horizon, Formula.horizon]
      simpa [atEnd] using Formula.horizon_temporalExpansion_le body node.time
  | strictUntilBeforeEnd interval left right present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.horizonBounded_replace_of_le node_bounded present
        intro occurrence occurrence_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
        subst occurrence
        simp only [Occurrence.horizon, Formula.horizon]
        exact (Formula.horizon_temporalExpansion_le right node.time).trans
          (Nat.add_le_add (Nat.le_of_lt beforeEnd) (Nat.le_max_right _ _))
      · apply Node.horizonBounded_replace_of_le node_bounded present
        intro occurrence occurrence_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
        rcases occurrence_mem with rfl | rfl
        · rfl
        · simp only [Occurrence.horizon, Formula.horizon]
          exact (Formula.horizon_temporalExpansion_le left node.time).trans
            (Nat.add_le_add (Nat.le_of_lt beforeEnd) (Nat.le_max_left _ _))
  | strictUntilAtEnd interval left right present atEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.horizonBounded_replace_of_le node_bounded present
      intro occurrence occurrence_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
      subst occurrence
      simp only [Occurrence.horizon, Formula.horizon]
      exact (Formula.horizon_temporalExpansion_le right node.time).trans
        (Nat.add_le_add (Nat.le_of_eq atEnd) (Nat.le_max_right _ _))
  | strictReleaseBeforeEnd interval left right present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.horizonBounded_replace_of_le node_bounded present
        intro occurrence occurrence_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
        rcases occurrence_mem with rfl | rfl
        · simp only [Occurrence.horizon, Formula.horizon]
          exact (Formula.horizon_temporalExpansion_le left node.time).trans
            (Nat.add_le_add (Nat.le_of_lt beforeEnd) (Nat.le_max_left _ _))
        · simp only [Occurrence.horizon, Formula.horizon]
          exact (Formula.horizon_temporalExpansion_le right node.time).trans
            (Nat.add_le_add (Nat.le_of_lt beforeEnd) (Nat.le_max_right _ _))
      · apply Node.horizonBounded_replace_of_le node_bounded present
        intro occurrence occurrence_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
        rcases occurrence_mem with rfl | rfl
        · rfl
        · simp only [Occurrence.horizon, Formula.horizon]
          exact (Formula.horizon_temporalExpansion_le right node.time).trans
            (Nat.add_le_add (Nat.le_of_lt beforeEnd) (Nat.le_max_right _ _))
  | strictReleaseAtEnd interval left right present atEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.horizonBounded_replace_of_le node_bounded present
      intro occurrence occurrence_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
      subst occurrence
      simp only [Occurrence.horizon, Formula.horizon]
      exact (Formula.horizon_temporalExpansion_le right node.time).trans
        (Nat.add_le_add (Nat.le_of_eq atEnd) (Nat.le_max_right _ _))

theorem child_timely {node child : Node Atom} {children : List (Node Atom)}
    (expansion : Expansion node children) (node_timely : node.Timely)
    (child_mem : child ∈ children) : child.Timely := by
  cases expansion with
  | disjunction left right present =>
      have selected_timely := node_timely (.unmarked (.or left right)) present
      simp only [Occurrence.Timely, Formula.Timely] at selected_timely
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.timely_replace node_timely
        intro occurrence occurrence_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
        subst occurrence
        exact selected_timely.1
      · apply Node.timely_replace node_timely
        intro occurrence occurrence_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
        subst occurrence
        exact selected_timely.2
  | conjunction left right present =>
      have selected_timely := node_timely (.unmarked (.and left right)) present
      simp only [Occurrence.Timely, Formula.Timely] at selected_timely
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.timely_replace node_timely
      intro occurrence occurrence_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
      rcases occurrence_mem with rfl | rfl
      · exact selected_timely.1
      · exact selected_timely.2
  | eventuallyBeforeEnd interval body present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.timely_replace node_timely
        intro occurrence occurrence_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
        subst occurrence
        exact Formula.timely_temporalExpansion body node.time
      · apply Node.timely_replace node_timely
        intro occurrence occurrence_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
        subst occurrence
        exact beforeEnd
  | eventuallyAtEnd interval body present atEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.timely_replace node_timely
      intro occurrence occurrence_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
      subst occurrence
      exact Formula.timely_temporalExpansion body node.time
  | alwaysBeforeEnd interval body present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.timely_replace node_timely
      intro occurrence occurrence_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
      rcases occurrence_mem with rfl | rfl
      · exact beforeEnd
      · exact Formula.timely_temporalExpansion body node.time
  | alwaysAtEnd interval body present atEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.timely_replace node_timely
      intro occurrence occurrence_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
      subst occurrence
      exact Formula.timely_temporalExpansion body node.time
  | strictUntilBeforeEnd interval left right present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.timely_replace node_timely
        intro occurrence occurrence_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
        subst occurrence
        exact Formula.timely_temporalExpansion right node.time
      · apply Node.timely_replace node_timely
        intro occurrence occurrence_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
        rcases occurrence_mem with rfl | rfl
        · exact beforeEnd
        · exact Formula.timely_temporalExpansion left node.time
  | strictUntilAtEnd interval left right present atEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.timely_replace node_timely
      intro occurrence occurrence_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
      subst occurrence
      exact Formula.timely_temporalExpansion right node.time
  | strictReleaseBeforeEnd interval left right present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      rcases child_mem with rfl | rfl
      · apply Node.timely_replace node_timely
        intro occurrence occurrence_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
        rcases occurrence_mem with rfl | rfl
        · exact Formula.timely_temporalExpansion left node.time
        · exact Formula.timely_temporalExpansion right node.time
      · apply Node.timely_replace node_timely
        intro occurrence occurrence_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
        rcases occurrence_mem with rfl | rfl
        · exact beforeEnd
        · exact Formula.timely_temporalExpansion right node.time
  | strictReleaseAtEnd interval left right present atEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Node.timely_replace node_timely
      intro occurrence occurrence_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence_mem
      subst occurrence
      exact Formula.timely_temporalExpansion right node.time

end Expansion

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

theorem step_horizonBounded {bound : ℕ} {node : Node Atom}
    (node_bounded : node.HorizonBounded bound) : node.step.HorizonBounded bound := by
  intro occurrence occurrence_mem
  change occurrence ∈ node.stepLabel at occurrence_mem
  rw [stepLabel, Finset.mem_union] at occurrence_mem
  rcases occurrence_mem with unmarked_mem | marked_mem
  · exact node_bounded occurrence (Finset.mem_filter.mp unmarked_mem).1
  · rcases Finset.mem_image.mp marked_mem with ⟨source, source_mem, rfl⟩
    rw [Occurrence.horizon_unmark]
    exact node_bounded source (Finset.mem_filter.mp source_mem).1

private theorem unmarkedTemporal_timely_succ {node : Node Atom} {formula : Formula Atom}
    (present : Occurrence.unmarked formula ∈ node.label)
    (temporal : formula.isTemporal = true) (node_timely : node.Timely)
    (poised : node.Poised) : formula.Timely (node.time + 1) := by
  have timely := node_timely (.unmarked formula) present
  cases formula with
  | truth => simp [Formula.isTemporal] at temporal
  | atom atom => simp [Formula.isTemporal] at temporal
  | neg body => simp [Formula.isTemporal] at temporal
  | and left right => simp [Formula.isTemporal] at temporal
  | or left right => simp [Formula.isTemporal] at temporal
  | eventually interval body =>
      simp only [Occurrence.Timely, Formula.Timely] at timely
      simp only [Formula.Timely]
      by_contra not_timely
      have atEnd : node.time = interval.upper := by omega
      exact poised ⟨_, Expansion.eventuallyAtEnd interval body present atEnd⟩
  | always interval body =>
      simp only [Occurrence.Timely, Formula.Timely] at timely
      simp only [Formula.Timely]
      by_contra not_timely
      have atEnd : node.time = interval.upper := by omega
      exact poised ⟨_, Expansion.alwaysAtEnd interval body present atEnd⟩
  | strictUntil interval left right =>
      simp only [Occurrence.Timely, Formula.Timely] at timely
      simp only [Formula.Timely]
      by_contra not_timely
      have atEnd : node.time = interval.upper := by omega
      exact poised ⟨_, Expansion.strictUntilAtEnd interval left right present atEnd⟩
  | strictRelease interval left right =>
      simp only [Occurrence.Timely, Formula.Timely] at timely
      simp only [Formula.Timely]
      by_contra not_timely
      have atEnd : node.time = interval.upper := by omega
      exact poised ⟨_, Expansion.strictReleaseAtEnd interval left right present atEnd⟩

theorem step_timely {node : Node Atom} (node_timely : node.Timely)
    (poised : node.Poised) : node.step.Timely := by
  intro occurrence occurrence_mem
  change occurrence.Timely (node.time + 1)
  change occurrence ∈ node.stepLabel at occurrence_mem
  rw [stepLabel, Finset.mem_union] at occurrence_mem
  rcases occurrence_mem with unmarked_mem | marked_mem
  · have present := (Finset.mem_filter.mp unmarked_mem).1
    have temporal := (Finset.mem_filter.mp unmarked_mem).2
    cases occurrence with
    | unmarked formula =>
        exact unmarkedTemporal_timely_succ present temporal node_timely poised
    | markedEventually interval body =>
        simp [Occurrence.isUnmarkedTemporal] at temporal
    | markedAlways interval body =>
        simp [Occurrence.isUnmarkedTemporal] at temporal
    | markedStrictUntil interval left right =>
        simp [Occurrence.isUnmarkedTemporal] at temporal
    | markedStrictRelease interval left right =>
        simp [Occurrence.isUnmarkedTemporal] at temporal
  · rcases Finset.mem_image.mp marked_mem with ⟨source, source_mem, rfl⟩
    have continues := (Finset.mem_filter.mp source_mem).2
    cases source <;>
      simp_all [Occurrence.markedContinuesAt, Occurrence.unmark, Occurrence.Timely,
        Formula.Timely] <;> omega

omit [DecidableEq Atom] in
theorem time_le_of_horizonBounded_of_timely_of_containsTemporal {bound : ℕ}
    {node : Node Atom} (node_bounded : node.HorizonBounded bound)
    (node_timely : node.Timely) (contains_temporal : node.ContainsTemporal) :
    node.time ≤ bound := by
  rcases contains_temporal with ⟨occurrence, occurrence_mem, temporal⟩
  exact (Occurrence.time_le_horizon_of_timely_of_temporal
    (node_timely occurrence occurrence_mem) temporal).trans
      (node_bounded occurrence occurrence_mem)

/--
The lexicographic termination measure: remaining bounded time is primary and
the amount of same-time expansion work is secondary.
-/
def terminationMeasure (bound : ℕ) (node : Node Atom) : ℕ × ℕ :=
  (bound + 1 - node.time, node.expansionWeight)

end Node

/-- Choosing one child produced by one application of a basic-tableau rule. -/
def BasicChild {Atom : Type u} [DecidableEq Atom]
    (semantics : AtomicSemantics Atom) (child parent : Node Atom) : Prop :=
  ∃ children, BasicRule semantics parent children ∧ child ∈ children

namespace BasicChild

variable {Atom : Type u} [DecidableEq Atom] {semantics : AtomicSemantics Atom}

theorem horizonBounded {bound : ℕ} {parent child : Node Atom}
    (child_of : BasicChild semantics child parent)
    (parent_bounded : parent.HorizonBounded bound) : child.HorizonBounded bound := by
  rcases child_of with ⟨children, rule, child_mem⟩
  cases rule with
  | expand notRejected expansion =>
      exact expansion.child_horizonBounded parent_bounded child_mem
  | step notRejected poised hasTemporal =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      exact Node.step_horizonBounded parent_bounded

theorem timely {parent child : Node Atom} (child_of : BasicChild semantics child parent)
    (parent_timely : parent.Timely) : child.Timely := by
  rcases child_of with ⟨children, rule, child_mem⟩
  cases rule with
  | expand notRejected expansion => exact expansion.child_timely parent_timely child_mem
  | step notRejected poised hasTemporal =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      exact Node.step_timely parent_timely poised

theorem terminationMeasure_decreases {bound : ℕ} {parent child : Node Atom}
    (child_of : BasicChild semantics child parent)
    (parent_bounded : parent.HorizonBounded bound) (parent_timely : parent.Timely) :
    Prod.Lex (fun left right : ℕ ↦ left < right) (fun left right : ℕ ↦ left < right)
      (child.terminationMeasure bound) (parent.terminationMeasure bound) := by
  rcases child_of with ⟨children, rule, child_mem⟩
  cases rule with
  | expand notRejected expansion =>
      rw [Node.terminationMeasure, Node.terminationMeasure, expansion.child_time child_mem]
      exact Prod.Lex.right _ (expansion.child_expansionWeight_lt child_mem)
  | step notRejected poised hasTemporal =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at child_mem
      subst child
      apply Prod.Lex.left _ _
      have time_le := Node.time_le_of_horizonBounded_of_timely_of_containsTemporal
        parent_bounded parent_timely hasTemporal
      simp only [Node.step]
      omega

end BasicChild

private theorem terminationMeasure_wellFounded {Atom : Type u} (bound : ℕ) :
    WellFounded
      (InvImage
        (Prod.Lex (fun left right : ℕ ↦ left < right)
          (fun left right : ℕ ↦ left < right))
        (Node.terminationMeasure (Atom := Atom) bound)) :=
  InvImage.wf _ (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf)

/-- Every horizon-bounded, timely node is accessible for basic-tableau child steps. -/
theorem basicChild_accessible_of_invariants {Atom : Type u} [DecidableEq Atom]
    {semantics : AtomicSemantics Atom} {bound : ℕ} {node : Node Atom}
    (node_bounded : node.HorizonBounded bound) (node_timely : node.Timely) :
    Acc (BasicChild semantics) node := by
  let relation :=
    InvImage
      (Prod.Lex (fun left right : ℕ ↦ left < right)
        (fun left right : ℕ ↦ left < right))
      (Node.terminationMeasure (Atom := Atom) bound)
  have relation_wf : WellFounded relation := terminationMeasure_wellFounded bound
  refine relation_wf.induction node (C := fun current ↦
    current.HorizonBounded bound → current.Timely →
      Acc (BasicChild semantics) current) ?_ node_bounded node_timely
  intro parent ih parent_bounded parent_timely
  apply Acc.intro parent
  intro child child_of
  exact ih child
    (BasicChild.terminationMeasure_decreases child_of parent_bounded parent_timely)
    (BasicChild.horizonBounded child_of parent_bounded)
    (BasicChild.timely child_of parent_timely)

/-- The initial node of every STL formula is accessible for basic-tableau rules. -/
theorem basicChild_initial_accessible {Atom : Type u} [DecidableEq Atom]
    (semantics : AtomicSemantics Atom) (formula : Formula Atom) :
    Acc (BasicChild semantics) (Node.initial formula) :=
  basicChild_accessible_of_invariants
    (Node.initial_horizonBounded formula) (Node.initial_timely formula)

/--
No infinite basic-tableau branch starts at the initial node.  Since
`TableauTree` is an inductive finite-tree type, this is the nontrivial
operational content of the paper's termination theorem.
-/
theorem no_infinite_basic_tableau_branch {Atom : Type u} [DecidableEq Atom]
    (semantics : AtomicSemantics Atom) (formula : Formula Atom) :
    ¬∃ branch : ℕ → Node Atom,
      branch 0 = Node.initial formula ∧
        ∀ index, BasicChild semantics (branch (index + 1)) (branch index) := by
  intro infinite_branch
  have no_chain := acc_iff_isEmpty_descending_chain.mp
    (basicChild_initial_accessible semantics formula)
  rcases infinite_branch with ⟨branch, starts_at, follows_rules⟩
  exact no_chain.false ⟨branch, starts_at, follows_rules⟩

end Stlsat
