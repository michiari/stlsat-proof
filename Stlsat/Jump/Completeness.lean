import Stlsat.Jump.UnconditionalSoundness
import Stlsat.Jump.CompletenessSplicing

/-!
# Completeness guard regression

The revised completeness conflict set contains all of `O(u)`.  This file
checks the concrete configuration that previously refuted completeness: its
postponed target now overlaps the target of an independent singleton
eventuality, so `CompleteSafe` disables the offending JUMP.
-/

namespace Stlsat.Jump.CompletenessGuardRegression

inductive Atom where | p
deriving DecidableEq

def interval (lower upper : Nat) (valid : lower ≤ upper := by omega) : Stlsat.Interval :=
  ⟨lower, upper, valid⟩

def p : Stlsat.Formula Atom := .atom .p
def np : Stlsat.Formula Atom := .neg p
def inner : Stlsat.Formula Atom := .eventually (interval 2 2) p
def negative2 : Stlsat.Formula Atom := .eventually (interval 2 2) np

def postponed : AnnotatedOccurrence Atom :=
  ⟨[0], .markedEventually (interval 0 2) inner, none⟩

def blocker : AnnotatedOccurrence Atom :=
  ⟨[1], .unmarked negative2, none⟩

def node : Node Atom where
  time := 0
  label := {postponed, blocker}

def targetValidity : ValidityOccurrence :=
  ⟨[0], interval 2 2⟩

def blockerValidity : ValidityOccurrence :=
  ⟨[0, 0], interval 2 2⟩

def targetWindow : WindowOccurrence :=
  (WindowOccurrence.ofValidity (postponed.id ++ [0]) targetValidity).shift node.time

def blockerWindow : WindowOccurrence :=
  WindowOccurrence.ofValidity blocker.id blockerValidity

theorem targetWindow_mem : targetWindow ∈ node.targetWindows := by
  apply node.targetWindow_mem postponed (by decide) 0 inner
  · rfl
  · decide

theorem blockerWindow_mem_independent : blockerWindow ∈ node.independentWindows := by
  apply node.independentWindow_mem blocker (by decide)
  · decide
  · simp [Node.ParentActive, blocker, node]
  · decide

theorem blockerWindow_mem_conflict : blockerWindow ∈ node.conflictWindows :=
  node.independentWindow_mem_conflictWindows blockerWindow
    blockerWindow_mem_independent

/-- The former counterexample's initial JUMP is disabled by the revised guard. -/
theorem not_completeSafe : ¬node.CompleteSafe := by
  intro complete
  exact complete targetWindow targetWindow_mem blockerWindow
    blockerWindow_mem_conflict
      (by simp [Node.DistinctAtoms, targetWindow, blockerWindow,
        postponed, blocker, targetValidity, blockerValidity, node,
        WindowOccurrence.shift, WindowOccurrence.ofValidity])
      (by simp [Node.WindowsOverlap, targetWindow, blockerWindow,
        postponed, blocker, targetValidity, blockerValidity, node, interval,
        WindowOccurrence.shift, WindowOccurrence.ofValidity, Stlsat.Interval.shift])

end Stlsat.Jump.CompletenessGuardRegression

namespace Stlsat.Jump

universe u

namespace Expansion

variable {Atom : Type u} [DecidableEq Atom]

/-- The ordinary expansion rules retain their model-guided completeness law
with occurrence identifiers and parent annotations. -/
theorem exists_child_satisfiedBy {node : Node Atom} {children : List (Node Atom)}
    {semantics : Stlsat.AtomicSemantics Atom} {signal : Stlsat.Signal semantics}
    (expansion : Expansion node children)
    (parentHolds : node.SatisfiedBy semantics signal) :
    ∃ child ∈ children, child.SatisfiedBy semantics signal := by
  cases expansion with
  | disjunction selected left right shape present =>
      have selectedHolds := (Node.satisfiedBy_iff node semantics signal).1
        parentHolds selected present
      simp only [AnnotatedOccurrence.SatisfiedBy, shape,
        Stlsat.Occurrence.SatisfiedBy, Stlsat.Formula.SatisfiesFrom] at selectedHolds
      rcases selectedHolds with leftHolds | rightHolds
      · refine ⟨node.replace selected
          [selected.child 0 (.unmarked left) selected.parent], by simp, ?_⟩
        apply Node.satisfiedBy_replace_of parentHolds
        intro occurrence occurrenceMem
        simp only [List.mem_singleton] at occurrenceMem
        subst occurrence
        simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
          Stlsat.Occurrence.SatisfiedBy,
          Stlsat.Formula.SatisfiesFrom] using leftHolds
      · refine ⟨node.replace selected
          [selected.child 1 (.unmarked right) selected.parent], by simp, ?_⟩
        apply Node.satisfiedBy_replace_of parentHolds
        intro occurrence occurrenceMem
        simp only [List.mem_singleton] at occurrenceMem
        subst occurrence
        simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
          Stlsat.Occurrence.SatisfiedBy,
          Stlsat.Formula.SatisfiesFrom] using rightHolds
  | conjunction selected left right shape present =>
      have selectedHolds := (Node.satisfiedBy_iff node semantics signal).1
        parentHolds selected present
      simp only [AnnotatedOccurrence.SatisfiedBy, shape,
        Stlsat.Occurrence.SatisfiedBy, Stlsat.Formula.SatisfiesFrom] at selectedHolds
      refine ⟨node.replace selected
        [selected.child 0 (.unmarked left) selected.parent,
         selected.child 1 (.unmarked right) selected.parent], by simp, ?_⟩
      apply Node.satisfiedBy_replace_of parentHolds
      intro occurrence occurrenceMem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMem
      rcases occurrenceMem with rfl | rfl
      · simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
          Stlsat.Occurrence.SatisfiedBy,
          Stlsat.Formula.SatisfiesFrom] using selectedHolds.1
      · simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
          Stlsat.Occurrence.SatisfiedBy,
          Stlsat.Formula.SatisfiesFrom] using selectedHolds.2
  | eventuallyBeforeEnd selected interval body shape present active beforeEnd =>
      have selectedHolds := (Node.satisfiedBy_iff node semantics signal).1
        parentHolds selected present
      simp only [AnnotatedOccurrence.SatisfiedBy, shape,
        Stlsat.Occurrence.SatisfiedBy] at selectedHolds
      rcases Stlsat.Formula.eventually_now_or_later active selectedHolds with now | later
      · refine ⟨node.replace selected
          [selected.child 0 (.unmarked (body.temporalExpansion node.time)) none],
          by simp, ?_⟩
        apply Node.satisfiedBy_replace_of parentHolds
        intro occurrence occurrenceMem
        simp only [List.mem_singleton] at occurrenceMem
        subst occurrence
        simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
          Stlsat.Occurrence.SatisfiedBy] using now
      · refine ⟨node.replace selected
          [selected.relabel (.markedEventually interval body)], by simp, ?_⟩
        apply Node.satisfiedBy_replace_of parentHolds
        intro occurrence occurrenceMem
        simp only [List.mem_singleton] at occurrenceMem
        subst occurrence
        simpa [AnnotatedOccurrence.relabel, AnnotatedOccurrence.SatisfiedBy,
          Stlsat.Occurrence.SatisfiedBy] using later
  | eventuallyAtEnd selected interval body shape present atEnd =>
      have selectedHolds := (Node.satisfiedBy_iff node semantics signal).1
        parentHolds selected present
      simp only [AnnotatedOccurrence.SatisfiedBy, shape,
        Stlsat.Occurrence.SatisfiedBy] at selectedHolds
      have now := (Stlsat.Formula.eventually_atEnd_iff atEnd).mp selectedHolds
      refine ⟨node.replace selected
        [selected.child 0 (.unmarked (body.temporalExpansion node.time)) none],
        by simp, ?_⟩
      apply Node.satisfiedBy_replace_of parentHolds
      intro occurrence occurrenceMem
      simp only [List.mem_singleton] at occurrenceMem
      subst occurrence
      simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
        Stlsat.Occurrence.SatisfiedBy] using now
  | alwaysBeforeEnd selected interval body shape present active beforeEnd =>
      have selectedHolds := (Node.satisfiedBy_iff node semantics signal).1
        parentHolds selected present
      simp only [AnnotatedOccurrence.SatisfiedBy, shape,
        Stlsat.Occurrence.SatisfiedBy] at selectedHolds
      rcases Stlsat.Formula.always_now_and_later active beforeEnd selectedHolds with
        ⟨now, later⟩
      refine ⟨node.replace selected
        [selected.relabel (.markedAlways interval body),
         selected.child 0 (.unmarked (body.temporalExpansion node.time))
           (some selected.reference)], by simp, ?_⟩
      apply Node.satisfiedBy_replace_of parentHolds
      intro occurrence occurrenceMem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMem
      rcases occurrenceMem with rfl | rfl
      · simpa [AnnotatedOccurrence.relabel, AnnotatedOccurrence.SatisfiedBy,
          Stlsat.Occurrence.SatisfiedBy] using later
      · simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
          Stlsat.Occurrence.SatisfiedBy] using now
  | alwaysAtEnd selected interval body shape present atEnd =>
      have selectedHolds := (Node.satisfiedBy_iff node semantics signal).1
        parentHolds selected present
      simp only [AnnotatedOccurrence.SatisfiedBy, shape,
        Stlsat.Occurrence.SatisfiedBy] at selectedHolds
      have now := (Stlsat.Formula.always_atEnd_iff atEnd).mp selectedHolds
      refine ⟨node.replace selected
        [selected.child 0 (.unmarked (body.temporalExpansion node.time))
          (some selected.reference)], by simp, ?_⟩
      apply Node.satisfiedBy_replace_of parentHolds
      intro occurrence occurrenceMem
      simp only [List.mem_singleton] at occurrenceMem
      subst occurrence
      simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
        Stlsat.Occurrence.SatisfiedBy] using now
  | strictUntilBeforeEnd selected interval invariant target shape present active beforeEnd =>
      have selectedHolds := (Node.satisfiedBy_iff node semantics signal).1
        parentHolds selected present
      simp only [AnnotatedOccurrence.SatisfiedBy, shape,
        Stlsat.Occurrence.SatisfiedBy] at selectedHolds
      rcases Stlsat.Formula.strictUntil_now_or_later active selectedHolds with
        now | ⟨invariantNow, later⟩
      · refine ⟨node.replace selected
          [selected.child 1 (.unmarked (target.temporalExpansion node.time)) none],
          by simp, ?_⟩
        apply Node.satisfiedBy_replace_of parentHolds
        intro occurrence occurrenceMem
        simp only [List.mem_singleton] at occurrenceMem
        subst occurrence
        simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
          Stlsat.Occurrence.SatisfiedBy] using now
      · refine ⟨node.replace selected
          [selected.relabel (.markedStrictUntil interval invariant target),
           selected.child 0 (.unmarked (invariant.temporalExpansion node.time))
             (some selected.reference)], by simp, ?_⟩
        apply Node.satisfiedBy_replace_of parentHolds
        intro occurrence occurrenceMem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMem
        rcases occurrenceMem with rfl | rfl
        · simpa [AnnotatedOccurrence.relabel, AnnotatedOccurrence.SatisfiedBy,
            Stlsat.Occurrence.SatisfiedBy] using later
        · simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
            Stlsat.Occurrence.SatisfiedBy]
            using invariantNow
  | strictUntilAtEnd selected interval invariant target shape present atEnd =>
      have selectedHolds := (Node.satisfiedBy_iff node semantics signal).1
        parentHolds selected present
      simp only [AnnotatedOccurrence.SatisfiedBy, shape,
        Stlsat.Occurrence.SatisfiedBy] at selectedHolds
      have now := (Stlsat.Formula.strictUntil_atEnd_iff atEnd).mp selectedHolds
      refine ⟨node.replace selected
        [selected.child 1 (.unmarked (target.temporalExpansion node.time)) none],
        by simp, ?_⟩
      apply Node.satisfiedBy_replace_of parentHolds
      intro occurrence occurrenceMem
      simp only [List.mem_singleton] at occurrenceMem
      subst occurrence
      simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
        Stlsat.Occurrence.SatisfiedBy] using now
  | strictReleaseBeforeEnd selected interval target invariant shape present active beforeEnd =>
      have selectedHolds := (Node.satisfiedBy_iff node semantics signal).1
        parentHolds selected present
      simp only [AnnotatedOccurrence.SatisfiedBy, shape,
        Stlsat.Occurrence.SatisfiedBy] at selectedHolds
      rcases Stlsat.Formula.strictRelease_now_or_later active beforeEnd selectedHolds with
        ⟨targetNow, invariantNow⟩ | ⟨invariantNow, later⟩
      · refine ⟨node.replace selected
          [selected.child 0 (.unmarked (target.temporalExpansion node.time)) none,
           selected.child 1 (.unmarked (invariant.temporalExpansion node.time)) none],
          by simp, ?_⟩
        apply Node.satisfiedBy_replace_of parentHolds
        intro occurrence occurrenceMem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMem
        rcases occurrenceMem with rfl | rfl
        · simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
            Stlsat.Occurrence.SatisfiedBy]
            using targetNow
        · simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
            Stlsat.Occurrence.SatisfiedBy]
            using invariantNow
      · refine ⟨node.replace selected
          [selected.relabel (.markedStrictRelease interval target invariant),
           selected.child 1 (.unmarked (invariant.temporalExpansion node.time))
             (some selected.reference)], by simp, ?_⟩
        apply Node.satisfiedBy_replace_of parentHolds
        intro occurrence occurrenceMem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMem
        rcases occurrenceMem with rfl | rfl
        · simpa [AnnotatedOccurrence.relabel, AnnotatedOccurrence.SatisfiedBy,
            Stlsat.Occurrence.SatisfiedBy] using later
        · simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
            Stlsat.Occurrence.SatisfiedBy]
            using invariantNow
  | strictReleaseAtEnd selected interval target invariant shape present atEnd =>
      have selectedHolds := (Node.satisfiedBy_iff node semantics signal).1
        parentHolds selected present
      simp only [AnnotatedOccurrence.SatisfiedBy, shape,
        Stlsat.Occurrence.SatisfiedBy] at selectedHolds
      have now := (Stlsat.Formula.strictRelease_atEnd_iff atEnd).mp selectedHolds
      refine ⟨node.replace selected
        [selected.child 1 (.unmarked (invariant.temporalExpansion node.time))
          (some selected.reference)], by simp, ?_⟩
      apply Node.satisfiedBy_replace_of parentHolds
      intro occurrence occurrenceMem
      simp only [List.mem_singleton] at occurrenceMem
      subst occurrence
      simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
        Stlsat.Occurrence.SatisfiedBy] using now

theorem exists_child_hasModel {node : Node Atom} {children : List (Node Atom)}
    {semantics : Stlsat.AtomicSemantics Atom} (expansion : Expansion node children)
    (model : node.HasModel semantics) :
    ∃ child ∈ children, child.HasModel semantics := by
  rcases model with ⟨model⟩
  rcases expansion.exists_child_satisfiedBy model.satisfies with
    ⟨child, childMem, childHolds⟩
  exact ⟨child, childMem, ⟨⟨model.signal, childHolds⟩⟩⟩

/-- A modeled sibling of a selected child in a binary expansion.  Encoding
the side in the constructor retains the branch information even when the two
child roots happen to be equal as finite labels. -/
inductive SiblingHasModel (semantics : Stlsat.AtomicSemantics Atom)
    (parent : Node Atom) :
    List (Node Atom) → Node Atom → Prop where
  | ofLeft {left right : Node Atom} (model : left.HasModel semantics)
      (escapeLifts : ∀ _escape : left.TargetEscape semantics,
        Nonempty (parent.TargetEscape semantics)) :
      SiblingHasModel semantics parent [left, right] right
  | ofRight {left right : Node Atom} (model : right.HasModel semantics)
      (escapeLifts : ∀ _escape : right.TargetEscape semantics,
        Nonempty (parent.TargetEscape semantics)) :
      SiblingHasModel semantics parent [left, right] left

/-- If the selected child is the left child, a sibling witness supplies a
model of the right child and routes all of its escapes to the parent.  This
eliminator is deliberately insensitive to the degenerate case in which the
two child roots are equal. -/
theorem SiblingHasModel.other_of_left {semantics : Stlsat.AtomicSemantics Atom}
    {parent left right : Node Atom}
    (sibling : SiblingHasModel semantics parent [left, right] left) :
    right.HasModel semantics ∧
      (∀ escape : right.TargetEscape semantics,
        Nonempty (parent.TargetEscape semantics)) := by
  cases sibling with
  | ofLeft model escapeLifts => exact ⟨model, escapeLifts⟩
  | ofRight model escapeLifts => exact ⟨model, escapeLifts⟩

/-- Symmetric eliminator for a selected right child. -/
theorem SiblingHasModel.other_of_right {semantics : Stlsat.AtomicSemantics Atom}
    {parent left right : Node Atom}
    (sibling : SiblingHasModel semantics parent [left, right] right) :
    left.HasModel semantics ∧
      (∀ escape : left.TargetEscape semantics,
        Nonempty (parent.TargetEscape semantics)) := by
  cases sibling with
  | ofLeft model escapeLifts => exact ⟨model, escapeLifts⟩
  | ofRight model escapeLifts => exact ⟨model, escapeLifts⟩

/-- An escape returned by a child either comes from an old occurrence and
lifts to the expansion parent, or comes from the newly marked residual of a
postpone child; in that case it supplies a model for the sibling which
satisfies the temporal target now. -/
theorem targetEscape_parent_or_alternate {node child : Node Atom}
    {children : List (Node Atom)} {semantics : Stlsat.AtomicSemantics Atom}
    (expansion : Expansion node children) (childMem : child ∈ children)
    (escape : child.TargetEscape semantics) :
    Nonempty (node.TargetEscape semantics) ∨
      SiblingHasModel semantics node children child := by
  have parentHolds := expansion.satisfiedBy_parent childMem escape.nodeHolds
  cases expansion with
  | disjunction selected left right shape present =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      rcases childMem with rfl | rfl
      · left
        exact escape.lift_of_replace (by
          intro fresh freshMem
          simp only [List.mem_singleton] at freshMem
          subst fresh
          simp [AnnotatedOccurrence.child, AnnotatedOccurrence.postponedTarget?]) parentHolds
      · left
        exact escape.lift_of_replace (by
          intro fresh freshMem
          simp only [List.mem_singleton] at freshMem
          subst fresh
          simp [AnnotatedOccurrence.child, AnnotatedOccurrence.postponedTarget?]) parentHolds
  | conjunction selected left right shape present =>
      simp only [List.mem_singleton] at childMem
      subst child
      left
      exact escape.lift_of_replace (by
        intro fresh freshMem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at freshMem
        rcases freshMem with rfl | rfl <;>
          simp [AnnotatedOccurrence.child, AnnotatedOccurrence.postponedTarget?]) parentHolds
  | eventuallyBeforeEnd selected interval body shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      rcases childMem with rfl | rfl
      · left
        exact escape.lift_of_replace (by
          intro fresh freshMem
          simp only [List.mem_singleton] at freshMem
          subst fresh
          simp [AnnotatedOccurrence.child, AnnotatedOccurrence.postponedTarget?]) parentHolds
      · have sourceMem := escape.sourceMem
        change escape.source ∈ node.label.erase selected ∪
          [selected.relabel (.markedEventually interval body)].toFinset at sourceMem
        rcases Finset.mem_union.mp sourceMem with old | fresh
        · left
          exact ⟨escape.lift rfl (Finset.mem_of_mem_erase old) parentHolds⟩
        · right
          simp only [List.toFinset_cons, List.toFinset_nil, Finset.union_empty,
            Finset.mem_singleton] at fresh
          have sourceEq : escape.source =
              selected.relabel (.markedEventually interval body) := by
            simpa using fresh
          have escapeShape := escape.shape
          rw [sourceEq] at escapeShape
          simp only [AnnotatedOccurrence.relabel,
            AnnotatedOccurrence.postponedTarget?, Option.some.injEq,
            Prod.mk.injEq] at escapeShape
          rcases escapeShape with ⟨_, targetEq⟩
          have escapeTargetHolds : escape.target.Satisfies semantics
              escape.signal node.time := by
            simpa [Node.replace] using escape.targetHolds
          have escapedTarget : body.Satisfies semantics escape.signal node.time := by
            simpa only [targetEq] using escapeTargetHolds
          apply SiblingHasModel.ofLeft
          · refine ⟨⟨escape.signal, ?_⟩⟩
            apply Node.satisfiedBy_replace_of parentHolds
            intro occurrence occurrenceMem
            simp only [List.mem_singleton] at occurrenceMem
            subst occurrence
            simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
              Stlsat.Occurrence.SatisfiedBy] using escapedTarget
          · intro siblingEscape
            apply siblingEscape.lift_of_replace
            · intro fresh freshMem
              simp only [List.mem_singleton] at freshMem
              subst fresh
              simp [AnnotatedOccurrence.child,
                AnnotatedOccurrence.postponedTarget?]
            · exact (Expansion.eventuallyBeforeEnd selected interval body shape
                present active beforeEnd).satisfiedBy_parent (by simp)
                  siblingEscape.nodeHolds
  | eventuallyAtEnd selected interval body shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      left
      exact escape.lift_of_replace (by
        intro fresh freshMem
        simp only [List.mem_singleton] at freshMem
        subst fresh
        simp [AnnotatedOccurrence.child, AnnotatedOccurrence.postponedTarget?]) parentHolds
  | alwaysBeforeEnd selected interval body shape present active beforeEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      left
      exact escape.lift_of_replace (by
        intro fresh freshMem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at freshMem
        rcases freshMem with rfl | rfl <;>
          simp [AnnotatedOccurrence.relabel, AnnotatedOccurrence.child,
            AnnotatedOccurrence.postponedTarget?]) parentHolds
  | alwaysAtEnd selected interval body shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      left
      exact escape.lift_of_replace (by
        intro fresh freshMem
        simp only [List.mem_singleton] at freshMem
        subst fresh
        simp [AnnotatedOccurrence.child, AnnotatedOccurrence.postponedTarget?]) parentHolds
  | strictUntilBeforeEnd selected interval invariant target shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      rcases childMem with rfl | rfl
      · left
        exact escape.lift_of_replace (by
          intro fresh freshMem
          simp only [List.mem_singleton] at freshMem
          subst fresh
          simp [AnnotatedOccurrence.child, AnnotatedOccurrence.postponedTarget?]) parentHolds
      · have sourceMem := escape.sourceMem
        change escape.source ∈ node.label.erase selected ∪
          [selected.relabel (.markedStrictUntil interval invariant target),
           selected.child 0 (.unmarked (invariant.temporalExpansion node.time))
             (some selected.reference)].toFinset at sourceMem
        rcases Finset.mem_union.mp sourceMem with old | fresh
        · left
          exact ⟨escape.lift rfl (Finset.mem_of_mem_erase old) parentHolds⟩
        · simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil,
            or_false] at fresh
          rcases fresh with markedEq | invariantEq
          · right
            have escapeShape := escape.shape
            rw [markedEq] at escapeShape
            simp only [AnnotatedOccurrence.relabel,
              AnnotatedOccurrence.postponedTarget?, Option.some.injEq,
              Prod.mk.injEq] at escapeShape
            rcases escapeShape with ⟨_, targetEq⟩
            have escapeTargetHolds : escape.target.Satisfies semantics
                escape.signal node.time := by
              simpa [Node.replace] using escape.targetHolds
            have escapedTarget : target.Satisfies semantics escape.signal node.time := by
              simpa only [targetEq] using escapeTargetHolds
            apply SiblingHasModel.ofLeft
            · refine ⟨⟨escape.signal, ?_⟩⟩
              apply Node.satisfiedBy_replace_of parentHolds
              intro occurrence occurrenceMem
              simp only [List.mem_singleton] at occurrenceMem
              subst occurrence
              simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
                Stlsat.Occurrence.SatisfiedBy] using escapedTarget
            · intro siblingEscape
              apply siblingEscape.lift_of_replace
              · intro fresh freshMem
                simp only [List.mem_singleton] at freshMem
                subst fresh
                simp [AnnotatedOccurrence.child,
                  AnnotatedOccurrence.postponedTarget?]
              · exact (Expansion.strictUntilBeforeEnd selected interval invariant
                  target shape present active beforeEnd).satisfiedBy_parent (by simp)
                    siblingEscape.nodeHolds
          · have escapeShape := escape.shape
            rw [invariantEq] at escapeShape
            simp [AnnotatedOccurrence.child,
              AnnotatedOccurrence.postponedTarget?] at escapeShape
  | strictUntilAtEnd selected interval invariant target shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      left
      exact escape.lift_of_replace (by
        intro fresh freshMem
        simp only [List.mem_singleton] at freshMem
        subst fresh
        simp [AnnotatedOccurrence.child, AnnotatedOccurrence.postponedTarget?]) parentHolds
  | strictReleaseBeforeEnd selected interval target invariant shape present active beforeEnd =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMem
      rcases childMem with rfl | rfl
      · left
        exact escape.lift_of_replace (by
          intro fresh freshMem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at freshMem
          rcases freshMem with rfl | rfl <;>
            simp [AnnotatedOccurrence.child,
              AnnotatedOccurrence.postponedTarget?]) parentHolds
      · have sourceMem := escape.sourceMem
        change escape.source ∈ node.label.erase selected ∪
          [selected.relabel (.markedStrictRelease interval target invariant),
           selected.child 1 (.unmarked (invariant.temporalExpansion node.time))
             (some selected.reference)].toFinset at sourceMem
        rcases Finset.mem_union.mp sourceMem with old | fresh
        · left
          exact ⟨escape.lift rfl (Finset.mem_of_mem_erase old) parentHolds⟩
        · simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil,
            or_false] at fresh
          rcases fresh with markedEq | invariantEq
          · right
            have escapeShape := escape.shape
            rw [markedEq] at escapeShape
            simp only [AnnotatedOccurrence.relabel,
              AnnotatedOccurrence.postponedTarget?, Option.some.injEq,
              Prod.mk.injEq] at escapeShape
            rcases escapeShape with ⟨_, targetEq⟩
            have escapeTargetHolds : escape.target.Satisfies semantics
                escape.signal node.time := by
              simpa [Node.replace] using escape.targetHolds
            have escapedTarget : target.Satisfies semantics escape.signal node.time := by
              simpa only [targetEq] using escapeTargetHolds
            have invariantHolds :=
              (Node.satisfiedBy_iff _ semantics escape.signal).1 escape.nodeHolds
                (selected.child 1
                  (.unmarked (invariant.temporalExpansion node.time))
                    (some selected.reference)) (by
                      change selected.child 1
                        (.unmarked (invariant.temporalExpansion node.time))
                          (some selected.reference) ∈
                        node.label.erase selected ∪
                          [selected.relabel
                            (.markedStrictRelease interval target invariant),
                           selected.child 1
                            (.unmarked (invariant.temporalExpansion node.time))
                              (some selected.reference)].toFinset
                      exact Finset.mem_union.mpr (Or.inr (by simp)))
            apply SiblingHasModel.ofLeft
            · refine ⟨⟨escape.signal, ?_⟩⟩
              apply Node.satisfiedBy_replace_of parentHolds
              intro occurrence occurrenceMem
              simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMem
              rcases occurrenceMem with rfl | rfl
              · simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
                  Stlsat.Occurrence.SatisfiedBy] using escapedTarget
              · simpa [AnnotatedOccurrence.child, AnnotatedOccurrence.SatisfiedBy,
                  Stlsat.Occurrence.SatisfiedBy, Node.replace] using invariantHolds
            · intro siblingEscape
              apply siblingEscape.lift_of_replace
              · intro fresh freshMem
                simp only [List.mem_cons, List.not_mem_nil, or_false] at freshMem
                rcases freshMem with rfl | rfl <;>
                  simp [AnnotatedOccurrence.child,
                    AnnotatedOccurrence.postponedTarget?]
              · exact (Expansion.strictReleaseBeforeEnd selected interval target
                  invariant shape present active beforeEnd).satisfiedBy_parent (by simp)
                    siblingEscape.nodeHolds
          · have escapeShape := escape.shape
            rw [invariantEq] at escapeShape
            simp [AnnotatedOccurrence.child,
              AnnotatedOccurrence.postponedTarget?] at escapeShape
  | strictReleaseAtEnd selected interval target invariant shape present atEnd =>
      simp only [List.mem_singleton] at childMem
      subst child
      left
      exact escape.lift_of_replace (by
        intro fresh freshMem
        simp only [List.mem_singleton] at freshMem
        subst fresh
        simp [AnnotatedOccurrence.child, AnnotatedOccurrence.postponedTarget?]) parentHolds

end Expansion

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

/-- Forward model preservation for the ordinary one-instant STEP. -/
theorem hasModel_step_of_hasModel {node : Node Atom}
    {semantics : Stlsat.AtomicSemantics Atom}
    (poised : node.Poised) (timely : node.Timely)
    (model : node.HasModel semantics) : node.step.HasModel semantics := by
  rcases model with ⟨model⟩
  change node.step.erase.HasModel semantics
  rw [Node.erase_step]
  exact ⟨Stlsat.Node.model_step (Node.poised_erase poised) timely model⟩

end Node

namespace Rule

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom}

/-- Complete progress through a unary rule, including the proof that a
phase-local escape returned by its child lifts to the parent. -/
structure UnaryProgress (semantics : Stlsat.AtomicSemantics Atom)
    (node child : Node Atom) where
  model : child.HasModel semantics
  escapeLifts : ∀ _escape : child.TargetEscape semantics,
    Nonempty (node.TargetEscape semantics)

theorem unaryProgress {node child : Node Atom}
    (rule : Rule semantics node [child])
    (derivation : node.FullDerivationValid) (timely : node.Timely)
    (normal : node.InStrictNormalForm) (model : node.HasModel semantics) :
    Nonempty (node.TargetEscape semantics) ∨
      UnaryProgress semantics node child := by
  have childMem : child ∈ [child] := by simp
  cases rule with
  | expand notRejected expansion =>
      rcases expansion.exists_child_hasModel model with
        ⟨modeled, modeledMem, childModel⟩
      simp only [List.mem_singleton] at modeledMem
      subst modeled
      right
      refine ⟨childModel, ?_⟩
      intro escape
      rcases expansion.targetEscape_parent_or_alternate childMem escape with
        parentEscape | sibling
      · exact parentEscape
      · cases sibling
  | step notRejected poised hasTemporal jumpDisabled =>
      right
      refine ⟨node.hasModel_step_of_hasModel poised timely model, ?_⟩
      intro escape
      exact False.elim (node.no_targetEscape_step semantics ⟨escape⟩)
  | jump notRejected poised hasTemporal sound complete size computed =>
      rcases model with ⟨sourceModel⟩
      rcases node.hasModel_jump_or_targetEscape computed derivation timely poised
          normal complete sourceModel with childModel | parentEscape
      · right
        refine ⟨childModel, ?_⟩
        intro escape
        exact False.elim (node.no_targetEscape_jump size semantics ⟨escape⟩)
      · exact Or.inl parentEscape

/-- The modeled side of a binary expansion, together with its exact escape
route to either the parent or the opposite sibling. -/
inductive BinaryProgress (semantics : Stlsat.AtomicSemantics Atom)
    (node left right : Node Atom) : Prop where
  | left (model : left.HasModel semantics)
      (route : ∀ escape : left.TargetEscape semantics,
        Nonempty (node.TargetEscape semantics) ∨
          Expansion.SiblingHasModel semantics node [left, right] left) :
      BinaryProgress semantics node left right
  | right (model : right.HasModel semantics)
      (route : ∀ escape : right.TargetEscape semantics,
        Nonempty (node.TargetEscape semantics) ∨
          Expansion.SiblingHasModel semantics node [left, right] right) :
      BinaryProgress semantics node left right

theorem binaryProgress {node left right : Node Atom}
    (rule : Rule semantics node [left, right])
    (model : node.HasModel semantics) :
    BinaryProgress semantics node left right := by
  cases rule with
  | expand notRejected expansion =>
      rcases expansion.exists_child_hasModel model with
        ⟨modeled, modeledMem, childModel⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at modeledMem
      rcases modeledMem with rfl | rfl
      · exact .left childModel
          (fun escape => expansion.targetEscape_parent_or_alternate (by simp) escape)
      · exact .right childModel
          (fun escape => expansion.targetEscape_parent_or_alternate (by simp) escape)

end Rule

namespace TableauTree

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom}

/-- Model-guided completeness with a phase-local escape result.  An escape is
returned only through formula-expansion edges; STEP and JUMP successors are
unmarked, so a top-level invocation cannot end with one. -/
theorem accepting_or_targetEscape (tree : TableauTree Atom)
    (wellFormed : tree.WellFormed semantics)
    (frontierTerminal : tree.FrontierTerminal semantics)
    (timely : tree.root.Timely) (normal : tree.root.InStrictNormalForm)
    (derivation : tree.root.FullDerivationValid)
    (model : tree.root.HasModel semantics) :
    tree.HasAcceptingLeaf semantics ∨
      Nonempty (tree.root.TargetEscape semantics) := by
  induction tree with
  | leaf node =>
      left
      simp only [HasAcceptingLeaf]
      simp only [FrontierTerminal] at frontierTerminal
      rcases frontierTerminal with rejected | accepting
      · exact False.elim (Stlsat.Node.notRejected_of_hasModel model rejected)
      · exact accepting
  | unary node child ih =>
      rcases wellFormed with ⟨rule, childWellFormed⟩
      have childMem : child.root ∈ [child.root] := by simp
      have childTimely := rule.child_timely timely childMem
      have childNormal := rule.child_normal normal childMem
      have childDerivation := rule.child_fullDerivationValid derivation childMem
      rcases rule.unaryProgress derivation timely normal model with
        parentEscape | progress
      · exact Or.inr parentEscape
      · rcases ih childWellFormed frontierTerminal childTimely childNormal
            childDerivation progress.model with accepting | childEscape
        · exact Or.inl accepting
        · rcases childEscape with ⟨childEscape⟩
          exact Or.inr (progress.escapeLifts childEscape)
  | binary node satisfy postpone ihSatisfy ihPostpone =>
      rcases wellFormed with
        ⟨rule, satisfyWellFormed, postponeWellFormed⟩
      rcases frontierTerminal with ⟨satisfyTerminal, postponeTerminal⟩
      have satisfyMem : satisfy.root ∈ [satisfy.root, postpone.root] := by simp
      have postponeMem : postpone.root ∈ [satisfy.root, postpone.root] := by simp
      have satisfyTimely := rule.child_timely timely satisfyMem
      have satisfyNormal := rule.child_normal normal satisfyMem
      have satisfyDerivation := rule.child_fullDerivationValid derivation satisfyMem
      have postponeTimely := rule.child_timely timely postponeMem
      have postponeNormal := rule.child_normal normal postponeMem
      have postponeDerivation := rule.child_fullDerivationValid derivation postponeMem
      cases rule.binaryProgress model with
      | left childModel route =>
          rcases ihSatisfy satisfyWellFormed satisfyTerminal satisfyTimely
              satisfyNormal satisfyDerivation childModel with accepting | childEscape
          · exact Or.inl (Or.inl accepting)
          · rcases childEscape with ⟨childEscape⟩
            rcases route childEscape with parentEscape | sibling
            · exact Or.inr parentEscape
            · rcases sibling.other_of_left with ⟨siblingModel, escapeLifts⟩
              rcases ihPostpone postponeWellFormed postponeTerminal postponeTimely
                  postponeNormal postponeDerivation siblingModel with
                siblingAccepting | siblingEscape
              · exact Or.inl (Or.inr siblingAccepting)
              · rcases siblingEscape with ⟨siblingEscape⟩
                exact Or.inr (escapeLifts siblingEscape)
      | right childModel route =>
          rcases ihPostpone postponeWellFormed postponeTerminal postponeTimely
              postponeNormal postponeDerivation childModel with accepting | childEscape
          · exact Or.inl (Or.inr accepting)
          · rcases childEscape with ⟨childEscape⟩
            rcases route childEscape with parentEscape | sibling
            · exact Or.inr parentEscape
            · rcases sibling.other_of_right with ⟨siblingModel, escapeLifts⟩
              rcases ihSatisfy satisfyWellFormed satisfyTerminal satisfyTimely
                  satisfyNormal satisfyDerivation siblingModel with
                siblingAccepting | siblingEscape
              · exact Or.inl (Or.inl siblingAccepting)
              · rcases siblingEscape with ⟨siblingEscape⟩
                exact Or.inr (escapeLifts siblingEscape)

end TableauTree

namespace Node

/-- A target escape cannot reach the initial node: its unique occurrence is
unmarked, whereas an escape always records the target of a marked postponed
temporal occurrence. -/
theorem no_targetEscape_initial {Atom : Type u} [DecidableEq Atom]
    (formula : Stlsat.Formula Atom) (semantics : Stlsat.AtomicSemantics Atom) :
    ¬Nonempty ((Node.initial formula).TargetEscape semantics) := by
  rintro ⟨escape⟩
  have sourceEq := escape.sourceMem
  simp only [Node.initial, Finset.mem_singleton] at sourceEq
  have shape := escape.shape
  rw [sourceEq] at shape
  simp [AnnotatedOccurrence.postponedTarget?] at shape

end Node

namespace Tableau

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom} {formula : Stlsat.Formula Atom}

/-- A model of the input formula selects an accepting branch in the guarded
JUMP tableau.  The proof follows the model through ordinary rules and safe
JUMPs; when a model chooses a target skipped by a JUMP, it switches to the
corresponding earlier satisfy sibling. -/
theorem hasAcceptingBranch_of_hasModel (tableau : Tableau semantics formula)
    (model : formula.HasModel semantics) : tableau.HasAcceptingBranch := by
  have rootTimely : tableau.tree.root.Timely := by
    rw [tableau.rooted_at]
    exact Node.initial_timely formula
  have rootNormal : tableau.tree.root.InStrictNormalForm := by
    rw [tableau.rooted_at]
    exact Node.initial_normal tableau.root_normal
  have rootDerivation : tableau.tree.root.FullDerivationValid := by
    rw [tableau.rooted_at]
    exact Node.initial_fullDerivationValid formula
  have rootModel : tableau.tree.root.HasModel semantics := by
    change tableau.tree.root.erase.HasModel semantics
    rw [tableau.rooted_at, Node.erase_initial]
    exact model
  rcases TableauTree.accepting_or_targetEscape tableau.tree tableau.wellFormed
      tableau.frontier_terminal rootTimely rootNormal rootDerivation rootModel with
    accepted | escape
  · exact accepted
  · rw [tableau.rooted_at] at escape
    exact False.elim (Node.no_targetEscape_initial formula semantics escape)

/-- Completeness of the guarded JUMP tableau: every satisfiable strict-normal
input formula has an accepting branch in every fully developed tableau.  The
strict-normal assumption is part of `Tableau`, matching both the construction
and the unconditional soundness theorem. -/
theorem completeness (tableau : Tableau semantics formula)
    (satisfiable : formula.Satisfiable semantics) : tableau.HasAcceptingBranch :=
  tableau.hasAcceptingBranch_of_hasModel
    ((Stlsat.Formula.satisfiable_iff_hasModel formula semantics).mp satisfiable)

end Tableau

end Stlsat.Jump
