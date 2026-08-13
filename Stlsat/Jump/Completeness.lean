import Stlsat.Jump.UnconditionalSoundness

/-!
# Failure of completeness for the current JUMP rule

The natural converse of `Stlsat.Jump.Tableau.soundness` would state that every
fully developed JUMP tableau for a satisfiable strict-normal formula has an
accepting branch.  The current construction does not satisfy that statement:
`CompletenessCounterexample.not_complete` below gives a kernel-checked finite
tableau whose satisfiable root has only rejected leaves.

The counterexample isolates the missing correspondence in the paper's proof.
The target of a postponed eventuality is checked only at the current time and
at the mandatory jump destination.  Independent eventuality targets do not
belong to `conflictWindows`, so they can reject both explored alternatives
while the only satisfiable intermediate extraction is skipped.
-/

namespace Stlsat.Jump.CompletenessCounterexample

inductive Atom where | p
deriving DecidableEq

def semantics : Stlsat.AtomicSemantics Atom where
  Valuation := Bool
  nonempty := inferInstance
  holds value _ := value = true

def interval (lower upper : Nat) (valid : lower ≤ upper := by omega) : Stlsat.Interval :=
  ⟨lower, upper, valid⟩

def p : Stlsat.Formula Atom := .atom .p
def np : Stlsat.Formula Atom := .neg p
def inner : Stlsat.Formula Atom := .eventually (interval 2 2) p
def outer : Stlsat.Formula Atom := .eventually (interval 0 2) inner
def negative2 : Stlsat.Formula Atom := .eventually (interval 2 2) np
def negative4 : Stlsat.Formula Atom := .eventually (interval 4 4) np
def formula : Stlsat.Formula Atom := .and outer (.and negative2 negative4)

theorem formula_normal : formula.InStrictNormalForm := by
  simp [formula, outer, inner, negative2, negative4, np, p,
    Stlsat.Formula.InStrictNormalForm]

def signal : Stlsat.Signal semantics := fun time => decide (time = 3)

theorem formula_satisfiable : formula.Satisfiable semantics := by
  refine ⟨signal, ?_⟩
  simp only [formula, outer, inner, negative2, negative4, np, p,
    Stlsat.Formula.Satisfies]
  constructor
  · refine ⟨1, ?_, ?_⟩
    · simp [interval, Stlsat.Interval.Contains]
    · refine ⟨2, ?_, ?_⟩
      · simp [interval, Stlsat.Interval.Contains]
      · simp [semantics, signal]
  · constructor
    · refine ⟨2, ?_, ?_⟩
      · simp [interval, Stlsat.Interval.Contains]
      · simp [semantics, signal]
    · refine ⟨4, ?_, ?_⟩
      · simp [interval, Stlsat.Interval.Contains]
      · simp [semantics, signal]

def rootOccurrence : AnnotatedOccurrence Atom :=
  ⟨[], .unmarked formula, none⟩
def outerOccurrence : AnnotatedOccurrence Atom :=
  rootOccurrence.child 0 (.unmarked outer) none
def rightOccurrence : AnnotatedOccurrence Atom :=
  rootOccurrence.child 1 (.unmarked (.and negative2 negative4)) none
def negative2Occurrence : AnnotatedOccurrence Atom :=
  rightOccurrence.child 0 (.unmarked negative2) none
def negative4Occurrence : AnnotatedOccurrence Atom :=
  rightOccurrence.child 1 (.unmarked negative4) none
def innerOccurrence0 : AnnotatedOccurrence Atom :=
  outerOccurrence.child 0 (.unmarked (inner.temporalExpansion 0)) none
def markedOuter : AnnotatedOccurrence Atom :=
  outerOccurrence.relabel (.markedEventually (interval 0 2) inner)

def n0 : Node Atom := Node.initial formula
def n1 : Node Atom := n0.replace rootOccurrence [outerOccurrence, rightOccurrence]
def satisfy1 : Node Atom := n1.replace outerOccurrence [innerOccurrence0]
def satisfyPoised : Node Atom :=
  satisfy1.replace rightOccurrence [negative2Occurrence, negative4Occurrence]
def satisfy2 : Node Atom := satisfyPoised.jump 2
def satisfyNegative : Node Atom :=
  satisfy2.replace negative2Occurrence.unmark
    [negative2Occurrence.unmark.child 0
      (.unmarked (np.temporalExpansion satisfy2.time)) none]
def satisfyReject : Node Atom :=
  satisfyNegative.replace innerOccurrence0.unmark
    [innerOccurrence0.unmark.child 0
      (.unmarked (p.temporalExpansion satisfyNegative.time)) none]

def postpone1 : Node Atom := n1.replace outerOccurrence [markedOuter]
def postponePoised : Node Atom :=
  postpone1.replace rightOccurrence [negative2Occurrence, negative4Occurrence]
def postpone2 : Node Atom := postponePoised.jump 2
def postponeOuter : Node Atom :=
  postpone2.replace markedOuter.unmark
    [markedOuter.unmark.child 0
      (.unmarked (inner.temporalExpansion postpone2.time)) none]
def postponeNegative : Node Atom :=
  postponeOuter.replace negative2Occurrence.unmark
    [negative2Occurrence.unmark.child 0
      (.unmarked (np.temporalExpansion postponeOuter.time)) none]
def postpone4 : Node Atom := postponeNegative.jump 2
def postponePositive : Node Atom :=
  postpone4.replace
    (markedOuter.unmark.child 0 (.unmarked (inner.temporalExpansion postpone2.time)) none).unmark
    [(markedOuter.unmark.child 0 (.unmarked (inner.temporalExpansion postpone2.time)) none).unmark.child 0
      (.unmarked (p.temporalExpansion postpone4.time)) none]
def postponeReject : Node Atom :=
  postponePositive.replace negative4Occurrence.unmark
    [negative4Occurrence.unmark.child 0
      (.unmarked (np.temporalExpansion postponePositive.time)) none]

theorem expansion_n0 : Expansion n0 [n1] := by
  apply Expansion.conjunction rootOccurrence outer (.and negative2 negative4)
  · rfl
  · decide

theorem expansion_n1 : Expansion n1 [satisfy1, postpone1] := by
  apply Expansion.eventuallyBeforeEnd outerOccurrence (interval 0 2) inner
  · rfl
  · decide
  · decide
  · change 0 < 2
    omega

theorem expansion_satisfy1 : Expansion satisfy1 [satisfyPoised] := by
  apply Expansion.conjunction rightOccurrence negative2 negative4
  · rfl
  · decide

theorem expansion_postpone1 : Expansion postpone1 [postponePoised] := by
  apply Expansion.conjunction rightOccurrence negative2 negative4
  · rfl
  · decide

theorem expansion_satisfy2 : Expansion satisfy2 [satisfyNegative] := by
  apply Expansion.eventuallyAtEnd negative2Occurrence.unmark (interval 2 2) np
  · rfl
  · decide
  · decide

theorem expansion_satisfyNegative : Expansion satisfyNegative [satisfyReject] := by
  apply Expansion.eventuallyAtEnd innerOccurrence0.unmark (interval 2 2) p
  · decide
  · decide
  · decide

theorem expansion_postpone2 : Expansion postpone2 [postponeOuter] := by
  apply Expansion.eventuallyAtEnd markedOuter.unmark (interval 0 2) inner
  · decide
  · decide
  · decide

theorem expansion_postponeOuter : Expansion postponeOuter [postponeNegative] := by
  apply Expansion.eventuallyAtEnd negative2Occurrence.unmark (interval 2 2) np
  · rfl
  · decide
  · decide

theorem expansion_postpone4 : Expansion postpone4 [postponePositive] := by
  let selected :=
    (markedOuter.unmark.child 0
      (.unmarked (inner.temporalExpansion postpone2.time)) none).unmark
  apply Expansion.eventuallyAtEnd selected (interval 4 4) p
  · decide
  · decide
  · decide

theorem expansion_postponePositive : Expansion postponePositive [postponeReject] := by
  apply Expansion.eventuallyAtEnd negative4Occurrence.unmark (interval 4 4) np
  · rfl
  · decide
  · decide

theorem satisfyReject_rejected : satisfyReject.Rejected semantics := by
  right
  intro consistent
  rcases consistent with ⟨value, holds⟩
  let positiveOccurrence := innerOccurrence0.unmark.child 0
    (.unmarked (p.temporalExpansion satisfyNegative.time)) none
  let negativeOccurrence := negative2Occurrence.unmark.child 0
    (.unmarked (np.temporalExpansion satisfy2.time)) none
  have positive := holds positiveOccurrence.payload (by decide)
  have negative := holds negativeOccurrence.payload (by decide)
  change value = true at positive
  change ¬value = true at negative
  exact negative positive

theorem postponeReject_rejected : postponeReject.Rejected semantics := by
  right
  intro consistent
  rcases consistent with ⟨value, holds⟩
  let positiveOccurrence :=
    (markedOuter.unmark.child 0
      (.unmarked (inner.temporalExpansion postpone2.time)) none).unmark.child 0
        (.unmarked (p.temporalExpansion postpone4.time)) none
  let negativeOccurrence := negative4Occurrence.unmark.child 0
    (.unmarked (np.temporalExpansion postponePositive.time)) none
  have positive := holds positiveOccurrence.payload (by decide)
  have negative := holds negativeOccurrence.payload (by decide)
  change value = true at positive
  change ¬value = true at negative
  exact negative positive

theorem satisfyPoised_label : satisfyPoised.label =
    {innerOccurrence0, negative2Occurrence, negative4Occurrence} := by
  decide

theorem postponePoised_label : postponePoised.label =
    {markedOuter, negative2Occurrence, negative4Occurrence} := by
  decide

theorem postponeNegative_label : postponeNegative.label =
    {(markedOuter.unmark.child 0
        (.unmarked (inner.temporalExpansion postpone2.time)) none),
      (negative2Occurrence.unmark.child 0
        (.unmarked (np.temporalExpansion postponeOuter.time)) none),
      negative4Occurrence.unmark} := by
  decide

def Inactive (node : Node Atom) : Prop :=
  ∀ occurrence ∈ node.label,
    match occurrence.payload with
    | .unmarked (.or _ _) | .unmarked (.and _ _) => False
    | .unmarked (.eventually bounds _) | .unmarked (.always bounds _)
    | .unmarked (.strictUntil bounds _ _) | .unmarked (.strictRelease bounds _ _) =>
        node.time < bounds.lower
    | _ => True

theorem poised_of_inactive {node : Node Atom} (inactive : Inactive node) : node.Poised := by
  rintro ⟨children, expansion⟩
  cases expansion with
  | disjunction selected left right shape present =>
      simpa [Inactive, shape] using inactive selected present
  | conjunction selected left right shape present =>
      simpa [Inactive, shape] using inactive selected present
  | eventuallyBeforeEnd selected bounds body shape present active beforeEnd =>
      have blocked := inactive selected present
      simp [shape] at blocked
      omega
  | eventuallyAtEnd selected bounds body shape present atEnd =>
      have blocked := inactive selected present
      simp [shape] at blocked
      exact (Nat.not_lt_of_ge bounds.lower_le_upper) (by omega)
  | alwaysBeforeEnd selected bounds body shape present active beforeEnd =>
      have blocked := inactive selected present
      simp [shape] at blocked
      omega
  | alwaysAtEnd selected bounds body shape present atEnd =>
      have blocked := inactive selected present
      simp [shape] at blocked
      exact (Nat.not_lt_of_ge bounds.lower_le_upper) (by omega)
  | strictUntilBeforeEnd selected bounds invariant target shape present active beforeEnd =>
      have blocked := inactive selected present
      simp [shape] at blocked
      omega
  | strictUntilAtEnd selected bounds invariant target shape present atEnd =>
      have blocked := inactive selected present
      simp [shape] at blocked
      exact (Nat.not_lt_of_ge bounds.lower_le_upper) (by omega)
  | strictReleaseBeforeEnd selected bounds target invariant shape present active beforeEnd =>
      have blocked := inactive selected present
      simp [shape] at blocked
      omega
  | strictReleaseAtEnd selected bounds target invariant shape present atEnd =>
      have blocked := inactive selected present
      simp [shape] at blocked
      exact (Nat.not_lt_of_ge bounds.lower_le_upper) (by omega)

theorem satisfyPoised_poised : satisfyPoised.Poised := by
  apply poised_of_inactive
  intro occurrence present
  rw [satisfyPoised_label] at present
  simp only [Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl | rfl <;>
    simp [innerOccurrence0, inner, negative2Occurrence, negative4Occurrence,
      negative2, negative4, rightOccurrence, outerOccurrence, rootOccurrence,
      satisfyPoised, satisfy1, n1, n0, interval, AnnotatedOccurrence.child,
      Node.replace, Node.initial]

theorem postponePoised_poised : postponePoised.Poised := by
  apply poised_of_inactive
  intro occurrence present
  rw [postponePoised_label] at present
  simp only [Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl | rfl <;>
    simp [markedOuter, outerOccurrence, negative2Occurrence, negative4Occurrence,
      negative2, negative4, rightOccurrence, rootOccurrence, postponePoised,
      postpone1, n1, n0, interval, AnnotatedOccurrence.child,
      AnnotatedOccurrence.relabel, Node.replace, Node.initial]

theorem postponeNegative_poised : postponeNegative.Poised := by
  apply poised_of_inactive
  intro occurrence present
  rw [postponeNegative_label] at present
  simp only [Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl | rfl <;>
    simp [postponeNegative, postponeOuter, postpone2, postponePoised, postpone1, n1, n0,
      markedOuter, outerOccurrence, inner, negative2Occurrence, negative4Occurrence,
      negative2, negative4, rightOccurrence, rootOccurrence, p, np, interval,
      AnnotatedOccurrence.child, AnnotatedOccurrence.unmark,
      AnnotatedOccurrence.relabel, Stlsat.Occurrence.unmark,
      Stlsat.Formula.temporalExpansion, Stlsat.Interval.shift,
      Node.replace, Node.initial, Node.jump]

theorem satisfyPoised_erase_label : satisfyPoised.erase.label =
    {innerOccurrence0.payload, negative2Occurrence.payload,
      negative4Occurrence.payload} := by
  decide

theorem postponePoised_erase_label : postponePoised.erase.label =
    {markedOuter.payload, negative2Occurrence.payload,
      negative4Occurrence.payload} := by
  decide

theorem postponeNegative_erase_label : postponeNegative.erase.label =
    {(markedOuter.unmark.child 0
        (.unmarked (inner.temporalExpansion postpone2.time)) none).payload,
      (negative2Occurrence.unmark.child 0
        (.unmarked (np.temporalExpansion postponeOuter.time)) none).payload,
      negative4Occurrence.unmark.payload} := by
  decide

theorem satisfyPoised_notRejected : ¬satisfyPoised.Rejected semantics := by
  rintro (falsePresent | inconsistent)
  · rw [satisfyPoised_erase_label] at falsePresent
    have absent : Stlsat.Occurrence.unmarked (.neg .truth) ∉
        ({innerOccurrence0.payload, negative2Occurrence.payload,
          negative4Occurrence.payload} : Finset (Stlsat.Occurrence Atom)) := by decide
    exact absent falsePresent
  · apply inconsistent
    refine ⟨false, ?_⟩
    intro occurrence present
    rw [satisfyPoised_erase_label] at present
    simp only [Finset.mem_insert, Finset.mem_singleton] at present
    rcases present with rfl | rfl | rfl <;>
      simp [innerOccurrence0, inner, negative2Occurrence, negative4Occurrence,
        negative2, negative4, np, p, rightOccurrence, rootOccurrence,
        Stlsat.Occurrence.LiteralSatisfied, AnnotatedOccurrence.child]

theorem postponePoised_notRejected : ¬postponePoised.Rejected semantics := by
  rintro (falsePresent | inconsistent)
  · rw [postponePoised_erase_label] at falsePresent
    have absent : Stlsat.Occurrence.unmarked (.neg .truth) ∉
        ({markedOuter.payload, negative2Occurrence.payload,
          negative4Occurrence.payload} : Finset (Stlsat.Occurrence Atom)) := by decide
    exact absent falsePresent
  · apply inconsistent
    refine ⟨false, ?_⟩
    intro occurrence present
    rw [postponePoised_erase_label] at present
    simp only [Finset.mem_insert, Finset.mem_singleton] at present
    rcases present with rfl | rfl | rfl <;>
      simp [markedOuter, outerOccurrence, inner, negative2Occurrence,
        negative4Occurrence, negative2, negative4, np, p, rightOccurrence,
        rootOccurrence, Stlsat.Occurrence.LiteralSatisfied,
        AnnotatedOccurrence.child, AnnotatedOccurrence.relabel]

theorem postponeNegative_notRejected : ¬postponeNegative.Rejected semantics := by
  rintro (falsePresent | inconsistent)
  · rw [postponeNegative_erase_label] at falsePresent
    have absent : Stlsat.Occurrence.unmarked (.neg .truth) ∉
        ({(markedOuter.unmark.child 0
            (.unmarked (inner.temporalExpansion postpone2.time)) none).payload,
          (negative2Occurrence.unmark.child 0
            (.unmarked (np.temporalExpansion postponeOuter.time)) none).payload,
          negative4Occurrence.unmark.payload} : Finset (Stlsat.Occurrence Atom)) := by
      decide
    exact absent falsePresent
  · apply inconsistent
    refine ⟨false, ?_⟩
    intro occurrence present
    rw [postponeNegative_erase_label] at present
    simp only [Finset.mem_insert, Finset.mem_singleton] at present
    rcases present with rfl | rfl | rfl <;>
      simp [markedOuter, outerOccurrence, inner, negative2Occurrence,
        negative4Occurrence, negative2, negative4, np, p, rightOccurrence,
        rootOccurrence, semantics, Stlsat.Occurrence.LiteralSatisfied,
        AnnotatedOccurrence.child, AnnotatedOccurrence.relabel,
        AnnotatedOccurrence.unmark, Stlsat.Occurrence.unmark,
        Stlsat.Formula.temporalExpansion]

theorem satisfyPoised_containsTemporal : satisfyPoised.ContainsTemporal := by
  refine ⟨innerOccurrence0, ?_, ?_⟩
  · rw [satisfyPoised_label]
    simp
  · decide

theorem postponePoised_containsTemporal : postponePoised.ContainsTemporal := by
  refine ⟨markedOuter, ?_, ?_⟩
  · rw [postponePoised_label]
    simp
  · decide

theorem postponeNegative_containsTemporal : postponeNegative.ContainsTemporal := by
  refine ⟨negative4Occurrence.unmark, ?_, ?_⟩
  · rw [postponeNegative_label]
    simp
  · decide

theorem satisfyPoised_invariantWindows : satisfyPoised.invariantWindows = [] := by
  unfold Node.invariantWindows
  rw [List.flatMap_eq_nil_iff]
  intro occurrence present
  have present' := Finset.mem_toList.mp present
  rw [satisfyPoised_label] at present'
  simp only [Finset.mem_insert, Finset.mem_singleton] at present'
  rcases present' with rfl | rfl | rfl <;> decide

theorem postponePoised_invariantWindows : postponePoised.invariantWindows = [] := by
  unfold Node.invariantWindows
  rw [List.flatMap_eq_nil_iff]
  intro occurrence present
  have present' := Finset.mem_toList.mp present
  rw [postponePoised_label] at present'
  simp only [Finset.mem_insert, Finset.mem_singleton] at present'
  rcases present' with rfl | rfl | rfl <;> decide

theorem postponeNegative_invariantWindows : postponeNegative.invariantWindows = [] := by
  unfold Node.invariantWindows
  rw [List.flatMap_eq_nil_iff]
  intro occurrence present
  have present' := Finset.mem_toList.mp present
  rw [postponeNegative_label] at present'
  simp only [Finset.mem_insert, Finset.mem_singleton] at present'
  rcases present' with rfl | rfl | rfl <;> decide

theorem satisfyPoised_targetWindows : satisfyPoised.targetWindows = [] := by
  unfold Node.targetWindows
  rw [List.flatMap_eq_nil_iff]
  intro occurrence present
  have present' := Finset.mem_toList.mp present
  rw [satisfyPoised_label] at present'
  simp only [Finset.mem_insert, Finset.mem_singleton] at present'
  rcases present' with rfl | rfl | rfl <;> decide

theorem postponePoised_conflictWindows : postponePoised.conflictWindows = [] := by
  unfold Node.conflictWindows
  rw [List.flatMap_eq_nil_iff]
  intro occurrence present
  have present' := Finset.mem_toList.mp present
  rw [postponePoised_label] at present'
  simp only [Finset.mem_insert, Finset.mem_singleton] at present'
  rcases present' with rfl | rfl | rfl <;>
    simp [Node.ParentActive, markedOuter, outerOccurrence, negative2Occurrence,
      negative4Occurrence, negative2, negative4, np, p, rightOccurrence, rootOccurrence,
      AnnotatedOccurrence.child, AnnotatedOccurrence.relabel]

theorem postponeNegative_targetWindows : postponeNegative.targetWindows = [] := by
  unfold Node.targetWindows
  rw [List.flatMap_eq_nil_iff]
  intro occurrence present
  have present' := Finset.mem_toList.mp present
  rw [postponeNegative_label] at present'
  simp only [Finset.mem_insert, Finset.mem_singleton] at present'
  rcases present' with rfl | rfl | rfl <;> decide

theorem satisfyPoised_soundSafe : satisfyPoised.SoundSafe := by
  intro invariant invariantMem
  rw [satisfyPoised_invariantWindows] at invariantMem
  simp at invariantMem

theorem postponePoised_soundSafe : postponePoised.SoundSafe := by
  intro invariant invariantMem
  rw [postponePoised_invariantWindows] at invariantMem
  simp at invariantMem

theorem postponeNegative_soundSafe : postponeNegative.SoundSafe := by
  intro invariant invariantMem
  rw [postponeNegative_invariantWindows] at invariantMem
  simp at invariantMem

theorem satisfyPoised_completeSafe : satisfyPoised.CompleteSafe := by
  intro target targetMem
  rw [satisfyPoised_targetWindows] at targetMem
  simp at targetMem

theorem postponePoised_completeSafe : postponePoised.CompleteSafe := by
  intro target targetMem conflict conflictMem
  rw [postponePoised_conflictWindows] at conflictMem
  simp at conflictMem

theorem postponeNegative_completeSafe : postponeNegative.CompleteSafe := by
  intro target targetMem
  rw [postponeNegative_targetWindows] at targetMem
  simp at targetMem

theorem satisfyPoised_soundLimit : satisfyPoised.soundLimit? = none := by
  unfold Node.soundLimit?
  rw [satisfyPoised_invariantWindows]
  rfl

theorem postponePoised_soundLimit : postponePoised.soundLimit? = none := by
  unfold Node.soundLimit?
  rw [postponePoised_invariantWindows]
  rfl

theorem postponeNegative_soundLimit : postponeNegative.soundLimit? = none := by
  unfold Node.soundLimit?
  rw [postponeNegative_invariantWindows]
  rfl

theorem satisfyPoised_completeLimit : satisfyPoised.completeLimit? = none := by
  unfold Node.completeLimit?
  rw [satisfyPoised_targetWindows]
  rfl

theorem postponePoised_completeLimit : postponePoised.completeLimit? = none := by
  exact postponePoised.completeLimit_eq_none_of_conflictWindows_eq_nil
    postponePoised_conflictWindows

theorem postponeNegative_completeLimit : postponeNegative.completeLimit? = none := by
  unfold Node.completeLimit?
  rw [postponeNegative_targetWindows]
  rfl

theorem satisfyPoised_boundCandidate (bound : Nat)
    (present : bound ∈ satisfyPoised.boundCandidates) : bound = 2 ∨ bound = 4 := by
  unfold Node.boundCandidates at present
  rcases List.mem_flatMap.mp present with ⟨occurrence, occurrenceMem, boundMem⟩
  have occurrenceMem' := Finset.mem_toList.mp occurrenceMem
  rw [satisfyPoised_label] at occurrenceMem'
  simp only [Finset.mem_insert, Finset.mem_singleton] at occurrenceMem'
  rcases occurrenceMem' with rfl | rfl | rfl <;>
    simp [innerOccurrence0, inner, negative2Occurrence, negative4Occurrence,
      negative2, negative4, rightOccurrence, outerOccurrence, rootOccurrence,
      interval, AnnotatedOccurrence.child] at boundMem <;> omega

theorem postponePoised_boundCandidate (bound : Nat)
    (present : bound ∈ postponePoised.boundCandidates) :
    bound = 0 ∨ bound = 2 ∨ bound = 4 := by
  unfold Node.boundCandidates at present
  rcases List.mem_flatMap.mp present with ⟨occurrence, occurrenceMem, boundMem⟩
  have occurrenceMem' := Finset.mem_toList.mp occurrenceMem
  rw [postponePoised_label] at occurrenceMem'
  simp only [Finset.mem_insert, Finset.mem_singleton] at occurrenceMem'
  rcases occurrenceMem' with rfl | rfl | rfl <;>
    simp [markedOuter, outerOccurrence, negative2Occurrence, negative4Occurrence,
      negative2, negative4, rightOccurrence, rootOccurrence,
      interval, AnnotatedOccurrence.child, AnnotatedOccurrence.relabel] at boundMem <;> omega

theorem postponeNegative_boundCandidate (bound : Nat)
    (present : bound ∈ postponeNegative.boundCandidates) : bound = 4 := by
  unfold Node.boundCandidates at present
  rcases List.mem_flatMap.mp present with ⟨occurrence, occurrenceMem, boundMem⟩
  have occurrenceMem' := Finset.mem_toList.mp occurrenceMem
  rw [postponeNegative_label] at occurrenceMem'
  simp only [Finset.mem_insert, Finset.mem_singleton] at occurrenceMem'
  rcases occurrenceMem' with rfl | rfl | rfl <;>
    simp [postpone2, postponePoised, postpone1, n1, n0, markedOuter,
      outerOccurrence, inner, negative2Occurrence, negative4Occurrence,
      negative2, negative4, rightOccurrence, rootOccurrence, p, np, interval,
      AnnotatedOccurrence.child, AnnotatedOccurrence.unmark,
      AnnotatedOccurrence.relabel, Stlsat.Occurrence.unmark,
      Stlsat.Formula.temporalExpansion, Stlsat.Interval.shift,
      Node.replace, Node.initial, Node.jump] at boundMem <;> omega

theorem satisfyPoised_jumpSize : satisfyPoised.jumpSize? = some 2 := by
  apply satisfyPoised.jumpSize_eq_of_least_future_bound
  · omega
  · have present := satisfyPoised.interval_bounds_mem_boundCandidates
        innerOccurrence0 (interval 2 2) (by rw [satisfyPoised_label]; simp) (by decide)
    exact present.1
  · intro bound boundMem future
    have time : satisfyPoised.time = 0 := by decide
    rw [time]
    rcases satisfyPoised_boundCandidate bound boundMem with rfl | rfl <;> omega
  · exact satisfyPoised_soundLimit
  · exact satisfyPoised_completeLimit

theorem postponePoised_jumpSize : postponePoised.jumpSize? = some 2 := by
  apply postponePoised.jumpSize_eq_of_least_future_bound
  · omega
  · have present := postponePoised.interval_bounds_mem_boundCandidates
        markedOuter (interval 0 2) (by rw [postponePoised_label]; simp) (by decide)
    exact present.2
  · intro bound boundMem future
    have time : postponePoised.time = 0 := by decide
    rw [time]
    rcases postponePoised_boundCandidate bound boundMem with rfl | rfl | rfl <;> omega
  · exact postponePoised_soundLimit
  · exact postponePoised_completeLimit

theorem postponeNegative_jumpSize : postponeNegative.jumpSize? = some 2 := by
  apply postponeNegative.jumpSize_eq_of_least_future_bound
  · omega
  · have present := postponeNegative.interval_bounds_mem_boundCandidates
        negative4Occurrence.unmark (interval 4 4)
        (by rw [postponeNegative_label]; simp) (by decide)
    have time : postponeNegative.time = 2 := by decide
    simpa [time, interval] using present.1
  · intro bound boundMem future
    rw [postponeNegative_boundCandidate bound boundMem]
    decide
  · exact postponeNegative_soundLimit
  · exact postponeNegative_completeLimit

theorem n0_notRejected : ¬n0.Rejected semantics := by
  simp [Node.Rejected, Node.erase, n0, Node.initial, Stlsat.Node.Rejected,
    Stlsat.Node.LocallyConsistent, Stlsat.Occurrence.LiteralSatisfied, formula]
  exact semantics.nonempty

theorem n1_notRejected : ¬n1.Rejected semantics := by
  simp [Node.Rejected, Node.erase, n1, n0, Node.initial, Node.replace,
    rootOccurrence, outerOccurrence, rightOccurrence, formula, outer, inner,
    Stlsat.Node.Rejected, Stlsat.Node.LocallyConsistent,
    Stlsat.Occurrence.LiteralSatisfied, AnnotatedOccurrence.child]
  exact semantics.nonempty

theorem satisfy1_notRejected : ¬satisfy1.Rejected semantics := by
  simp [Node.Rejected, Node.erase, satisfy1, n1, n0, Node.initial, Node.replace,
    rootOccurrence, outerOccurrence, rightOccurrence, innerOccurrence0,
    formula, outer, inner, negative2, negative4, np, p,
    Stlsat.Node.Rejected, Stlsat.Node.LocallyConsistent,
    Stlsat.Occurrence.LiteralSatisfied, AnnotatedOccurrence.child]
  exact semantics.nonempty

theorem postpone1_notRejected : ¬postpone1.Rejected semantics := by
  simp [Node.Rejected, Node.erase, postpone1, n1, n0, Node.initial, Node.replace,
    rootOccurrence, outerOccurrence, rightOccurrence, markedOuter,
    formula, outer, inner, negative2, negative4, np, p,
    Stlsat.Node.Rejected, Stlsat.Node.LocallyConsistent,
    Stlsat.Occurrence.LiteralSatisfied, AnnotatedOccurrence.child,
    AnnotatedOccurrence.relabel]
  exact semantics.nonempty

theorem notRejected_of_erase_label {node : Node Atom}
    (label : Finset (Stlsat.Occurrence Atom))
    (labelEq : node.erase.label = label) (value : semantics.Valuation)
    (falseAbsent : Stlsat.Occurrence.unmarked (.neg .truth) ∉ label)
    (consistent : ∀ occurrence ∈ label,
      occurrence.LiteralSatisfied semantics value) :
    ¬node.Rejected semantics := by
  rintro (falsePresent | inconsistent)
  · apply falseAbsent
    rw [← labelEq]
    exact falsePresent
  · apply inconsistent
    exact ⟨value, fun occurrence present => consistent occurrence (by simpa [labelEq] using present)⟩

theorem satisfy2_notRejected : ¬satisfy2.Rejected semantics := by
  have labels : satisfy2.erase.label = satisfyPoised.erase.label := by decide
  simpa only [Node.Rejected, Stlsat.Node.Rejected, Stlsat.Node.LocallyConsistent,
    labels] using satisfyPoised_notRejected

theorem satisfyNegative_notRejected : ¬satisfyNegative.Rejected semantics := by
  let positive := innerOccurrence0.unmark.payload
  let negative := (negative2Occurrence.unmark.child 0
    (.unmarked (np.temporalExpansion satisfy2.time)) none).payload
  let future := negative4Occurrence.unmark.payload
  apply notRejected_of_erase_label {positive, negative, future} (value := false)
  · decide
  · decide
  · intro occurrence present
    simp only [Finset.mem_insert, Finset.mem_singleton] at present
    rcases present with rfl | rfl | rfl <;>
      simp [positive, negative, future, Stlsat.Occurrence.LiteralSatisfied,
        innerOccurrence0, inner, negative2Occurrence, negative4Occurrence,
        negative2, negative4, np, p, semantics, rightOccurrence,
        outerOccurrence, rootOccurrence, AnnotatedOccurrence.child,
        AnnotatedOccurrence.unmark, AnnotatedOccurrence.relabel,
        Stlsat.Occurrence.unmark, Stlsat.Formula.temporalExpansion]

theorem postpone2_notRejected : ¬postpone2.Rejected semantics := by
  let liveOuter := markedOuter.unmark.payload
  let liveNegative2 := negative2Occurrence.unmark.payload
  let liveNegative4 := negative4Occurrence.unmark.payload
  apply notRejected_of_erase_label
    {liveOuter, liveNegative2, liveNegative4} (value := false)
  · decide
  · decide
  · intro occurrence present
    simp only [Finset.mem_insert, Finset.mem_singleton] at present
    rcases present with rfl | rfl | rfl <;>
      simp [liveOuter, liveNegative2, liveNegative4,
        Stlsat.Occurrence.LiteralSatisfied, markedOuter, outerOccurrence,
        negative2Occurrence, negative4Occurrence, negative2, negative4, np, p,
        rightOccurrence,
        rootOccurrence, AnnotatedOccurrence.child, AnnotatedOccurrence.unmark,
        AnnotatedOccurrence.relabel, Stlsat.Occurrence.unmark]

theorem postponeOuter_notRejected : ¬postponeOuter.Rejected semantics := by
  let shiftedInner := (markedOuter.unmark.child 0
    (.unmarked (inner.temporalExpansion postpone2.time)) none).payload
  let liveNegative2 := negative2Occurrence.unmark.payload
  let liveNegative4 := negative4Occurrence.unmark.payload
  apply notRejected_of_erase_label
    {shiftedInner, liveNegative2, liveNegative4} (value := false)
  · decide
  · decide
  · intro occurrence present
    simp only [Finset.mem_insert, Finset.mem_singleton] at present
    rcases present with rfl | rfl | rfl <;>
      simp [shiftedInner, liveNegative2, liveNegative4,
        Stlsat.Occurrence.LiteralSatisfied, markedOuter, outerOccurrence,
        inner, negative2Occurrence, negative4Occurrence, negative2, negative4,
        np, p, rightOccurrence,
        rootOccurrence, AnnotatedOccurrence.child, AnnotatedOccurrence.unmark,
        AnnotatedOccurrence.relabel, Stlsat.Occurrence.unmark,
        Stlsat.Formula.temporalExpansion]

theorem postpone4_notRejected : ¬postpone4.Rejected semantics := by
  let shiftedInner := (markedOuter.unmark.child 0
    (.unmarked (inner.temporalExpansion postpone2.time)) none).unmark.payload
  let liveNegative4 := negative4Occurrence.unmark.payload
  apply notRejected_of_erase_label {shiftedInner, liveNegative4} (value := false)
  · decide
  · decide
  · intro occurrence present
    simp only [Finset.mem_insert, Finset.mem_singleton] at present
    rcases present with rfl | rfl <;>
      simp [shiftedInner, liveNegative4, Stlsat.Occurrence.LiteralSatisfied,
        markedOuter, outerOccurrence, inner, negative4Occurrence,
        negative4, np, p, rightOccurrence, rootOccurrence, AnnotatedOccurrence.child,
        AnnotatedOccurrence.unmark, AnnotatedOccurrence.relabel,
        Stlsat.Occurrence.unmark, Stlsat.Formula.temporalExpansion]

theorem postponePositive_notRejected : ¬postponePositive.Rejected semantics := by
  let positive :=
    (markedOuter.unmark.child 0
      (.unmarked (inner.temporalExpansion postpone2.time)) none).unmark.child 0
        (.unmarked (p.temporalExpansion postpone4.time)) none |>.payload
  let liveNegative4 := negative4Occurrence.unmark.payload
  apply notRejected_of_erase_label {positive, liveNegative4} (value := true)
  · decide
  · decide
  · intro occurrence present
    simp only [Finset.mem_insert, Finset.mem_singleton] at present
    rcases present with rfl | rfl <;>
      simp [positive, liveNegative4, Stlsat.Occurrence.LiteralSatisfied,
        markedOuter, outerOccurrence, inner, p, semantics,
        negative4Occurrence, negative4, np, rightOccurrence, rootOccurrence,
        AnnotatedOccurrence.child, AnnotatedOccurrence.unmark,
        AnnotatedOccurrence.relabel, Stlsat.Occurrence.unmark,
        Stlsat.Formula.temporalExpansion]

theorem rule_n0 : Rule semantics n0 [n1] :=
  Rule.expand n0_notRejected expansion_n0

theorem rule_n1 : Rule semantics n1 [satisfy1, postpone1] :=
  Rule.expand n1_notRejected expansion_n1

theorem rule_satisfy1 : Rule semantics satisfy1 [satisfyPoised] :=
  Rule.expand satisfy1_notRejected expansion_satisfy1

theorem rule_satisfyPoised : Rule semantics satisfyPoised [satisfy2] :=
  Rule.jump satisfyPoised_notRejected satisfyPoised_poised
    satisfyPoised_containsTemporal satisfyPoised_soundSafe
    satisfyPoised_completeSafe 2 satisfyPoised_jumpSize

theorem rule_satisfy2 : Rule semantics satisfy2 [satisfyNegative] :=
  Rule.expand satisfy2_notRejected expansion_satisfy2

theorem rule_satisfyNegative : Rule semantics satisfyNegative [satisfyReject] :=
  Rule.expand satisfyNegative_notRejected expansion_satisfyNegative

theorem rule_postpone1 : Rule semantics postpone1 [postponePoised] :=
  Rule.expand postpone1_notRejected expansion_postpone1

theorem rule_postponePoised : Rule semantics postponePoised [postpone2] :=
  Rule.jump postponePoised_notRejected postponePoised_poised
    postponePoised_containsTemporal postponePoised_soundSafe
    postponePoised_completeSafe 2 postponePoised_jumpSize

theorem rule_postpone2 : Rule semantics postpone2 [postponeOuter] :=
  Rule.expand postpone2_notRejected expansion_postpone2

theorem rule_postponeOuter : Rule semantics postponeOuter [postponeNegative] :=
  Rule.expand postponeOuter_notRejected expansion_postponeOuter

theorem rule_postponeNegative : Rule semantics postponeNegative [postpone4] :=
  Rule.jump postponeNegative_notRejected postponeNegative_poised
    postponeNegative_containsTemporal postponeNegative_soundSafe
    postponeNegative_completeSafe 2 postponeNegative_jumpSize

theorem rule_postpone4 : Rule semantics postpone4 [postponePositive] :=
  Rule.expand postpone4_notRejected expansion_postpone4

theorem rule_postponePositive : Rule semantics postponePositive [postponeReject] :=
  Rule.expand postponePositive_notRejected expansion_postponePositive

def satisfyTree : TableauTree Atom :=
  .unary satisfy1
    (.unary satisfyPoised
      (.unary satisfy2
        (.unary satisfyNegative (.leaf satisfyReject))))

def postponeTree : TableauTree Atom :=
  .unary postpone1
    (.unary postponePoised
      (.unary postpone2
        (.unary postponeOuter
          (.unary postponeNegative
            (.unary postpone4
              (.unary postponePositive (.leaf postponeReject)))))))

def tree : TableauTree Atom :=
  .unary n0 (.binary n1 satisfyTree postponeTree)

theorem tree_wellFormed : tree.WellFormed semantics := by
  simp only [tree, satisfyTree, postponeTree, TableauTree.WellFormed]
  refine ⟨rule_n0, rule_n1, ?_, ?_⟩
  · exact ⟨rule_satisfy1, rule_satisfyPoised, rule_satisfy2,
      rule_satisfyNegative, trivial⟩
  · exact ⟨rule_postpone1, rule_postponePoised, rule_postpone2,
      rule_postponeOuter, rule_postponeNegative, rule_postpone4,
      rule_postponePositive, trivial⟩

theorem tree_frontierTerminal : tree.FrontierTerminal semantics := by
  simp only [tree, satisfyTree, postponeTree, TableauTree.FrontierTerminal,
    Node.Terminal]
  exact ⟨Or.inl satisfyReject_rejected, Or.inl postponeReject_rejected⟩

theorem tree_allLeavesRejected : tree.AllLeavesRejected semantics := by
  simp only [tree, satisfyTree, postponeTree, TableauTree.AllLeavesRejected]
  exact ⟨satisfyReject_rejected, postponeReject_rejected⟩

theorem tree_hasNoAcceptingLeaf : ¬tree.HasAcceptingLeaf semantics := by
  simp only [tree, satisfyTree, postponeTree, TableauTree.HasAcceptingLeaf]
  intro accepted
  rcases accepted with satisfyAccepted | postponeAccepted
  · exact satisfyAccepted.2.1 satisfyReject_rejected
  · exact postponeAccepted.2.1 postponeReject_rejected

def tableau : Tableau semantics formula where
  tree := tree
  root_normal := formula_normal
  rooted_at := rfl
  wellFormed := tree_wellFormed
  frontier_terminal := tree_frontierTerminal

/-- A satisfiable strict-normal input can have a fully rejected JUMP tableau. -/
theorem satisfiable_and_allBranchesRejected :
    formula.Satisfiable semantics ∧ tableau.AllBranchesRejected := by
  exact ⟨formula_satisfiable, tree_allLeavesRejected⟩

/-- The natural satisfiability-to-acceptance completeness statement is false. -/
theorem not_complete :
    ¬∀ candidate : Tableau semantics formula,
      formula.Satisfiable semantics → candidate.HasAcceptingBranch := by
  intro claimed
  exact tree_hasNoAcceptingLeaf (claimed tableau formula_satisfiable)

end Stlsat.Jump.CompletenessCounterexample
