import Stlsat.Jump.UnconditionalSoundness

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
