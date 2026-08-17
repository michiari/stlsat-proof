/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Tableau.Syntax

/-!
# Semantics of signal temporal logic

This file formalizes the relative-time semantics from the paper's
"Background" section.  The concrete signals `ℕ → ℝⁿ` and linear atomic
predicates of the paper are abstracted by `AtomicSemantics`: a signal maps
each natural-number time instant to an instantaneous valuation, and
`AtomicSemantics.holds` interprets atoms on those valuations.

`Formula` is the strict-normal-form language consumed by the tableau, so its
recursive semantics contains strict until and strict release.  The ordinary
STL until and release operators from the Background section are exposed as
the semantic predicates `Formula.SatisfiesUntil` and
`Formula.SatisfiesRelease`; adding them as constructors would take formulas
outside the tableau's input language.

All interval bounds below are relative offsets.  This is distinct from the
absolute bounds produced inside tableau labels by `Formula.temporalExpansion`;
the bridge between these two views belongs to the subsequent soundness
development.
-/

namespace Stlsat

universe u

/--
A discrete-time signal for an atomic theory: an instantaneous valuation at
every natural-number time instant.
-/
abbrev Signal {Atom : Type u} (semantics : AtomicSemantics Atom) :=
  ℕ → semantics.Valuation

namespace Formula

variable {Atom : Type u}

/--
Satisfaction of a strict-normal-form formula by `signal` at `time`.

Intervals contain offsets relative to `time`.  In strict until, the invariant
is required from the lower endpoint up to, but not including, the target
offset.  Strict release is written directly as the negation of the
corresponding strict-until counterexample, exactly following its definition as
the dual of strict until in the paper.
-/
def Satisfies (formula : Formula Atom) (semantics : AtomicSemantics Atom)
    (signal : Signal semantics) (time : ℕ) : Prop :=
  match formula with
  | .truth => True
  | .atom proposition => semantics.holds (signal time) proposition
  | .neg body => ¬body.Satisfies semantics signal time
  | .and left right =>
      left.Satisfies semantics signal time ∧ right.Satisfies semantics signal time
  | .or left right =>
      left.Satisfies semantics signal time ∨ right.Satisfies semantics signal time
  | .eventually interval body =>
      ∃ offset,
        interval.Contains offset ∧ body.Satisfies semantics signal (time + offset)
  | .always interval body =>
      ∀ offset,
        interval.Contains offset → body.Satisfies semantics signal (time + offset)
  | .strictUntil interval invariant target =>
      ∃ targetOffset,
        interval.Contains targetOffset ∧
          target.Satisfies semantics signal (time + targetOffset) ∧
          ∀ invariantOffset,
            interval.lower ≤ invariantOffset → invariantOffset < targetOffset →
              invariant.Satisfies semantics signal (time + invariantOffset)
  | .strictRelease interval target invariant =>
      ¬∃ violatingOffset,
        interval.Contains violatingOffset ∧
          ¬invariant.Satisfies semantics signal (time + violatingOffset) ∧
          ∀ targetOffset,
            interval.lower ≤ targetOffset → targetOffset < violatingOffset →
              ¬target.Satisfies semantics signal (time + targetOffset)
termination_by formula

/--
Satisfaction of the Background section's ordinary STL until operator.

Unlike strict until, its invariant prefix starts at the current time (offset
zero) and includes the instant at which the target holds.
-/
def SatisfiesUntil (invariant target : Formula Atom) (semantics : AtomicSemantics Atom)
    (signal : Signal semantics) (time : ℕ) (interval : Interval) : Prop :=
  ∃ targetOffset,
    interval.Contains targetOffset ∧
      target.Satisfies semantics signal (time + targetOffset) ∧
      ∀ invariantOffset,
        invariantOffset ≤ targetOffset →
          invariant.Satisfies semantics signal (time + invariantOffset)

/--
Satisfaction of the Background section's ordinary STL release operator.

The argument order follows the paper: `target` is the releasing formula and
`invariant` is the formula that must otherwise continue to hold.  The
definition is the direct negation of an ordinary-until counterexample.
-/
def SatisfiesRelease (target invariant : Formula Atom) (semantics : AtomicSemantics Atom)
    (signal : Signal semantics) (time : ℕ) (interval : Interval) : Prop :=
  ¬∃ violatingOffset,
    interval.Contains violatingOffset ∧
      ¬invariant.Satisfies semantics signal (time + violatingOffset) ∧
      ∀ targetOffset,
        targetOffset ≤ violatingOffset →
          ¬target.Satisfies semantics signal (time + targetOffset)

/-- A formula is satisfiable when some signal satisfies it at time zero. -/
def Satisfiable (formula : Formula Atom) (semantics : AtomicSemantics Atom) : Prop :=
  ∃ signal : Signal semantics, formula.Satisfies semantics signal 0

end Formula

end Stlsat
