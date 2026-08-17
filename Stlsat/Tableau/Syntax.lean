/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Mathlib.Data.Finset.Image

/-!
# Shared STL syntax and semantic obligation sets

This module contains STL syntax and the lightweight unannotated obligation set
used as the semantic projection of a canonical tableau node. Rule applications
operate on the provenance-aware representation in `Stlsat.Tableau.Core`; this
projection carries only their logical payload.
-/

namespace Stlsat

universe u v

/-- A nonempty closed interval of natural-number time instants. -/
@[ext]
structure Interval where
  /-- The first time instant in the interval. -/
  lower : ℕ
  /-- The last time instant in the interval. -/
  upper : ℕ
  /-- Closed tableau intervals are nonempty. -/
  lower_le_upper : lower ≤ upper
deriving DecidableEq

namespace Interval

/-- Whether a time instant belongs to an interval. -/
def Contains (interval : Interval) (time : ℕ) : Prop :=
  interval.lower ≤ time ∧ time ≤ interval.upper

/-- Add an offset to both endpoints of an interval. -/
def shift (interval : Interval) (offset : ℕ) : Interval where
  lower := interval.lower + offset
  upper := interval.upper + offset
  lower_le_upper := Nat.add_le_add_right interval.lower_le_upper offset

end Interval

/--
The STL syntax used by both tableau configurations.

Negation is retained as a general constructor because temporal expansion is
defined recursively through it and the rejecting formula `¬⊤` must be
representable.  `Formula.InStrictNormalForm` below restricts its use at the
root of a tableau.

For strict until, `left` is the invariant and `right` is the target.  For
strict release, as in the paper's argument order, `left` is the releasing
target and `right` is the invariant.
-/
inductive Formula (Atom : Type u) where
  | truth
  | atom (atom : Atom)
  | neg (body : Formula Atom)
  | and (left right : Formula Atom)
  | or (left right : Formula Atom)
  | eventually (interval : Interval) (body : Formula Atom)
  | always (interval : Interval) (body : Formula Atom)
  | strictUntil (interval : Interval) (left right : Formula Atom)
  | strictRelease (interval : Interval) (left right : Formula Atom)
deriving DecidableEq

namespace Formula

variable {Atom : Type u}

/--
Strict normal form: temporal operators occur positively and negation occurs
only in literals.  We also allow `¬⊤`, the false formula tested by the
tableau's explicit rejection condition.
-/
def InStrictNormalForm : Formula Atom → Prop
  | .truth | .atom _ | .neg .truth | .neg (.atom _) => True
  | .neg _ => False
  | .and left right | .or left right =>
      left.InStrictNormalForm ∧ right.InStrictNormalForm
  | .eventually _ body | .always _ body => body.InStrictNormalForm
  | .strictUntil _ left right | .strictRelease _ left right =>
      left.InStrictNormalForm ∧ right.InStrictNormalForm

/-- Whether the outermost constructor is a temporal operator. -/
def isTemporal : Formula Atom → Bool
  | .eventually _ _ | .always _ _ | .strictUntil _ _ _ | .strictRelease _ _ _ => true
  | _ => false

/--
The paper's temporal expansion `exp^time`.

Expansion recurses through propositional structure.  On reaching a temporal
operator it shifts that operator's interval and intentionally leaves its
arguments unchanged; nested intervals are shifted later, when their enclosing
formula is emitted by a tableau rule.
-/
def temporalExpansion (time : ℕ) : Formula Atom → Formula Atom
  | .truth => .truth
  | .atom proposition => .atom proposition
  | .neg body => .neg (body.temporalExpansion time)
  | .and left right =>
      .and (left.temporalExpansion time) (right.temporalExpansion time)
  | .or left right =>
      .or (left.temporalExpansion time) (right.temporalExpansion time)
  | .eventually interval body => .eventually (interval.shift time) body
  | .always interval body => .always (interval.shift time) body
  | .strictUntil interval left right =>
      .strictUntil (interval.shift time) left right
  | .strictRelease interval left right =>
      .strictRelease (interval.shift time) left right

end Formula

/--
A formula occurrence stripped of provenance metadata.

Only a temporal operator at the root of an occurrence can be marked.  The
unmarked arguments remain ordinary STL formulas. Canonical tableau occurrences
attach identity and parent metadata to this semantic payload.
-/
inductive Occurrence (Atom : Type u) where
  | unmarked (formula : Formula Atom)
  | markedEventually (interval : Interval) (body : Formula Atom)
  | markedAlways (interval : Interval) (body : Formula Atom)
  | markedStrictUntil (interval : Interval) (left right : Formula Atom)
  | markedStrictRelease (interval : Interval) (left right : Formula Atom)
deriving DecidableEq

namespace Occurrence

variable {Atom : Type u}

/-- Erase a temporal mark, leaving unmarked occurrences unchanged. -/
def unmark : Occurrence Atom → Occurrence Atom
  | occurrence@(.unmarked _) => occurrence
  | .markedEventually interval body => .unmarked (.eventually interval body)
  | .markedAlways interval body => .unmarked (.always interval body)
  | .markedStrictUntil interval left right =>
      .unmarked (.strictUntil interval left right)
  | .markedStrictRelease interval left right =>
      .unmarked (.strictRelease interval left right)

/-- Whether an occurrence has a temporal operator at its root. -/
def isTemporal : Occurrence Atom → Bool
  | .unmarked formula => formula.isTemporal
  | .markedEventually _ _
  | .markedAlways _ _
  | .markedStrictUntil _ _ _
  | .markedStrictRelease _ _ _ => true

/-- Whether an occurrence is an unmarked temporal formula. -/
def isUnmarkedTemporal : Occurrence Atom → Bool
  | .unmarked formula => formula.isTemporal
  | _ => false

/--
Whether a marked occurrence survives a `STEP` taken at `time`.

Surviving marked operators are unmarked in the successor label.
-/
def markedContinuesAt (time : ℕ) : Occurrence Atom → Bool
  | .markedEventually interval _
  | .markedAlways interval _
  | .markedStrictUntil interval _ _
  | .markedStrictRelease interval _ _ => decide (time < interval.upper)
  | .unmarked _ => false

end Occurrence

/-- The instantaneous semantics of the atomic theory used by STL formulas. -/
structure AtomicSemantics (Atom : Type u) where
  /-- Instantaneous assignments of values to the signal variables. -/
  Valuation : Type v
  /-- The atomic theory has at least one valuation. -/
  nonempty : Nonempty Valuation
  /-- Satisfaction of an atomic formula by an instantaneous valuation. -/
  holds : Valuation → Atom → Prop

namespace Occurrence

variable {Atom : Type u}

/--
The constraint imposed by an atomic literal in an occurrence.  Non-literals
do not contribute to the local arithmetic-consistency check.
-/
def LiteralSatisfied (semantics : AtomicSemantics Atom)
    (valuation : semantics.Valuation) : Occurrence Atom → Prop
  | .unmarked (.atom atom) => semantics.holds valuation atom
  | .unmarked (.neg (.atom atom)) => ¬semantics.holds valuation atom
  | _ => True

end Occurrence

/-- Labels are finite sets of formula occurrences interpreted conjunctively. -/
abbrev ObligationLabel (Atom : Type u) := Finset (Occurrence Atom)

/-- The unannotated semantic obligation set carried by a tableau node. -/
structure ObligationSet (Atom : Type u) where
  /-- The absolute time instant represented by the node. -/
  time : ℕ
  /-- Formula occurrences required conjunctively at this node. -/
  label : ObligationLabel Atom
deriving DecidableEq

namespace ObligationSet

variable {Atom : Type u} [DecidableEq Atom]

/-- The semantic projection of the root obligation for an input formula. -/
def initial (formula : Formula Atom) : ObligationSet Atom where
  time := 0
  label := {.unmarked formula}

/--
Replace one selected occurrence by a finite collection of new occurrences,
without changing the node's time counter.
-/
def replace (node : ObligationSet Atom) (selected : Occurrence Atom)
    (replacement : List (Occurrence Atom)) : ObligationSet Atom where
  time := node.time
  label := (node.label.erase selected) ∪ replacement.toFinset

/-- The label produced by the paper's `STEP` equation. -/
def stepLabel (node : ObligationSet Atom) : ObligationLabel Atom :=
  (node.label.filter fun occurrence => occurrence.isUnmarkedTemporal = true) ∪
    ((node.label.filter fun occurrence => occurrence.markedContinuesAt node.time = true).image
      Occurrence.unmark)

/-- The unique node produced by `STEP`, when the rule is applicable. -/
def step (node : ObligationSet Atom) : ObligationSet Atom where
  time := node.time + 1
  label := node.stepLabel

/-- The atomic literals in a node have a simultaneous valuation. -/
def LocallyConsistent (semantics : AtomicSemantics Atom) (node : ObligationSet Atom) : Prop :=
  ∃ valuation : semantics.Valuation,
    ∀ occurrence ∈ node.label, occurrence.LiteralSatisfied semantics valuation

/-- The two local rejection conditions shared by both rule configurations. -/
def Rejected (semantics : AtomicSemantics Atom) (node : ObligationSet Atom) : Prop :=
  .unmarked (.neg .truth) ∈ node.label ∨ ¬node.LocallyConsistent semantics

/-- Semantic characterization of a poised label: propositional formulas have
been expanded, and every unmarked temporal obligation is still before its
lower endpoint. This contains no rule or child construction. -/
def Ready (node : ObligationSet Atom) : Prop :=
  ∀ occurrence ∈ node.label,
    match occurrence with
    | .unmarked (.and _ _) | .unmarked (.or _ _) => False
    | .unmarked (.eventually interval _)
    | .unmarked (.always interval _)
    | .unmarked (.strictUntil interval _ _)
    | .unmarked (.strictRelease interval _ _) => node.time < interval.lower
    | _ => True

end ObligationSet

end Stlsat
