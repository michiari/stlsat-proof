/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Mathlib.Data.Finset.Image

/-!
# The basic STL tableau

This file formalizes the tree-shaped tableau from the paper's subsection
"Basic Tableau".  It contains the STL syntax needed by the tableau, temporal
expansion, all propositional and temporal expansion rules, the `STEP` rule,
and the accepting and rejecting leaf conditions.

The `JUMP` rule and the parent annotations used only by that rule are
deliberately absent.  Correctness results are also left to later files.
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
The STL syntax used by the basic tableau.

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
A formula occurrence in a basic-tableau label.

Only a temporal operator at the root of an occurrence can be marked.  The
unmarked arguments remain ordinary STL formulas.  Parent metadata is omitted
because it is used only by `JUMP`, which is outside this formalization.
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
abbrev Label (Atom : Type u) := Finset (Occurrence Atom)

/-- A tableau node consists of a time counter and a conjunctive label. -/
structure Node (Atom : Type u) where
  /-- The absolute time instant represented by the node. -/
  time : ℕ
  /-- Formula occurrences required conjunctively at this node. -/
  label : Label Atom
deriving DecidableEq

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

/-- The root node for an input formula. -/
def initial (formula : Formula Atom) : Node Atom where
  time := 0
  label := {.unmarked formula}

/--
Replace one selected occurrence by a finite collection of new occurrences,
without changing the node's time counter.
-/
def replace (node : Node Atom) (selected : Occurrence Atom)
    (replacement : List (Occurrence Atom)) : Node Atom where
  time := node.time
  label := (node.label.erase selected) ∪ replacement.toFinset

/-- The label produced by the paper's `STEP` equation. -/
def stepLabel (node : Node Atom) : Label Atom :=
  (node.label.filter fun occurrence => occurrence.isUnmarkedTemporal = true) ∪
    ((node.label.filter fun occurrence => occurrence.markedContinuesAt node.time = true).image
      Occurrence.unmark)

/-- The unique node produced by `STEP`, when the rule is applicable. -/
def step (node : Node Atom) : Node Atom where
  time := node.time + 1
  label := node.stepLabel

/-- Whether the label contains a marked or unmarked temporal occurrence. -/
def ContainsTemporal (node : Node Atom) : Prop :=
  ∃ occurrence ∈ node.label, occurrence.isTemporal = true

/-- The atomic literals in a node have a simultaneous valuation. -/
def LocallyConsistent (semantics : AtomicSemantics Atom) (node : Node Atom) : Prop :=
  ∃ valuation : semantics.Valuation,
    ∀ occurrence ∈ node.label, occurrence.LiteralSatisfied semantics valuation

/-- The two local rejection conditions from the basic tableau. -/
def Rejected (semantics : AtomicSemantics Atom) (node : Node Atom) : Prop :=
  .unmarked (.neg .truth) ∈ node.label ∨ ¬node.LocallyConsistent semantics

end Node

/--
One application of an expansion rule, including all of its one or two
children.  For binary rules, child order follows the table: left/right for
disjunction and satisfy-or-terminate/postpone for temporal rules.
-/
inductive Expansion {Atom : Type u} [DecidableEq Atom] (node : Node Atom) :
    List (Node Atom) → Prop where
  | disjunction (left right : Formula Atom)
      (present : Occurrence.unmarked (.or left right) ∈ node.label) :
      Expansion node
        [node.replace (.unmarked (.or left right)) [.unmarked left],
          node.replace (.unmarked (.or left right)) [.unmarked right]]
  | conjunction (left right : Formula Atom)
      (present : Occurrence.unmarked (.and left right) ∈ node.label) :
      Expansion node
        [node.replace (.unmarked (.and left right)) [.unmarked left, .unmarked right]]
  | eventuallyBeforeEnd (interval : Interval) (body : Formula Atom)
      (present : Occurrence.unmarked (.eventually interval body) ∈ node.label)
      (active : interval.lower ≤ node.time) (beforeEnd : node.time < interval.upper) :
      Expansion node
        [node.replace (.unmarked (.eventually interval body))
            [.unmarked (body.temporalExpansion node.time)],
          node.replace (.unmarked (.eventually interval body))
            [.markedEventually interval body]]
  | eventuallyAtEnd (interval : Interval) (body : Formula Atom)
      (present : Occurrence.unmarked (.eventually interval body) ∈ node.label)
      (atEnd : node.time = interval.upper) :
      Expansion node
        [node.replace (.unmarked (.eventually interval body))
          [.unmarked (body.temporalExpansion node.time)]]
  | alwaysBeforeEnd (interval : Interval) (body : Formula Atom)
      (present : Occurrence.unmarked (.always interval body) ∈ node.label)
      (active : interval.lower ≤ node.time) (beforeEnd : node.time < interval.upper) :
      Expansion node
        [node.replace (.unmarked (.always interval body))
          [.markedAlways interval body, .unmarked (body.temporalExpansion node.time)]]
  | alwaysAtEnd (interval : Interval) (body : Formula Atom)
      (present : Occurrence.unmarked (.always interval body) ∈ node.label)
      (atEnd : node.time = interval.upper) :
      Expansion node
        [node.replace (.unmarked (.always interval body))
          [.unmarked (body.temporalExpansion node.time)]]
  | strictUntilBeforeEnd (interval : Interval) (left right : Formula Atom)
      (present : Occurrence.unmarked (.strictUntil interval left right) ∈ node.label)
      (active : interval.lower ≤ node.time) (beforeEnd : node.time < interval.upper) :
      Expansion node
        [node.replace (.unmarked (.strictUntil interval left right))
            [.unmarked (right.temporalExpansion node.time)],
          node.replace (.unmarked (.strictUntil interval left right))
            [.markedStrictUntil interval left right,
              .unmarked (left.temporalExpansion node.time)]]
  | strictUntilAtEnd (interval : Interval) (left right : Formula Atom)
      (present : Occurrence.unmarked (.strictUntil interval left right) ∈ node.label)
      (atEnd : node.time = interval.upper) :
      Expansion node
        [node.replace (.unmarked (.strictUntil interval left right))
          [.unmarked (right.temporalExpansion node.time)]]
  | strictReleaseBeforeEnd (interval : Interval) (left right : Formula Atom)
      (present : Occurrence.unmarked (.strictRelease interval left right) ∈ node.label)
      (active : interval.lower ≤ node.time) (beforeEnd : node.time < interval.upper) :
      Expansion node
        [node.replace (.unmarked (.strictRelease interval left right))
            [.unmarked (left.temporalExpansion node.time),
              .unmarked (right.temporalExpansion node.time)],
          node.replace (.unmarked (.strictRelease interval left right))
            [.markedStrictRelease interval left right,
              .unmarked (right.temporalExpansion node.time)]]
  | strictReleaseAtEnd (interval : Interval) (left right : Formula Atom)
      (present : Occurrence.unmarked (.strictRelease interval left right) ∈ node.label)
      (atEnd : node.time = interval.upper) :
      Expansion node
        [node.replace (.unmarked (.strictRelease interval left right))
          [.unmarked (right.temporalExpansion node.time)]]

namespace Node

variable {Atom : Type u}

/-- A node is poised exactly when no expansion rule is applicable. -/
def Poised (node : Node Atom) [DecidableEq Atom] : Prop :=
  ¬∃ children, Expansion node children

/--
An accepting leaf: the node is poised and consistent, and advancing it would
leave no remaining temporal obligation.
-/
def Accepting (semantics : AtomicSemantics Atom) (node : Node Atom)
    [DecidableEq Atom] : Prop :=
  node.Poised ∧ ¬node.Rejected semantics ∧ node.stepLabel = ∅

/-- A node at which a complete basic-tableau branch may terminate. -/
def Terminal (semantics : AtomicSemantics Atom) (node : Node Atom)
    [DecidableEq Atom] : Prop :=
  node.Rejected semantics ∨ node.Accepting semantics

end Node

/-- A nonterminal rule application in the basic tableau. -/
inductive BasicRule {Atom : Type u} [DecidableEq Atom]
    (semantics : AtomicSemantics Atom) (node : Node Atom) : List (Node Atom) → Prop where
  | expand {children : List (Node Atom)}
      (notRejected : ¬node.Rejected semantics)
      (expansion : Expansion node children) : BasicRule semantics node children
  | step (notRejected : ¬node.Rejected semantics) (poised : node.Poised)
      (hasTemporal : node.ContainsTemporal) :
      BasicRule semantics node [node.step]

/--
An ordered tree whose nodes have zero, one, or two children, as prescribed by
the basic-tableau rules.
-/
inductive TableauTree (Atom : Type u) where
  | leaf (node : Node Atom)
  | unary (node : Node Atom) (child : TableauTree Atom)
  | binary (node : Node Atom) (satisfy postpone : TableauTree Atom)

namespace TableauTree

variable {Atom : Type u}

/-- The node at the root of a tableau tree. -/
def root : TableauTree Atom → Node Atom
  | .leaf node | .unary node _ | .binary node _ _ => node

/-- Every developed node follows one basic rule and contains all its children. -/
def WellFormed (semantics : AtomicSemantics Atom) [DecidableEq Atom] :
    TableauTree Atom → Prop
  | .leaf _ => True
  | .unary node child =>
      BasicRule semantics node [child.root] ∧ child.WellFormed semantics
  | .binary node satisfy postpone =>
      BasicRule semantics node [satisfy.root, postpone.root] ∧
        satisfy.WellFormed semantics ∧ postpone.WellFormed semantics

/-- Every leaf of the raw tree is either accepting or rejected. -/
def FrontierTerminal (semantics : AtomicSemantics Atom) [DecidableEq Atom] :
    TableauTree Atom → Prop
  | .leaf node => node.Terminal semantics
  | .unary _ child => child.FrontierTerminal semantics
  | .binary _ satisfy postpone =>
      satisfy.FrontierTerminal semantics ∧ postpone.FrontierTerminal semantics

/-- Some leaf of the raw tree is accepting. -/
def HasAcceptingLeaf (semantics : AtomicSemantics Atom) [DecidableEq Atom] :
    TableauTree Atom → Prop
  | .leaf node => node.Accepting semantics
  | .unary _ child => child.HasAcceptingLeaf semantics
  | .binary _ satisfy postpone =>
      satisfy.HasAcceptingLeaf semantics ∨ postpone.HasAcceptingLeaf semantics

/-- Every leaf of the raw tree is rejected. -/
def AllLeavesRejected (semantics : AtomicSemantics Atom) [DecidableEq Atom] :
    TableauTree Atom → Prop
  | .leaf node => node.Rejected semantics
  | .unary _ child => child.AllLeavesRejected semantics
  | .binary _ satisfy postpone =>
      satisfy.AllLeavesRejected semantics ∧ postpone.AllLeavesRejected semantics

end TableauTree

/-- A fully developed basic tableau rooted in a strict-normal-form STL formula. -/
structure BasicTableau {Atom : Type u} [DecidableEq Atom]
    (semantics : AtomicSemantics Atom) (formula : Formula Atom) where
  /-- The underlying finite tableau tree. -/
  tree : TableauTree Atom
  /-- The input formula satisfies the paper's normal-form assumption. -/
  root_normal : formula.InStrictNormalForm
  /-- The root is the singleton input label at time zero. -/
  rooted_at : tree.root = Node.initial formula
  /-- Each nonleaf is produced by one basic-tableau rule. -/
  wellFormed : tree.WellFormed semantics
  /-- Every branch has been developed to an accepting or rejected leaf. -/
  frontier_terminal : tree.FrontierTerminal semantics

namespace BasicTableau

/-- The tableau has a root-to-leaf branch ending in an accepting node. -/
def HasAcceptingBranch {Atom : Type u} [DecidableEq Atom]
    {semantics : AtomicSemantics Atom}
    {formula : Formula Atom} (tableau : BasicTableau semantics formula) : Prop :=
  tableau.tree.HasAcceptingLeaf semantics

/-- Every branch of the tableau ends in a rejected node. -/
def AllBranchesRejected {Atom : Type u} [DecidableEq Atom]
    {semantics : AtomicSemantics Atom}
    {formula : Formula Atom} (tableau : BasicTableau semantics formula) : Prop :=
  tableau.tree.AllLeavesRejected semantics

end BasicTableau

end Stlsat
