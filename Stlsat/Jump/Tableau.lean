/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Basic.Tableau

/-!
# The corrected JUMP tableau

This file formalizes the corrected `JUMP` rule from the paper, without proving
its metatheory. It is deliberately parallel to `Stlsat.Basic.Tableau`: adding
parent metadata to the basic occurrence type or another constructor to
`BasicRule` would invalidate exhaustive matches throughout the already proved
basic-tableau development.

The paper describes `JUMP` after replacing `F` and `G` by strict until and
strict release. The existing Lean syntax retains these unary operators, so the
definitions below include the direct, encoding-equivalent `F` and `G` cases.

The displayed successor equation writes a parent only on retained release
occurrences. Since `JUMP` is specified to simulate repeated postponement and
`STEP`, both of which retain parents, we retain the parent of every surviving
temporal occurrence; otherwise later parent-activity tests would be corrupted.
-/

namespace Stlsat.Jump

universe u

/-- A stable address for a syntactic formula occurrence. -/
abbrev OccurrenceId := List Nat

/-- A path from a formula root to one particular atomic leaf. -/
abbrev FormulaPath := List Nat

/-- One atomic-leaf occurrence and its relative window computed by `tinv`. -/
structure ValidityOccurrence where
  path : FormulaPath
  window : Stlsat.Interval
deriving DecidableEq

namespace ValidityOccurrence

/-- Extend the path with one syntax-tree edge. -/
def prefixPath (edge : Nat) (occurrence : ValidityOccurrence) : ValidityOccurrence where
  path := edge :: occurrence.path
  window := occurrence.window

/-- Shift a validity occurrence by an absolute time offset. -/
def shift (offset : Nat) (occurrence : ValidityOccurrence) : ValidityOccurrence where
  path := occurrence.path
  window := occurrence.window.shift offset

/-- Extend a window through the complete interval of a temporal operator. -/
def through (bounds : Stlsat.Interval)
    (occurrence : ValidityOccurrence) : ValidityOccurrence where
  path := occurrence.path
  window := {
    lower := occurrence.window.lower + bounds.lower
    upper := occurrence.window.upper + bounds.upper
    lower_le_upper := Nat.add_le_add occurrence.window.lower_le_upper bounds.lower_le_upper
  }

/--
Extend a window through the strict prefix of a temporal operator. This is the
paper's `(l + a, r + b - 1)` case, which exists only when `a < b`.
-/
def beforeTarget (bounds : Stlsat.Interval) (nontrivial : bounds.lower < bounds.upper)
    (occurrence : ValidityOccurrence) : ValidityOccurrence where
  path := occurrence.path
  window := {
    lower := occurrence.window.lower + bounds.lower
    upper := occurrence.window.upper + (bounds.upper - 1)
    lower_le_upper := Nat.add_le_add occurrence.window.lower_le_upper (by omega)
  }

end ValidityOccurrence

namespace FormulaValidity

variable {Atom : Type u}

/--
The paper's proposition-validity-interval function `tinv`.

Paths retain the identity of repeated syntactic atom occurrences even when
their atoms and computed windows coincide. Unary `F` and `G` use their sole
syntax-tree edge `0`; their windows agree with the strict-until/release
encodings used in the paper.
-/
def validityOccurrences : Stlsat.Formula Atom → List ValidityOccurrence
  | .truth => []
  | .atom _ =>
      [{ path := [], window := { lower := 0, upper := 0, lower_le_upper := by omega } }]
  | .neg body => (validityOccurrences body).map (ValidityOccurrence.prefixPath 0)
  | .and left right | .or left right =>
      (validityOccurrences left).map (ValidityOccurrence.prefixPath 0) ++
        (validityOccurrences right).map (ValidityOccurrence.prefixPath 1)
  | .eventually bounds body | .always bounds body =>
      (validityOccurrences body).map
        (fun occurrence => ValidityOccurrence.prefixPath 0 (occurrence.through bounds))
  | .strictUntil bounds left right | .strictRelease bounds left right =>
      (if h : bounds.lower < bounds.upper then
        (validityOccurrences left).map
          (fun occurrence => ValidityOccurrence.prefixPath 0 (occurrence.beforeTarget bounds h))
       else []) ++
        (validityOccurrences right).map
          (fun occurrence => ValidityOccurrence.prefixPath 1 (occurrence.through bounds))

end FormulaValidity

/--
A stable reference to a formula occurrence, including its complete provenance.

The recursive parent component distinguishes simultaneously live shifted
instances of the same nested syntax, which an identifier-only pointer would
conflate.
-/
inductive OccurrenceRef (Atom : Type u) where
  | mk (id : OccurrenceId) (formula : Stlsat.Formula Atom)
      (parent : Option (OccurrenceRef Atom))

namespace OccurrenceRef

variable {Atom : Type u}

private def decEq [DecidableEq Atom] :
    (left right : OccurrenceRef Atom) → Decidable (left = right)
  | .mk leftId leftFormula none, .mk rightId rightFormula none =>
      if idEq : leftId = rightId then
        if formulaEq : leftFormula = rightFormula then
          isTrue (by subst rightId; subst rightFormula; rfl)
        else
          isFalse (by intro equal; cases equal; exact formulaEq rfl)
      else
        isFalse (by intro equal; cases equal; exact idEq rfl)
  | .mk _ _ none, .mk _ _ (some _) =>
      isFalse (by intro equal; cases equal)
  | .mk _ _ (some _), .mk _ _ none =>
      isFalse (by intro equal; cases equal)
  | .mk leftId leftFormula (some leftParent),
      .mk rightId rightFormula (some rightParent) =>
      if idEq : leftId = rightId then
        if formulaEq : leftFormula = rightFormula then
          match decEq leftParent rightParent with
          | isTrue parentEq =>
              isTrue (by subst rightId; subst rightFormula; subst rightParent; rfl)
          | isFalse parentNe =>
              isFalse (by intro equal; cases equal; exact parentNe rfl)
        else
          isFalse (by intro equal; cases equal; exact formulaEq rfl)
      else
        isFalse (by intro equal; cases equal; exact idEq rfl)
termination_by left => left

instance [DecidableEq Atom] : DecidableEq (OccurrenceRef Atom) := decEq

end OccurrenceRef

/--
An occurrence used by the JUMP tableau.

Its identifier denotes its stable syntactic origin. `parent` points to the
temporal occurrence that generated it, when such a parent is recorded by the
paper's expansion table.
-/
structure AnnotatedOccurrence (Atom : Type u) where
  id : OccurrenceId
  payload : Stlsat.Occurrence Atom
  parent : Option (OccurrenceRef Atom)
deriving DecidableEq

namespace AnnotatedOccurrence

variable {Atom : Type u}

/-- Change the marked/unmarked payload while retaining identity and parent. -/
def relabel (occurrence : AnnotatedOccurrence Atom) (payload : Stlsat.Occurrence Atom)
    (parent := occurrence.parent) : AnnotatedOccurrence Atom where
  id := occurrence.id
  payload := payload
  parent := parent

/-- Create the occurrence at one child edge of the selected syntax node. -/
def child (occurrence : AnnotatedOccurrence Atom) (edge : Nat)
    (payload : Stlsat.Occurrence Atom) (parent : Option (OccurrenceRef Atom)) :
    AnnotatedOccurrence Atom where
  id := occurrence.id ++ [edge]
  payload := payload
  parent := parent

/-- Unmark an occurrence without discarding its provenance. -/
def unmark (occurrence : AnnotatedOccurrence Atom) : AnnotatedOccurrence Atom :=
  occurrence.relabel occurrence.payload.unmark

/-- Extract the formula represented by a marked or unmarked payload. -/
def formula (occurrence : AnnotatedOccurrence Atom) : Stlsat.Formula Atom :=
  match occurrence.payload with
  | .unmarked formula => formula
  | .markedEventually interval body => .eventually interval body
  | .markedAlways interval body => .always interval body
  | .markedStrictUntil interval invariant target =>
      .strictUntil interval invariant target
  | .markedStrictRelease interval target invariant =>
      .strictRelease interval target invariant

/-- The recursive reference denoted by this live occurrence. -/
def reference (occurrence : AnnotatedOccurrence Atom) : OccurrenceRef Atom :=
  .mk occurrence.id occurrence.formula occurrence.parent

def isTemporal (occurrence : AnnotatedOccurrence Atom) : Bool := occurrence.payload.isTemporal

def isUnmarkedTemporal (occurrence : AnnotatedOccurrence Atom) : Bool :=
  occurrence.payload.isUnmarkedTemporal

def markedContinuesAt (time : Nat) (occurrence : AnnotatedOccurrence Atom) : Bool :=
  occurrence.payload.markedContinuesAt time

/-- The outer temporal interval, if this occurrence has one. -/
def interval? (occurrence : AnnotatedOccurrence Atom) : Option Stlsat.Interval :=
  match occurrence.payload with
  | .unmarked (.eventually interval _)
  | .unmarked (.always interval _)
  | .unmarked (.strictUntil interval _ _)
  | .unmarked (.strictRelease interval _ _)
  | .markedEventually interval _
  | .markedAlways interval _
  | .markedStrictUntil interval _ _
  | .markedStrictRelease interval _ _ => some interval
  | _ => none

/--
The edge and invariant repeatedly emitted while a marked obligation is
postponed. `eventually` has the atom-free invariant `⊤`, so contributes none.
-/
def postponedInvariant? (occurrence : AnnotatedOccurrence Atom) :
    Option (Nat × Stlsat.Formula Atom) :=
  match occurrence.payload with
  | .markedAlways _ body => some (0, body)
  | .markedStrictUntil _ invariant _ => some (0, invariant)
  | .markedStrictRelease _ _ invariant => some (1, invariant)
  | _ => none

/--
The edge and target that could discharge a marked obligation at an
intermediate time. `always` has the atom-free releasing target `¬⊤`.
-/
def postponedTarget? (occurrence : AnnotatedOccurrence Atom) :
    Option (Nat × Stlsat.Formula Atom) :=
  match occurrence.payload with
  | .markedEventually _ body => some (0, body)
  | .markedStrictUntil _ _ target => some (1, target)
  | .markedStrictRelease _ target _ => some (0, target)
  | _ => none

end AnnotatedOccurrence

/-- Parent-annotated labels remain finite conjunctive sets. -/
abbrev Label (Atom : Type u) := Finset (AnnotatedOccurrence Atom)

/-- A node of the tableau with the corrected JUMP rule. -/
structure Node (Atom : Type u) where
  time : Nat
  label : Label Atom
deriving DecidableEq

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

/-- The root occurrence has the empty syntactic address and no parent. -/
def initial (formula : Stlsat.Formula Atom) : Node Atom where
  time := 0
  label := {{ id := [], payload := .unmarked formula, parent := none }}

/-- Forget JUMP-only metadata, obtaining a basic-tableau node. -/
def erase (node : Node Atom) : Stlsat.Node Atom where
  time := node.time
  label := node.label.image AnnotatedOccurrence.payload

def replace (node : Node Atom) (selected : AnnotatedOccurrence Atom)
    (replacement : List (AnnotatedOccurrence Atom)) : Node Atom where
  time := node.time
  label := (node.label.erase selected) ∪ replacement.toFinset

/-- The paper's parent-active predicate. -/
def ParentActive (node : Node Atom) (occurrence : AnnotatedOccurrence Atom) : Prop :=
  occurrence ∈ node.label ∧
    match occurrence.parent with
    | none => False
    | some parentRef => ∃ parent ∈ node.label, parent.reference = parentRef

/-- Parent-aware version of the basic `STEP` label. -/
def stepLabel (node : Node Atom) : Label Atom :=
  (node.label.filter fun occurrence => occurrence.isUnmarkedTemporal = true) ∪
    ((node.label.filter fun occurrence => occurrence.markedContinuesAt node.time = true).image
      AnnotatedOccurrence.unmark)

def step (node : Node Atom) : Node Atom where
  time := node.time + 1
  label := node.stepLabel

def ContainsTemporal (node : Node Atom) : Prop :=
  ∃ occurrence ∈ node.label, occurrence.isTemporal = true

/-- Reuse the basic false/local-consistency rejection checks after erasure. -/
def Rejected (semantics : Stlsat.AtomicSemantics Atom) (node : Node Atom) : Prop :=
  node.erase.Rejected semantics

end Node

/-- Parent-aware versions of all basic expansion rules. -/
inductive Expansion {Atom : Type u} [DecidableEq Atom] (node : Node Atom) :
    List (Node Atom) → Prop where
  | disjunction (selected : AnnotatedOccurrence Atom) (left right : Stlsat.Formula Atom)
      (shape : selected.payload = .unmarked (.or left right)) (present : selected ∈ node.label) :
      Expansion node
        [node.replace selected [selected.child 0 (.unmarked left) selected.parent],
         node.replace selected [selected.child 1 (.unmarked right) selected.parent]]
  | conjunction (selected : AnnotatedOccurrence Atom) (left right : Stlsat.Formula Atom)
      (shape : selected.payload = .unmarked (.and left right)) (present : selected ∈ node.label) :
      Expansion node
        [node.replace selected
          [selected.child 0 (.unmarked left) selected.parent,
           selected.child 1 (.unmarked right) selected.parent]]
  | eventuallyBeforeEnd (selected : AnnotatedOccurrence Atom) (interval : Stlsat.Interval)
      (body : Stlsat.Formula Atom)
      (shape : selected.payload = .unmarked (.eventually interval body))
      (present : selected ∈ node.label) (active : interval.lower ≤ node.time)
      (beforeEnd : node.time < interval.upper) :
      Expansion node
        [node.replace selected
          [selected.child 0 (.unmarked (body.temporalExpansion node.time)) none],
         node.replace selected
          [selected.relabel (.markedEventually interval body)]]
  | eventuallyAtEnd (selected : AnnotatedOccurrence Atom) (interval : Stlsat.Interval)
      (body : Stlsat.Formula Atom)
      (shape : selected.payload = .unmarked (.eventually interval body))
      (present : selected ∈ node.label) (atEnd : node.time = interval.upper) :
      Expansion node
        [node.replace selected
          [selected.child 0 (.unmarked (body.temporalExpansion node.time)) none]]
  | alwaysBeforeEnd (selected : AnnotatedOccurrence Atom) (interval : Stlsat.Interval)
      (body : Stlsat.Formula Atom)
      (shape : selected.payload = .unmarked (.always interval body))
      (present : selected ∈ node.label) (active : interval.lower ≤ node.time)
      (beforeEnd : node.time < interval.upper) :
      Expansion node
        [node.replace selected
          [selected.relabel (.markedAlways interval body),
           selected.child 0 (.unmarked (body.temporalExpansion node.time))
             (some selected.reference)]]
  | alwaysAtEnd (selected : AnnotatedOccurrence Atom) (interval : Stlsat.Interval)
      (body : Stlsat.Formula Atom)
      (shape : selected.payload = .unmarked (.always interval body))
      (present : selected ∈ node.label) (atEnd : node.time = interval.upper) :
      Expansion node
        [node.replace selected
          [selected.child 0 (.unmarked (body.temporalExpansion node.time))
            (some selected.reference)]]
  | strictUntilBeforeEnd (selected : AnnotatedOccurrence Atom) (interval : Stlsat.Interval)
      (invariant target : Stlsat.Formula Atom)
      (shape : selected.payload = .unmarked (.strictUntil interval invariant target))
      (present : selected ∈ node.label) (active : interval.lower ≤ node.time)
      (beforeEnd : node.time < interval.upper) :
      Expansion node
        [node.replace selected
          [selected.child 1 (.unmarked (target.temporalExpansion node.time)) none],
         node.replace selected
          [selected.relabel (.markedStrictUntil interval invariant target),
           selected.child 0 (.unmarked (invariant.temporalExpansion node.time))
             (some selected.reference)]]
  | strictUntilAtEnd (selected : AnnotatedOccurrence Atom) (interval : Stlsat.Interval)
      (invariant target : Stlsat.Formula Atom)
      (shape : selected.payload = .unmarked (.strictUntil interval invariant target))
      (present : selected ∈ node.label) (atEnd : node.time = interval.upper) :
      Expansion node
        [node.replace selected
          [selected.child 1 (.unmarked (target.temporalExpansion node.time)) none]]
  | strictReleaseBeforeEnd (selected : AnnotatedOccurrence Atom) (interval : Stlsat.Interval)
      (target invariant : Stlsat.Formula Atom)
      (shape : selected.payload = .unmarked (.strictRelease interval target invariant))
      (present : selected ∈ node.label) (active : interval.lower ≤ node.time)
      (beforeEnd : node.time < interval.upper) :
      Expansion node
        [node.replace selected
          [selected.child 0 (.unmarked (target.temporalExpansion node.time)) none,
           selected.child 1 (.unmarked (invariant.temporalExpansion node.time)) none],
         node.replace selected
          [selected.relabel (.markedStrictRelease interval target invariant),
           selected.child 1 (.unmarked (invariant.temporalExpansion node.time))
             (some selected.reference)]]
  | strictReleaseAtEnd (selected : AnnotatedOccurrence Atom) (interval : Stlsat.Interval)
      (target invariant : Stlsat.Formula Atom)
      (shape : selected.payload = .unmarked (.strictRelease interval target invariant))
      (present : selected ∈ node.label) (atEnd : node.time = interval.upper) :
      Expansion node
        [node.replace selected
          [selected.child 1 (.unmarked (invariant.temporalExpansion node.time))
            (some selected.reference)]]

/-- A validity window indexed by its canonical, root-relative atomic identity. -/
structure WindowOccurrence where
  id : OccurrenceId
  window : Stlsat.Interval
deriving DecidableEq

namespace WindowOccurrence

/-- Attach a relative atom path to the canonical identity of its formula root. -/
def ofValidity (root : OccurrenceId) (occurrence : ValidityOccurrence) :
    WindowOccurrence where
  id := root ++ occurrence.path
  window := occurrence.window

def shift (offset : Nat) (occurrence : WindowOccurrence) : WindowOccurrence where
  id := occurrence.id
  window := occurrence.window.shift offset

end WindowOccurrence

private def windowsOf {Atom : Type u} (root : OccurrenceId)
    (formula : Stlsat.Formula Atom) : List WindowOccurrence :=
  (FormulaValidity.validityOccurrences formula).map (WindowOccurrence.ofValidity root)

private def windowsThrough {Atom : Type u} (root : OccurrenceId)
    (bounds : Stlsat.Interval) (formula : Stlsat.Formula Atom) : List WindowOccurrence :=
  (FormulaValidity.validityOccurrences formula).map fun occurrence =>
    WindowOccurrence.ofValidity root (occurrence.through bounds)

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

/-- `K(u)`: temporal bounds which a jump may not cross. -/
noncomputable def boundCandidates (node : Node Atom) : List Nat := by
  classical
  exact node.label.toList.flatMap fun occurrence =>
    let bounds (interval : Stlsat.Interval) := [interval.lower, interval.upper]
    match occurrence.payload with
    | .unmarked (.eventually interval _)
    | .unmarked (.strictUntil interval _ _)
    | .markedEventually interval _
    | .markedStrictUntil interval _ _ => bounds interval
    | .unmarked (.always interval _)
    | .unmarked (.strictRelease interval _ _)
    | .markedAlways interval _
    | .markedStrictRelease interval _ _ =>
        if node.ParentActive occurrence then [] else bounds interval
    | _ => []

/-- `N(u)`: windows generated by postponed invariants at the current time. -/
noncomputable def invariantWindows (node : Node Atom) : List WindowOccurrence :=
  node.label.toList.flatMap fun occurrence =>
    match occurrence.postponedInvariant? with
    | none => []
    | some (edge, invariant) =>
        (windowsOf (occurrence.id ++ [edge]) invariant).map
          (WindowOccurrence.shift node.time)

/-- `M(u)`: windows generated by targets of postponed obligations. -/
noncomputable def targetWindows (node : Node Atom) : List WindowOccurrence :=
  node.label.toList.flatMap fun occurrence =>
    match occurrence.postponedTarget? with
    | none => []
    | some (edge, target) =>
        (windowsOf (occurrence.id ++ [edge]) target).map
          (WindowOccurrence.shift node.time)

/-- `O(u)`: windows of temporal occurrences without an active parent. -/
noncomputable def independentWindows (node : Node Atom) : List WindowOccurrence := by
  classical
  exact node.label.toList.flatMap fun occurrence =>
    if occurrence.isTemporal = true ∧ ¬node.ParentActive occurrence then
      windowsOf occurrence.id occurrence.formula
    else []

/-- `S(u)`: windows which could conflict with an intermediate target extraction. -/
noncomputable def conflictWindows (node : Node Atom) : List WindowOccurrence := by
  classical
  exact node.label.toList.flatMap fun occurrence =>
    if node.ParentActive occurrence then []
    else
      match occurrence.payload with
      | .unmarked (.atom _) =>
          [{ id := occurrence.id,
             window := { lower := node.time, upper := node.time, lower_le_upper := by omega } }]
      | .unmarked (.neg (.atom _)) =>
          [{ id := occurrence.id ++ [0],
             window := { lower := node.time, upper := node.time, lower_le_upper := by omega } }]
      | .unmarked (.strictUntil interval invariant _)
      | .markedStrictUntil interval invariant _ =>
          windowsThrough (occurrence.id ++ [0]) interval invariant
      | .unmarked (.strictRelease interval _ invariant)
      | .markedStrictRelease interval _ invariant =>
          windowsThrough (occurrence.id ++ [1]) interval invariant
      | .unmarked (.always interval invariant)
      | .markedAlways interval invariant =>
          windowsThrough (occurrence.id ++ [0]) interval invariant
      | _ => []

def WindowsOverlap (left right : WindowOccurrence) : Prop :=
  left.window.lower ≤ right.window.upper ∧ right.window.lower ≤ left.window.upper

/--
Only windows from different atomic syntax leaves can form a conflict pair.
This exclusion is needed to make the paper's worked example agree with its
own limits: an invariant window also occurs inside its governing operator's
window, but an atomic constraint cannot conflict with itself.
-/
def DistinctAtoms (left right : WindowOccurrence) : Prop := left.id ≠ right.id

/-
The text immediately before equations (sound-condition) and
(complete-condition) says that an overlap *disables* JUMP. Line 771's phrase
"satisfies both conditions" is therefore read as satisfying their no-overlap
guards, not satisfying the displayed existential overlap formulas.
-/

/-- The negation of the paper's soundness-disabling overlap condition. -/
def SoundSafe (node : Node Atom) : Prop :=
  ∀ invariant ∈ node.invariantWindows, ∀ other ∈ node.independentWindows,
    DistinctAtoms invariant other → ¬WindowsOverlap invariant other

/-- The negation of the paper's completeness-disabling overlap condition. -/
def CompleteSafe (node : Node Atom) : Prop :=
  ∀ target ∈ node.targetWindows, ∀ conflict ∈ node.conflictWindows,
    DistinctAtoms target conflict → ¬WindowsOverlap target conflict

private def minimum? : List Nat → Option Nat
  | [] => none
  | value :: values =>
      match minimum? values with
      | none => some value
      | some other => some (min value other)

/-- Minimum where `none` represents the paper's `+∞`. -/
private def minLimit : Option Nat → Option Nat → Option Nat
  | none, other | other, none => other
  | some left, some right => some (min left right)

/-- The finite distance to the next member of `K(u)`, if one exists. -/
noncomputable def boundsLimit? (node : Node Atom) : Option Nat :=
  minimum? ((node.boundCandidates.filter (node.time < ·)).map (· - node.time))

/-- The paper's soundness limit; `none` denotes `+∞`. -/
noncomputable def soundLimit? (node : Node Atom) : Option Nat :=
  minimum? (node.invariantWindows.flatMap fun invariant =>
    node.independentWindows.filterMap fun other =>
      if invariant.id ≠ other.id ∧ invariant.window.upper < other.window.lower then
        some (other.window.lower - invariant.window.upper)
      else none)

/-- The paper's completeness limit; `none` denotes `+∞`. -/
noncomputable def completeLimit? (node : Node Atom) : Option Nat :=
  minimum? (node.targetWindows.flatMap fun target =>
    node.conflictWindows.filterMap fun conflict =>
      if target.id ≠ conflict.id ∧ target.window.upper < conflict.window.lower then
        some (conflict.window.lower - target.window.upper)
      else none)

/--
The final jump size. Unlike the two conflict limits, `k(u)` must be finite:
when `K(u)` has no future member, this definition returns `none` rather than
manufacturing a destination from a soundness or completeness gap alone.
-/
noncomputable def jumpSize? (node : Node Atom) : Option Nat :=
  match node.boundsLimit? with
  | none => none
  | some bounds => minLimit (some bounds) (minLimit node.soundLimit? node.completeLimit?)

/-- JUMP is enabled exactly when both no-overlap guards and a finite size exist. -/
noncomputable def CanJump (node : Node Atom) : Prop :=
  node.SoundSafe ∧ node.CompleteSafe ∧ ∃ size, node.jumpSize? = some size

def survivesJump (destination : Nat) (occurrence : AnnotatedOccurrence Atom) : Bool :=
  match occurrence.interval? with
  | none => false
  | some interval => decide (destination ≤ interval.upper)

/--
The JUMP successor label drops local constraints, retains every unexpired
temporal operator, unmarks it, and preserves its identity and parent metadata.
-/
def jumpLabel (node : Node Atom) (size : Nat) : Label Atom :=
  ((node.label.filter fun occurrence => survivesJump (node.time + size) occurrence = true).image
    AnnotatedOccurrence.unmark)

def jump (node : Node Atom) (size : Nat) : Node Atom where
  time := node.time + size
  label := node.jumpLabel size

end Node

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

def Poised (node : Node Atom) : Prop := ¬∃ children, Expansion node children

def Accepting (semantics : Stlsat.AtomicSemantics Atom) (node : Node Atom) : Prop :=
  node.Poised ∧ ¬node.Rejected semantics ∧ node.stepLabel = ∅

def Terminal (semantics : Stlsat.AtomicSemantics Atom) (node : Node Atom) : Prop :=
  node.Rejected semantics ∨ node.Accepting semantics

end Node

/-- The basic expansion/STEP rules plus the corrected, mutually exclusive JUMP rule. -/
inductive Rule {Atom : Type u} [DecidableEq Atom]
    (semantics : Stlsat.AtomicSemantics Atom) (node : Node Atom) : List (Node Atom) → Prop where
  | expand {children : List (Node Atom)} (notRejected : ¬node.Rejected semantics)
      (expansion : Expansion node children) : Rule semantics node children
  | step (notRejected : ¬node.Rejected semantics) (poised : node.Poised)
      (hasTemporal : node.ContainsTemporal) (jumpDisabled : ¬node.CanJump) :
      Rule semantics node [node.step]
  | jump (notRejected : ¬node.Rejected semantics) (poised : node.Poised)
      (hasTemporal : node.ContainsTemporal) (sound : node.SoundSafe)
      (complete : node.CompleteSafe) (size : Nat)
      (computed : node.jumpSize? = some size) :
      Rule semantics node [node.jump size]

/-- The same finite unary/binary tree shape used by the basic tableau. -/
inductive TableauTree (Atom : Type u) where
  | leaf (node : Node Atom)
  | unary (node : Node Atom) (child : TableauTree Atom)
  | binary (node : Node Atom) (satisfy postpone : TableauTree Atom)

namespace TableauTree

variable {Atom : Type u}

def root : TableauTree Atom → Node Atom
  | .leaf node | .unary node _ | .binary node _ _ => node

def WellFormed (semantics : Stlsat.AtomicSemantics Atom) [DecidableEq Atom] :
    TableauTree Atom → Prop
  | .leaf _ => True
  | .unary node child =>
      Rule semantics node [child.root] ∧ child.WellFormed semantics
  | .binary node satisfy postpone =>
      Rule semantics node [satisfy.root, postpone.root] ∧
        satisfy.WellFormed semantics ∧ postpone.WellFormed semantics

def FrontierTerminal (semantics : Stlsat.AtomicSemantics Atom) [DecidableEq Atom] :
    TableauTree Atom → Prop
  | .leaf node => node.Terminal semantics
  | .unary _ child => child.FrontierTerminal semantics
  | .binary _ satisfy postpone =>
      satisfy.FrontierTerminal semantics ∧ postpone.FrontierTerminal semantics

def HasAcceptingLeaf (semantics : Stlsat.AtomicSemantics Atom) [DecidableEq Atom] :
    TableauTree Atom → Prop
  | .leaf node => node.Accepting semantics
  | .unary _ child => child.HasAcceptingLeaf semantics
  | .binary _ satisfy postpone =>
      satisfy.HasAcceptingLeaf semantics ∨ postpone.HasAcceptingLeaf semantics

/-- Every leaf of the JUMP tableau is rejected. -/
def AllLeavesRejected (semantics : Stlsat.AtomicSemantics Atom) [DecidableEq Atom] :
    TableauTree Atom → Prop
  | .leaf node => node.Rejected semantics
  | .unary _ child => child.AllLeavesRejected semantics
  | .binary _ satisfy postpone =>
      satisfy.AllLeavesRejected semantics ∧ postpone.AllLeavesRejected semantics

end TableauTree

/-- A fully developed tableau whose advancing rule may be STEP or corrected JUMP. -/
structure Tableau {Atom : Type u} [DecidableEq Atom]
    (semantics : Stlsat.AtomicSemantics Atom) (formula : Stlsat.Formula Atom) where
  tree : TableauTree Atom
  root_normal : formula.InStrictNormalForm
  rooted_at : tree.root = Node.initial formula
  wellFormed : tree.WellFormed semantics
  frontier_terminal : tree.FrontierTerminal semantics

namespace Tableau

/-- The JUMP tableau has a root-to-leaf branch ending at an accepting node. -/
def HasAcceptingBranch {Atom : Type u} [DecidableEq Atom]
    {semantics : Stlsat.AtomicSemantics Atom} {formula : Stlsat.Formula Atom}
    (tableau : Tableau semantics formula) : Prop :=
  tableau.tree.HasAcceptingLeaf semantics

/-- Every branch of the JUMP tableau ends at a rejected node. -/
def AllBranchesRejected {Atom : Type u} [DecidableEq Atom]
    {semantics : Stlsat.AtomicSemantics Atom} {formula : Stlsat.Formula Atom}
    (tableau : Tableau semantics formula) : Prop :=
  tableau.tree.AllLeavesRejected semantics

end Tableau

end Stlsat.Jump
