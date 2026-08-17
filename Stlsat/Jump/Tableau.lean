/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Basic.Tableau

/-!
# The JUMP tableau

This file formalizes the `JUMP` rule proposed in the paper, with `truth`
treated as a validity leaf in order to expose atom-free obligations to the
JUMP guards.  The definitions are deliberately parallel to
`Stlsat.Basic.Tableau`: adding
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

/-- A path from a formula root to one particular atom-or-truth leaf. -/
abbrev FormulaPath := List Nat

/-- One atom-or-truth leaf and its relative window computed by `tinv`. -/
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
The proposition-validity-interval function `tinv`, extended so that `truth`
contributes the same singleton window as an atom.  In particular,
`tinv (¬⊤)` is now nonempty.

Paths retain the identity of repeated syntactic leaf occurrences even when
their formulas and computed windows coincide. Unary `F` and `G` use their
sole syntax-tree edge `0`; their windows agree with the strict-until/release
encodings used in the paper.
-/
def validityOccurrences : Stlsat.Formula Atom → List ValidityOccurrence
  | .truth | .atom _ =>
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

/-- `truth` contributes exactly the same base validity occurrence as an atom. -/
@[simp]
theorem validityOccurrences_truth_eq_atom (atom : Atom) :
    validityOccurrences (Stlsat.Formula.truth : Stlsat.Formula Atom) =
      validityOccurrences (.atom atom) :=
  rfl

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
postponed. Native `eventually` has no explicit invariant entry here.
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
intermediate time. Native `always` has no explicit releasing-target entry here.
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

/-- A validity window indexed by its canonical, root-relative leaf identity. -/
structure WindowOccurrence where
  id : OccurrenceId
  window : Stlsat.Interval
deriving DecidableEq

namespace WindowOccurrence

/-- Attach a relative leaf path to the canonical identity of its formula root. -/
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
    | .markedStrictUntil interval _ _
    | .unmarked (.always interval _)
    | .unmarked (.strictRelease interval _ _)
    | .markedAlways interval _
    | .markedStrictRelease interval _ _ => bounds interval
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

omit [DecidableEq Atom] in
/-- Every validity occurrence of a postponed invariant gives the corresponding
absolute member of `N(u)`. -/
theorem invariantWindow_mem (node : Node Atom) (occurrence : AnnotatedOccurrence Atom)
    (present : occurrence ∈ node.label) (edge : Nat) (invariant : Stlsat.Formula Atom)
    (shape : occurrence.postponedInvariant? = some (edge, invariant))
    (validity : ValidityOccurrence)
    (validityMem : validity ∈ FormulaValidity.validityOccurrences invariant) :
    (WindowOccurrence.ofValidity (occurrence.id ++ [edge]) validity).shift node.time ∈
      node.invariantWindows := by
  classical
  unfold invariantWindows
  apply List.mem_flatMap.mpr
  refine ⟨occurrence, Finset.mem_toList.mpr present, ?_⟩
  rw [shape]
  simp only [windowsOf, List.mem_map]
  exact ⟨WindowOccurrence.ofValidity (occurrence.id ++ [edge]) validity,
    ⟨validity, validityMem, rfl⟩, rfl⟩

omit [DecidableEq Atom] in
/-- Every validity occurrence of a postponed target gives the corresponding
absolute member of `M(u)`. -/
theorem targetWindow_mem (node : Node Atom) (occurrence : AnnotatedOccurrence Atom)
    (present : occurrence ∈ node.label) (edge : Nat) (target : Stlsat.Formula Atom)
    (shape : occurrence.postponedTarget? = some (edge, target))
    (validity : ValidityOccurrence)
    (validityMem : validity ∈ FormulaValidity.validityOccurrences target) :
    (WindowOccurrence.ofValidity (occurrence.id ++ [edge]) validity).shift node.time ∈
      node.targetWindows := by
  classical
  unfold targetWindows
  apply List.mem_flatMap.mpr
  refine ⟨occurrence, Finset.mem_toList.mpr present, ?_⟩
  rw [shape]
  simp only [windowsOf, List.mem_map]
  exact ⟨WindowOccurrence.ofValidity (occurrence.id ++ [edge]) validity,
    ⟨validity, validityMem, rfl⟩, rfl⟩

omit [DecidableEq Atom] in
/-- Every validity occurrence of an independent temporal formula gives the
corresponding member of `O(u)`. -/
theorem independentWindow_mem (node : Node Atom) (occurrence : AnnotatedOccurrence Atom)
    (present : occurrence ∈ node.label) (temporal : occurrence.isTemporal = true)
    (notParentActive : ¬node.ParentActive occurrence)
    (validity : ValidityOccurrence)
    (validityMem : validity ∈ FormulaValidity.validityOccurrences occurrence.formula) :
    WindowOccurrence.ofValidity occurrence.id validity ∈ node.independentWindows := by
  classical
  unfold independentWindows
  apply List.mem_flatMap.mpr
  refine ⟨occurrence, Finset.mem_toList.mpr present, ?_⟩
  simp only [temporal, notParentActive, not_false_eq_true, and_self,
    if_true, windowsOf, List.mem_map]
  exact ⟨validity, validityMem, rfl⟩

/-- Current-time windows of non-parent-active positive and negated atoms. -/
noncomputable def atomicConflictWindows (node : Node Atom) : List WindowOccurrence := by
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
      | _ => []

/--
`S(u)`: every window in `O(u)`, together with a singleton current-time
window for each non-parent-active positive or negated atom in the label.

In particular, this includes both invariant- and target-derived validity
windows of every independent temporal occurrence.  The latter are necessary
for completeness: otherwise a JUMP may skip the only successful intermediate
target extraction.
-/
noncomputable def conflictWindows (node : Node Atom) : List WindowOccurrence :=
  node.independentWindows ++ node.atomicConflictWindows

omit [DecidableEq Atom] in
/-- Every independent validity window belongs to the completeness conflict set. -/
theorem independentWindow_mem_conflictWindows (node : Node Atom)
    (window : WindowOccurrence) (present : window ∈ node.independentWindows) :
    window ∈ node.conflictWindows := by
  exact List.mem_append.mpr (Or.inl present)

omit [DecidableEq Atom] in
/-- Every atomic current-time window belongs to the completeness conflict set. -/
theorem atomicWindow_mem_conflictWindows (node : Node Atom)
    (window : WindowOccurrence) (present : window ∈ node.atomicConflictWindows) :
    window ∈ node.conflictWindows := by
  exact List.mem_append.mpr (Or.inr present)

def WindowsOverlap (left right : WindowOccurrence) : Prop :=
  left.window.lower ≤ right.window.upper ∧ right.window.lower ≤ left.window.upper

/--
Only windows from different atom-or-truth syntax leaves can form a conflict pair.
This exclusion is needed to make the paper's worked example agree with its
own limits: an invariant window also occurs inside its governing operator's
window, but a constraint cannot conflict with itself.
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

omit [DecidableEq Atom] in
/-- The revised completeness guard tests postponed targets against every
window in `O(u)`. -/
theorem CompleteSafe.disjoint_independent {node : Node Atom}
    (complete : node.CompleteSafe) {target other : WindowOccurrence}
    (targetMem : target ∈ node.targetWindows)
    (otherMem : other ∈ node.independentWindows)
    (distinct : DistinctAtoms target other) :
    ¬WindowsOverlap target other :=
  complete target targetMem other
    (node.independentWindow_mem_conflictWindows other otherMem) distinct

omit [DecidableEq Atom] in
/-- The revised completeness guard also tests postponed targets against
non-parent-active atomic constraints at the current time. -/
theorem CompleteSafe.disjoint_atomic {node : Node Atom}
    (complete : node.CompleteSafe) {target atom : WindowOccurrence}
    (targetMem : target ∈ node.targetWindows)
    (atomMem : atom ∈ node.atomicConflictWindows)
    (distinct : DistinctAtoms target atom) :
    ¬WindowsOverlap target atom :=
  complete target targetMem atom
    (node.atomicWindow_mem_conflictWindows atom atomMem) distinct

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

private theorem minimum?_eq_none_iff (values : List Nat) :
    minimum? values = none ↔ values = [] := by
  cases values with
  | nil => simp [minimum?]
  | cons head tail =>
      cases computed : minimum? tail <;> simp [minimum?, computed]

private theorem minimum?_le_of_mem {values : List Nat} {minimum value : Nat}
    (computed : minimum? values = some minimum) (present : value ∈ values) :
    minimum ≤ value := by
  induction values generalizing minimum with
  | nil => simp at present
  | cons head tail ih =>
      simp only [minimum?] at computed
      simp only [List.mem_cons] at present
      cases tailMinimum : minimum? tail with
      | none =>
          simp only [tailMinimum, Option.some.injEq] at computed
          subst minimum
          have tailEmpty := (minimum?_eq_none_iff tail).mp tailMinimum
          subst tail
          rcases present with equal | impossible
          · exact Nat.le_of_eq equal.symm
          · simp at impossible
      | some other =>
          simp only [tailMinimum, Option.some.injEq] at computed
          subst minimum
          rcases present with rfl | tailPresent
          · exact Nat.min_le_left _ _
          · exact (Nat.min_le_right _ _).trans (ih tailMinimum tailPresent)

private theorem minimum?_positive_of_all_positive {values : List Nat} {minimum : Nat}
    (computed : minimum? values = some minimum)
    (positive : ∀ value ∈ values, 0 < value) : 0 < minimum := by
  induction values generalizing minimum with
  | nil => simp [minimum?] at computed
  | cons head tail ih =>
      cases tailMinimum : minimum? tail with
      | none =>
          simp only [minimum?, tailMinimum, Option.some.injEq] at computed
          subst minimum
          exact positive head (by simp)
      | some other =>
          simp only [minimum?, tailMinimum, Option.some.injEq] at computed
          subst minimum
          exact (Nat.lt_min).2 ⟨positive head (by simp),
            ih tailMinimum (fun value present => positive value (by simp [present]))⟩

private theorem minLimit_some_left_le {left result : Nat} {right : Option Nat}
    (computed : minLimit (some left) right = some result) : result ≤ left := by
  cases right with
  | none =>
      simp only [minLimit, Option.some.injEq] at computed
      subst result
      exact le_rfl
  | some right =>
      simp only [minLimit, Option.some.injEq] at computed
      subst result
      exact Nat.min_le_left _ _

private theorem minLimit_positive {left right : Option Nat} {result : Nat}
    (leftPositive : ∀ value, left = some value → 0 < value)
    (rightPositive : ∀ value, right = some value → 0 < value)
    (computed : minLimit left right = some result) : 0 < result := by
  cases left with
  | none =>
      simp only [minLimit] at computed
      exact rightPositive result computed
  | some left =>
      cases right with
      | none =>
          simp only [minLimit, Option.some.injEq] at computed
          subst result
          exact leftPositive left rfl
      | some right =>
          simp only [minLimit, Option.some.injEq] at computed
          subst result
          exact (Nat.lt_min).2 ⟨leftPositive left rfl, rightPositive right rfl⟩

omit [DecidableEq Atom] in
/--
A computed jump cannot pass any future member of `K(u)`.  In particular this
now applies to the lower and upper bounds of parent-active release/always
occurrences as well as every other live temporal occurrence.
-/
theorem jumpSize_le_future_boundCandidate (node : Node Atom) {size bound : Nat}
    (computed : node.jumpSize? = some size)
    (candidate : bound ∈ node.boundCandidates) (future : node.time < bound) :
    node.time + size ≤ bound := by
  unfold jumpSize? at computed
  cases boundsComputed : node.boundsLimit? with
  | none => simp [boundsComputed] at computed
  | some bounds =>
      have size_le_bounds : size ≤ bounds :=
        minLimit_some_left_le (by simpa [boundsComputed] using computed)
      have distancePresent : bound - node.time ∈
          (node.boundCandidates.filter (node.time < ·)).map (· - node.time) := by
        apply List.mem_map.mpr
        exact ⟨bound, by simp [candidate, future], rfl⟩
      have bounds_le_distance : bounds ≤ bound - node.time := by
        apply minimum?_le_of_mem (value := bound - node.time)
        · simpa [boundsLimit?] using boundsComputed
        · exact distancePresent
      omega

omit [DecidableEq Atom] in
/-- Every computed JUMP advances time by at least one instant. -/
theorem jumpSize_pos (node : Node Atom) {size : Nat}
    (computed : node.jumpSize? = some size) : 0 < size := by
  have boundsPositive : ∀ value, node.boundsLimit? = some value → 0 < value := by
    intro value valueComputed
    apply minimum?_positive_of_all_positive (by simpa [boundsLimit?] using valueComputed)
    intro distance present
    rcases List.mem_map.mp present with ⟨bound, boundPresent, rfl⟩
    have future : node.time < bound := by
      simpa using (List.mem_filter.mp boundPresent).2
    omega
  have soundPositive : ∀ value, node.soundLimit? = some value → 0 < value := by
    intro value valueComputed
    apply minimum?_positive_of_all_positive (by simpa [soundLimit?] using valueComputed)
    intro distance present
    rcases List.mem_flatMap.mp present with ⟨invariant, _, present⟩
    rcases List.mem_filterMap.mp present with ⟨other, _, selected⟩
    split at selected <;> simp_all
    omega
  have completePositive : ∀ value, node.completeLimit? = some value → 0 < value := by
    intro value valueComputed
    apply minimum?_positive_of_all_positive (by simpa [completeLimit?] using valueComputed)
    intro distance present
    rcases List.mem_flatMap.mp present with ⟨target, _, present⟩
    rcases List.mem_filterMap.mp present with ⟨conflict, _, selected⟩
    split at selected <;> simp_all
    omega
  unfold jumpSize? at computed
  cases boundsComputed : node.boundsLimit? with
  | none => simp [boundsComputed] at computed
  | some bounds =>
      apply minLimit_positive
        (left := some bounds) (right := minLimit node.soundLimit? node.completeLimit?)
        (fun value equal => by
          simp only [Option.some.injEq] at equal
          subst value
          exact boundsPositive bounds boundsComputed)
        (fun value equal => minLimit_positive soundPositive completePositive equal)
        (by simpa [boundsComputed] using computed)

omit [DecidableEq Atom] in
/-- The final jump size is bounded by every finite soundness limit. -/
theorem jumpSize_le_soundLimit (node : Node Atom) {size limit : Nat}
    (computed : node.jumpSize? = some size)
    (soundComputed : node.soundLimit? = some limit) : size ≤ limit := by
  unfold jumpSize? at computed
  cases boundsComputed : node.boundsLimit? with
  | none => simp [boundsComputed] at computed
  | some bounds =>
      cases completeComputed : node.completeLimit? <;>
        simp [boundsComputed, soundComputed, completeComputed, minLimit] at computed <;>
        omega

omit [DecidableEq Atom] in
/-- The final jump size is bounded by every finite completeness limit. -/
theorem jumpSize_le_completeLimit (node : Node Atom) {size limit : Nat}
    (computed : node.jumpSize? = some size)
    (completeComputed : node.completeLimit? = some limit) : size ≤ limit := by
  unfold jumpSize? at computed
  cases boundsComputed : node.boundsLimit? with
  | none => simp [boundsComputed] at computed
  | some bounds =>
      cases soundComputed : node.soundLimit? <;>
        simp [boundsComputed, soundComputed, completeComputed, minLimit] at computed <;>
        omega

omit [DecidableEq Atom] in
/-- A particular ordered `N`/`O` gap bounds the computed jump. -/
theorem jumpSize_le_soundGap (node : Node Atom) {size : Nat}
    (computed : node.jumpSize? = some size)
    (invariant other : WindowOccurrence)
    (invariantMem : invariant ∈ node.invariantWindows)
    (otherMem : other ∈ node.independentWindows)
    (distinct : invariant.id ≠ other.id)
    (ordered : invariant.window.upper < other.window.lower) :
    size ≤ other.window.lower - invariant.window.upper := by
  let gap := other.window.lower - invariant.window.upper
  have gapMem : gap ∈ node.invariantWindows.flatMap fun invariant =>
      node.independentWindows.filterMap fun other =>
        if invariant.id ≠ other.id ∧ invariant.window.upper < other.window.lower then
          some (other.window.lower - invariant.window.upper)
        else none := by
    apply List.mem_flatMap.mpr
    refine ⟨invariant, invariantMem, ?_⟩
    apply List.mem_filterMap.mpr
    exact ⟨other, otherMem, by simp [gap, distinct, ordered]⟩
  cases soundComputed : node.soundLimit? with
  | none =>
      have empty := (minimum?_eq_none_iff _).mp (by
        simpa [soundLimit?] using soundComputed)
      rw [empty] at gapMem
      simp at gapMem
  | some limit =>
      exact (node.jumpSize_le_soundLimit computed soundComputed).trans
        (minimum?_le_of_mem (by simpa [soundLimit?] using soundComputed) gapMem)

omit [DecidableEq Atom] in
/-- A particular ordered `M`/`S` gap bounds the computed jump. -/
theorem jumpSize_le_completeGap (node : Node Atom) {size : Nat}
    (computed : node.jumpSize? = some size)
    (target conflict : WindowOccurrence)
    (targetMem : target ∈ node.targetWindows)
    (conflictMem : conflict ∈ node.conflictWindows)
    (distinct : target.id ≠ conflict.id)
    (ordered : target.window.upper < conflict.window.lower) :
    size ≤ conflict.window.lower - target.window.upper := by
  let gap := conflict.window.lower - target.window.upper
  have gapMem : gap ∈ node.targetWindows.flatMap fun target =>
      node.conflictWindows.filterMap fun conflict =>
        if target.id ≠ conflict.id ∧ target.window.upper < conflict.window.lower then
          some (conflict.window.lower - target.window.upper)
        else none := by
    apply List.mem_flatMap.mpr
    refine ⟨target, targetMem, ?_⟩
    apply List.mem_filterMap.mpr
    exact ⟨conflict, conflictMem, by simp [gap, distinct, ordered]⟩
  cases completeComputed : node.completeLimit? with
  | none =>
      have empty := (minimum?_eq_none_iff _).mp (by
        simpa [completeLimit?] using completeComputed)
      rw [empty] at gapMem
      simp at gapMem
  | some limit =>
      exact (node.jumpSize_le_completeLimit computed completeComputed).trans
        (minimum?_le_of_mem (by simpa [completeLimit?] using completeComputed) gapMem)

omit [DecidableEq Atom] in
/-- Every invariant window translated to a strictly skipped instant remains
disjoint from every distinct independent window. -/
theorem shiftedInvariant_disjoint (node : Node Atom) {size offset : Nat}
    (computed : node.jumpSize? = some size) (sound : node.SoundSafe)
    (strictlySkipped : offset < size)
    (invariant other : WindowOccurrence)
    (invariantMem : invariant ∈ node.invariantWindows)
    (otherMem : other ∈ node.independentWindows)
    (distinct : invariant.id ≠ other.id) :
    ¬WindowsOverlap (invariant.shift offset) other := by
  have initiallyDisjoint := sound invariant invariantMem other otherMem distinct
  have separated : invariant.window.upper < other.window.lower ∨
      other.window.upper < invariant.window.lower := by
    by_contra notSeparated
    apply initiallyDisjoint
    exact ⟨by omega, by omega⟩
  rcases separated with invariantBefore | otherBefore
  · have bounded := node.jumpSize_le_soundGap computed invariant other invariantMem otherMem
      distinct invariantBefore
    intro overlap
    rcases overlap with ⟨left, right⟩
    simp only [WindowOccurrence.shift, Stlsat.Interval.shift] at left right
    omega
  · intro overlap
    rcases overlap with ⟨left, right⟩
    simp only [WindowOccurrence.shift, Stlsat.Interval.shift] at left right
    omega

omit [DecidableEq Atom] in
/-- Both endpoints of every live temporal occurrence occur in `K(u)`. -/
theorem interval_bounds_mem_boundCandidates (node : Node Atom)
    (occurrence : AnnotatedOccurrence Atom) (interval : Stlsat.Interval)
    (present : occurrence ∈ node.label) (shape : occurrence.interval? = some interval) :
    interval.lower ∈ node.boundCandidates ∧ interval.upper ∈ node.boundCandidates := by
  classical
  unfold boundCandidates
  have inList : occurrence ∈ node.label.toList := Finset.mem_toList.mpr present
  constructor <;>
    apply List.mem_flatMap.mpr <;>
    refine ⟨occurrence, inList, ?_⟩ <;>
    cases occurrence with
    | mk id payload parent =>
        cases payload with
        | unmarked formula =>
            cases formula <;>
              simp_all [AnnotatedOccurrence.interval?]
        | markedEventually bounds body =>
            simp_all [AnnotatedOccurrence.interval?]
        | markedAlways bounds body =>
            simp_all [AnnotatedOccurrence.interval?]
        | markedStrictUntil bounds invariant target =>
            simp_all [AnnotatedOccurrence.interval?]
        | markedStrictRelease bounds target invariant =>
            simp_all [AnnotatedOccurrence.interval?]

omit [DecidableEq Atom] in
/-- A JUMP destination cannot pass the future lower endpoint of a live operator. -/
theorem jump_destination_le_lower (node : Node Atom)
    (occurrence : AnnotatedOccurrence Atom) (interval : Stlsat.Interval) {size : Nat}
    (present : occurrence ∈ node.label) (shape : occurrence.interval? = some interval)
    (computed : node.jumpSize? = some size) (future : node.time < interval.lower) :
    node.time + size ≤ interval.lower := by
  exact node.jumpSize_le_future_boundCandidate computed
    (node.interval_bounds_mem_boundCandidates occurrence interval present shape).1 future

omit [DecidableEq Atom] in
/-- A JUMP destination cannot pass the future upper endpoint of a live operator. -/
theorem jump_destination_le_upper (node : Node Atom)
    (occurrence : AnnotatedOccurrence Atom) (interval : Stlsat.Interval) {size : Nat}
    (present : occurrence ∈ node.label) (shape : occurrence.interval? = some interval)
    (computed : node.jumpSize? = some size) (future : node.time < interval.upper) :
    node.time + size ≤ interval.upper := by
  exact node.jumpSize_le_future_boundCandidate computed
    (node.interval_bounds_mem_boundCandidates occurrence interval present shape).2 future

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

/-- The basic expansion/STEP rules plus the proposed, mutually exclusive JUMP rule. -/
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

end TableauTree

/-- A fully developed tableau whose advancing rule may be STEP or JUMP. -/
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

end Tableau

end Stlsat.Jump
