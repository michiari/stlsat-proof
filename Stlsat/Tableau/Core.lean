/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Tableau.Syntax

/-!
# Shared tableau core

This is the single implementation of formula occurrences, tableau nodes,
ordinary expansion, raw finite trees, and fully developed tableaux. Stable
occurrence identities and parent provenance are part of the canonical node:
they are semantically inert for the basic rule set and provide exactly the
metadata inspected by the optional JUMP rule.

`Development` is parameterized only by a rule relation. The basic and JUMP
variants therefore differ at the rule layer without duplicating any node,
expansion, tree, acceptance, or semantic representation.
-/

namespace Stlsat.Tableau

universe u

/-- A stable address for a syntactic formula occurrence. -/
abbrev OccurrenceId := List Nat
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
An occurrence used by both tableau configurations.

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

/-- A node in the shared tableau core. -/
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

/-- Forget tableau provenance, obtaining the semantic obligation set carried
by this node. This is a projection, not a second tableau representation. -/
def erase (node : Node Atom) : Stlsat.ObligationSet Atom where
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

/-- Every occurrence retained by `STEP` comes from a temporal occurrence in
the source label. -/
theorem containsTemporal_of_mem_stepLabel {node : Node Atom}
    {occurrence : AnnotatedOccurrence Atom} (present : occurrence ∈ node.stepLabel) :
    node.ContainsTemporal := by
  rcases Finset.mem_union.mp present with unchanged | continued
  · rcases Finset.mem_filter.mp unchanged with ⟨sourceMem, temporal⟩
    refine ⟨occurrence, sourceMem, ?_⟩
    cases occurrence with
    | mk id payload parent =>
        cases payload <;>
          simp_all [AnnotatedOccurrence.isUnmarkedTemporal,
            Stlsat.Occurrence.isUnmarkedTemporal,
            AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal,
            Stlsat.Formula.isTemporal]
  · rcases Finset.mem_image.mp continued with ⟨source, sourceFiltered, rfl⟩
    rcases Finset.mem_filter.mp sourceFiltered with ⟨sourceMem, continues⟩
    refine ⟨source, sourceMem, ?_⟩
    cases source with
    | mk id payload parent =>
        cases payload <;>
          simp_all [AnnotatedOccurrence.markedContinuesAt,
            Stlsat.Occurrence.markedContinuesAt,
            AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal]

theorem stepLabel_eq_empty_of_not_containsTemporal {node : Node Atom}
    (absent : ¬node.ContainsTemporal) : node.stepLabel = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro occurrence present
  exact absent (containsTemporal_of_mem_stepLabel present)

/-- Reuse the basic false/local-consistency rejection checks after erasure. -/
def Rejected (semantics : Stlsat.AtomicSemantics Atom) (node : Node Atom) : Prop :=
  node.erase.Rejected semantics

end Node

/-- Choosing one child produced by a rule relation on the shared node type. -/
def Child {Atom : Type u}
    (rules : Node Atom → List (Node Atom) → Prop)
    (child parent : Node Atom) : Prop :=
  ∃ children, rules parent children ∧ child ∈ children

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
namespace Node

variable {Atom : Type u} [DecidableEq Atom]

def Poised (node : Node Atom) : Prop := ¬∃ children, Expansion node children

def Accepting (semantics : Stlsat.AtomicSemantics Atom) (node : Node Atom) : Prop :=
  node.Poised ∧ ¬node.Rejected semantics ∧ node.stepLabel = ∅

def Terminal (semantics : Stlsat.AtomicSemantics Atom) (node : Node Atom) : Prop :=
  node.Rejected semantics ∨ node.Accepting semantics

end Node

/-- The same finite unary/binary tree shape used by the basic tableau. -/
inductive TableauTree (Atom : Type u) where
  | leaf (node : Node Atom)
  | unary (node : Node Atom) (child : TableauTree Atom)
  | binary (node : Node Atom) (satisfy postpone : TableauTree Atom)

namespace TableauTree

variable {Atom : Type u}

def root : TableauTree Atom → Node Atom
  | .leaf node | .unary node _ | .binary node _ _ => node

/-- Generic well-formedness for a tableau tree under a chosen rule relation.

The raw node and tree representations are independent of whether advancement
uses only `STEP` or may use the `JUMP` optimization.  The distinction belongs
solely in `rules`. -/
def WellFormedWith (rules : Node Atom → List (Node Atom) → Prop) :
    TableauTree Atom → Prop
  | .leaf _ => True
  | .unary node child =>
      rules node [child.root] ∧ child.WellFormedWith rules
  | .binary node satisfy postpone =>
      rules node [satisfy.root, postpone.root] ∧
        satisfy.WellFormedWith rules ∧ postpone.WellFormedWith rules


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

/-- A finite, fully developed tableau for an arbitrary rule set on the shared
node representation. Instantiating `rules` with the ordinary or JUMP rule
relation selects the corresponding tableau variant. -/
structure Development {Atom : Type u} [DecidableEq Atom]
    (semantics : Stlsat.AtomicSemantics Atom) (formula : Stlsat.Formula Atom)
    (rules : Node Atom → List (Node Atom) → Prop) where
  tree : TableauTree Atom
  root_normal : formula.InStrictNormalForm
  rooted_at : tree.root = Node.initial formula
  wellFormed : tree.WellFormedWith rules
  frontier_terminal : tree.FrontierTerminal semantics

namespace Development

/-- Acceptance is independent of the configured rule relation once a finite
developed tree has been supplied. -/
def HasAcceptingBranch {Atom : Type u} [DecidableEq Atom]
    {semantics : Stlsat.AtomicSemantics Atom} {formula : Stlsat.Formula Atom}
    {rules : Node Atom → List (Node Atom) → Prop}
    (tableau : Development semantics formula rules) : Prop :=
  tableau.tree.HasAcceptingLeaf semantics

end Development

end Stlsat.Tableau
