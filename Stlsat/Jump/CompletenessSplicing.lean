/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Tableau.ModelGuided
import Stlsat.Jump.RankedSplicing

/-!
# Target splicing for JUMP completeness

Completeness is not obtained by forwarding one fixed source model through a
JUMP: a marked eventuality may be witnessed strictly before the destination.
Instead, the completeness guard must allow that witness to be moved to the
current extraction alternative while preserving the other live obligations.
This file develops the semantic part of that argument.
-/

namespace Stlsat.Tableau
universe u

variable {Atom : Type u}

/-- Translate a signal to the left by reading `shift` instants later. -/
def pullSignal {semantics : Stlsat.AtomicSemantics Atom}
    (signal : Stlsat.Signal semantics) (shift : Nat) : Stlsat.Signal semantics :=
  fun instant => signal (instant + shift)

theorem satisfies_pull_iff (formula : Stlsat.Formula Atom)
    (semantics : Stlsat.AtomicSemantics Atom) (signal : Stlsat.Signal semantics)
    (start shift : Nat) :
    formula.Satisfies semantics (pullSignal signal shift) start ↔
      formula.Satisfies semantics signal (start + shift) := by
  induction formula generalizing start <;>
    simp_all [Stlsat.Formula.Satisfies, pullSignal,
      Nat.add_comm, Nat.add_left_comm]

theorem satisfies_pull (formula : Stlsat.Formula Atom)
    (semantics : Stlsat.AtomicSemantics Atom) (signal : Stlsat.Signal semantics)
    (start shift : Nat) (holds : formula.Satisfies semantics signal (start + shift)) :
    formula.Satisfies semantics (pullSignal signal shift) start :=
  (satisfies_pull_iff formula semantics signal start shift).mpr holds

namespace Node

variable [DecidableEq Atom]

omit [DecidableEq Atom] in
theorem postponedTarget_normal (source : AnnotatedOccurrence Atom)
    {edge : Nat} {target : Stlsat.Formula Atom}
    (sourceNormal : source.InStrictNormalForm)
    (shape : source.postponedTarget? = some (edge, target)) :
    target.InStrictNormalForm := by
  cases source with
  | mk id payload parent =>
      cases payload <;> simp_all [AnnotatedOccurrence.postponedTarget?,
        AnnotatedOccurrence.InStrictNormalForm, Stlsat.Occurrence.InStrictNormalForm,
        Stlsat.Formula.InStrictNormalForm]

omit [DecidableEq Atom] in
/-- A signed target leaf embeds into the signed syntax tree of its marked
source occurrence. -/
theorem postponedTarget_semantic_source
    (source : AnnotatedOccurrence Atom) {edge : Nat}
    {target : Stlsat.Formula Atom}
    (shape : source.postponedTarget? = some (edge, target))
    (active : match source.interval? with
      | some interval => interval.lower < interval.upper
      | none => False)
    (leaf : FormulaValidity.SemanticOccurrence Atom)
    (leafMem : leaf ∈ FormulaValidity.semanticOccurrences target) :
    ∃ sourceLeaf ∈ FormulaValidity.semanticOccurrences source.formula,
      source.id ++ sourceLeaf.path = source.id ++ [edge] ++ leaf.path ∧
        sourceLeaf.leaf = leaf.leaf := by
  cases source with
  | mk id payload parent =>
      cases payload with
      | unmarked formula => simp [AnnotatedOccurrence.postponedTarget?] at shape
      | markedEventually interval body =>
          simp only [AnnotatedOccurrence.postponedTarget?, Option.some.injEq,
            Prod.mk.injEq] at shape
          rcases shape with ⟨rfl, rfl⟩
          refine ⟨(leaf.through interval).prefixPath 0, ?_, ?_, rfl⟩
          · exact List.mem_map.mpr ⟨leaf, leafMem, rfl⟩
          · simp [FormulaValidity.SemanticOccurrence.prefixPath,
              FormulaValidity.SemanticOccurrence.through, List.append_assoc]
      | markedAlways interval body =>
          simp [AnnotatedOccurrence.postponedTarget?] at shape
      | markedStrictUntil interval invariant target =>
          simp only [AnnotatedOccurrence.postponedTarget?, Option.some.injEq,
            Prod.mk.injEq] at shape
          rcases shape with ⟨rfl, rfl⟩
          refine ⟨(leaf.through interval).prefixPath 1, ?_, ?_, rfl⟩
          · simp only [AnnotatedOccurrence.formula,
              FormulaValidity.semanticOccurrences, List.mem_append]
            exact Or.inr (List.mem_map.mpr ⟨leaf, leafMem, rfl⟩)
          · simp [FormulaValidity.SemanticOccurrence.prefixPath,
              FormulaValidity.SemanticOccurrence.through, List.append_assoc]
      | markedStrictRelease interval target invariant =>
          simp only [AnnotatedOccurrence.postponedTarget?, Option.some.injEq,
            Prod.mk.injEq] at shape
          rcases shape with ⟨rfl, rfl⟩
          simp only [AnnotatedOccurrence.interval?] at active
          have nontrivial : interval.lower < interval.upper := by omega
          refine ⟨(leaf.beforeTarget interval nontrivial).prefixPath 0, ?_, ?_, rfl⟩
          · simp only [AnnotatedOccurrence.formula,
              FormulaValidity.semanticOccurrences, dif_pos nontrivial,
              List.mem_append]
            exact Or.inl (List.mem_map.mpr ⟨leaf, leafMem, rfl⟩)
          · simp [FormulaValidity.SemanticOccurrence.prefixPath,
              FormulaValidity.SemanticOccurrence.beforeTarget, List.append_assoc]

/-- Reachability and timeliness place every marked target-bearing occurrence
strictly inside its interval. -/
theorem postponedTarget_active (node : Node Atom)
    (derivation : node.DerivationValid) (timely : node.Timely)
    (source : AnnotatedOccurrence Atom) (sourceMem : source ∈ node.label)
    {edge : Nat} {target : Stlsat.Formula Atom}
    (shape : source.postponedTarget? = some (edge, target)) :
    match source.interval? with
    | some interval => interval.lower ≤ node.time ∧ node.time < interval.upper
    | none => False := by
  have lower := derivation.2 source sourceMem
  have upper := (Node.timely_iff node).mp timely source sourceMem
  cases source with
  | mk id payload parent =>
      cases payload <;>
        simp_all [AnnotatedOccurrence.postponedTarget?,
          AnnotatedOccurrence.interval?,
          AnnotatedOccurrence.Timely, Stlsat.Occurrence.Timely]

/-- A semantic leaf is valuation-relevant unless it is the constant truth
leaf.  Falsity remains relevant, although a satisfied requirement can never
place a demand for it. -/
def Demanding (leaf : FormulaValidity.SemanticOccurrence Atom) : Prop :=
  leaf.leaf ≠ .truth

noncomputable def demandingLeaves
    (leaves : List (FormulaValidity.SemanticOccurrence Atom)) :
    List (FormulaValidity.SemanticOccurrence Atom) := by
  classical
  exact leaves.filter fun leaf => decide (Demanding leaf)

omit [DecidableEq Atom] in
theorem mem_demandingLeaves {leaf : FormulaValidity.SemanticOccurrence Atom}
    {leaves : List (FormulaValidity.SemanticOccurrence Atom)}
    (present : leaf ∈ leaves) (demanding : Demanding leaf) :
    leaf ∈ demandingLeaves leaves := by
  classical
  unfold demandingLeaves
  exact List.mem_filter.mpr ⟨present, by simpa using demanding⟩

omit [DecidableEq Atom] in
/-- Truth leaves need no signal agreement, so preservation on demanding
leaves suffices for relative STL satisfaction. -/
theorem satisfies_of_demandingPreserves (formula : Stlsat.Formula Atom)
    (normal : formula.InStrictNormalForm)
    (semantics : Stlsat.AtomicSemantics Atom)
    {left right : Stlsat.Signal semantics} {start : Nat}
    (holds : formula.Satisfies semantics left start)
    (preserves : ∀ occurrence ∈ demandingLeaves
        (FormulaValidity.semanticOccurrences formula), ∀ instant,
      occurrence.Supports start instant →
        occurrence.leaf.Holds semantics (left instant) →
          occurrence.leaf.Holds semantics (right instant)) :
    formula.Satisfies semantics right start := by
  apply FormulaValidity.satisfies_of_atomicallyPreserves formula normal semantics holds
  intro occurrence occurrenceMem instant support leafHolds
  by_cases truth : occurrence.leaf = .truth
  · simp [truth, FormulaValidity.SignedLeaf.Holds]
  · exact preserves occurrence
      (mem_demandingLeaves occurrenceMem truth) instant support leafHolds

omit [DecidableEq Atom] in
/-- Truth leaves likewise need no agreement for absolute tableau
satisfaction. -/
theorem satisfiesFrom_of_demandingPreserves (formula : Stlsat.Formula Atom)
    (normal : formula.InStrictNormalForm)
    (semantics : Stlsat.AtomicSemantics Atom)
    {left right : Stlsat.Signal semantics} {time : Nat}
    (holds : formula.SatisfiesFrom semantics left time)
    (preserves : ∀ occurrence ∈ demandingLeaves
        (FormulaValidity.semanticFrom time formula), ∀ instant,
      occurrence.window.lower ≤ instant → instant ≤ occurrence.window.upper →
        occurrence.leaf.Holds semantics (left instant) →
          occurrence.leaf.Holds semantics (right instant)) :
    formula.SatisfiesFrom semantics right time := by
  apply FormulaValidity.satisfiesFrom_of_absoluteAtomicallyPreserves
    formula normal semantics holds
  intro occurrence occurrenceMem instant lower upper leafHolds
  by_cases truth : occurrence.leaf = .truth
  · simp [truth, FormulaValidity.SignedLeaf.Holds]
  · exact preserves occurrence
      (mem_demandingLeaves occurrenceMem truth) instant lower upper leafHolds

/-- The valuation-relevant signed leaves of all live node obligations. -/
noncomputable def demandingLiveLeaves (node : Node Atom) :
    List (FormulaValidity.SemanticOccurrence Atom) :=
  demandingLeaves node.liveSemanticLeaves

omit [DecidableEq Atom] in
theorem reroot_mem_demandingLiveLeaves (node : Node Atom)
    (occurrence : AnnotatedOccurrence Atom) (present : occurrence ∈ node.label)
    (leaf : FormulaValidity.SemanticOccurrence Atom)
    (leafMem : leaf ∈ FormulaValidity.semanticFrom node.time occurrence.formula)
    (demanding : Demanding leaf) :
    leaf.reroot occurrence.id ∈ node.demandingLiveLeaves := by
  apply mem_demandingLeaves
  · exact node.reroot_mem_liveSemanticLeaves occurrence present leaf leafMem
  · simpa [Demanding, FormulaValidity.SemanticOccurrence.reroot] using demanding

/-- Every valuation-relevant live leaf is covered by the revised `S(u)`:
temporal leaves use their first independent temporal ancestor in `O(u)`, and
parent-independent literals use their singleton current-time window. -/
theorem demandingLeaf_covered_by_conflictWindows (node : Node Atom)
    (provenance : node.ProvenanceValid) (poised : node.Poised)
    (normal : node.InStrictNormalForm)
    {semantics : Stlsat.AtomicSemantics Atom} (model : node.Model semantics)
    (source : AnnotatedOccurrence Atom) (sourceMem : source ∈ node.label)
    (leaf : FormulaValidity.SemanticOccurrence Atom)
    (leafMem : leaf ∈ FormulaValidity.semanticFrom node.time source.formula)
    (demanding : Demanding leaf) :
    ∃ window ∈ node.conflictWindows,
      window.id = source.id ++ leaf.path ∧
      window.window.lower ≤ leaf.window.lower ∧
      leaf.window.upper ≤ window.window.upper := by
  by_cases temporal : source.isTemporal = true
  · have formulaTemporal : source.formula.isTemporal = true :=
      (AnnotatedOccurrence.formula_isTemporal source).trans temporal
    have semanticMem : leaf ∈
        FormulaValidity.semanticOccurrences source.formula := by
      rw [← FormulaValidity.semanticFrom_eq_semanticOccurrences_of_temporal
        source.formula formulaTemporal node.time]
      exact leafMem
    have validityMem := FormulaValidity.toValidity_mem_validityOccurrences
      source.formula leaf semanticMem
    rcases node.validity_covered_by_independent_ancestor provenance source sourceMem
        temporal leaf.toValidity validityMem with
      ⟨window, windowMem, identifier, lower, upper⟩
    exact ⟨window, node.independentWindow_mem_conflictWindows window windowMem,
      identifier, lower, upper⟩
  · have nonTemporal : source.isTemporal = false := Bool.eq_false_of_not_eq_true temporal
    by_cases parentActive : node.ParentActive source
    · rcases parentActive with ⟨_, activeParent⟩
      cases parentEq : source.parent with
      | none => simp [parentEq] at activeParent
      | some parentRef =>
          rw [parentEq] at activeParent
          rcases activeParent with ⟨parent, parentMem, reference⟩
          cases parentRef with
          | mk parentId parentFormula parentParent =>
              have sourceLink := provenance source sourceMem
              simp only [AnnotatedOccurrence.ParentLinkValid, parentEq] at sourceLink
              rcases sourceLink with ⟨parentTemporalFormula, covered⟩
              have validityMem : leaf.toValidity ∈
                  FormulaValidity.validityFrom node.time source.formula := by
                have occurrenceNormal := (Node.normal_iff node).mp normal source sourceMem
                cases source with
                | mk id payload sourceParent =>
                    cases payload with
                    | unmarked formula =>
                        cases formula with
                        | truth =>
                            simp only [AnnotatedOccurrence.formula,
                              FormulaValidity.semanticFrom, List.mem_singleton] at leafMem
                            subst leaf
                            apply List.mem_singleton.mpr
                            rfl
                        | atom atom =>
                            simp only [AnnotatedOccurrence.formula,
                              FormulaValidity.semanticFrom, List.mem_singleton] at leafMem
                            subst leaf
                            apply List.mem_singleton.mpr
                            rfl
                        | neg body =>
                            cases body <;>
                              simp_all [AnnotatedOccurrence.formula,
                                FormulaValidity.semanticFrom,
                                FormulaValidity.validityFrom,
                                FormulaValidity.SemanticOccurrence.toValidity,
                                FormulaValidity.SemanticOccurrence.negate,
                                FormulaValidity.SemanticOccurrence.prefixPath,
                                ValidityOccurrence.prefixPath,
                                AnnotatedOccurrence.InStrictNormalForm,
                                Stlsat.Occurrence.InStrictNormalForm,
                                Stlsat.Formula.InStrictNormalForm]
                        | and left right =>
                            exact False.elim (poised ⟨_, Expansion.conjunction
                              ⟨id, .unmarked (.and left right), sourceParent⟩
                              left right rfl sourceMem⟩)
                        | or left right =>
                            exact False.elim (poised ⟨_, Expansion.disjunction
                              ⟨id, .unmarked (.or left right), sourceParent⟩
                              left right rfl sourceMem⟩)
                        | eventually interval body => simp_all
                            [AnnotatedOccurrence.isTemporal,
                              Stlsat.Occurrence.isTemporal, Stlsat.Formula.isTemporal]
                        | always interval body => simp_all
                            [AnnotatedOccurrence.isTemporal,
                              Stlsat.Occurrence.isTemporal, Stlsat.Formula.isTemporal]
                        | strictUntil interval invariant target => simp_all
                            [AnnotatedOccurrence.isTemporal,
                              Stlsat.Occurrence.isTemporal, Stlsat.Formula.isTemporal]
                        | strictRelease interval target invariant => simp_all
                            [AnnotatedOccurrence.isTemporal,
                              Stlsat.Occurrence.isTemporal, Stlsat.Formula.isTemporal]
                    | markedEventually interval body => simp_all
                        [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal]
                    | markedAlways interval body => simp_all
                        [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal]
                    | markedStrictUntil interval invariant target => simp_all
                        [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal]
                    | markedStrictRelease interval target invariant => simp_all
                        [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal]
              rcases covered leaf.toValidity validityMem with
                ⟨parentValidity, parentValidityMem, canonical, lower, upper⟩
              have parentData : parent.id = parentId ∧
                  parent.formula = parentFormula ∧ parent.parent = parentParent := by
                cases parent with
                | mk id payload parent =>
                    simp only [AnnotatedOccurrence.reference,
                      OccurrenceRef.mk.injEq] at reference
                    simpa using reference
              have parentTemporal : parent.isTemporal = true := by
                rw [← AnnotatedOccurrence.formula_isTemporal, parentData.2.1]
                exact parentTemporalFormula
              have parentValidityMem' : parentValidity ∈
                  FormulaValidity.validityOccurrences parent.formula := by
                simpa [parentData.2.1] using parentValidityMem
              rcases node.validity_covered_by_independent_ancestor provenance parent
                  parentMem parentTemporal parentValidity parentValidityMem' with
                ⟨window, windowMem, windowId, ancestorLower, ancestorUpper⟩
              refine ⟨window,
                node.independentWindow_mem_conflictWindows window windowMem, ?_, ?_, ?_⟩
              · rw [windowId, parentData.1]
                exact canonical
              · exact ancestorLower.trans lower
              · exact upper.trans ancestorUpper
    · have occurrenceNormal := (Node.normal_iff node).mp normal source sourceMem
      cases source with
      | mk id payload parent =>
          cases payload with
          | unmarked formula =>
              cases formula with
              | truth =>
                  simp only [AnnotatedOccurrence.formula,
                    FormulaValidity.semanticFrom, List.mem_singleton] at leafMem
                  subst leaf
                  simp [Demanding] at demanding
              | atom atom =>
                  simp only [AnnotatedOccurrence.formula,
                    FormulaValidity.semanticFrom, List.mem_singleton] at leafMem
                  subst leaf
                  let window : WindowOccurrence :=
                    ⟨id, ⟨node.time, node.time, le_rfl⟩⟩
                  refine ⟨window, ?_, ?_, le_rfl, le_rfl⟩
                  · apply node.atomicWindow_mem_conflictWindows window
                    unfold atomicConflictWindows
                    apply List.mem_flatMap.mpr
                    refine ⟨⟨id, .unmarked (.atom atom), parent⟩,
                      Finset.mem_toList.mpr sourceMem, ?_⟩
                    simp [parentActive, window]
                  · simp [window]
              | neg body =>
                  cases body with
                  | truth =>
                      have sourceHolds := (Node.satisfiedBy_iff node semantics model.signal).1
                        model.satisfies ⟨id, .unmarked (.neg .truth), parent⟩ sourceMem
                      simp [AnnotatedOccurrence.SatisfiedBy,
                        Stlsat.Occurrence.SatisfiedBy,
                        Stlsat.Formula.SatisfiesFrom] at sourceHolds
                  | atom atom =>
                      simp only [AnnotatedOccurrence.formula,
                        FormulaValidity.semanticFrom, List.mem_map] at leafMem
                      rcases leafMem with ⟨base, baseMem, rfl⟩
                      simp only [List.mem_singleton] at baseMem
                      subst base
                      let window : WindowOccurrence :=
                        ⟨id ++ [0], ⟨node.time, node.time, le_rfl⟩⟩
                      refine ⟨window, ?_, rfl, le_rfl, le_rfl⟩
                      apply node.atomicWindow_mem_conflictWindows window
                      unfold atomicConflictWindows
                      apply List.mem_flatMap.mpr
                      refine ⟨⟨id, .unmarked (.neg (.atom atom)), parent⟩,
                        Finset.mem_toList.mpr sourceMem, ?_⟩
                      simp [parentActive, window]
                  | neg body => simp [AnnotatedOccurrence.InStrictNormalForm,
                      Stlsat.Occurrence.InStrictNormalForm,
                      Stlsat.Formula.InStrictNormalForm] at occurrenceNormal
                  | and left right => simp [AnnotatedOccurrence.InStrictNormalForm,
                      Stlsat.Occurrence.InStrictNormalForm,
                      Stlsat.Formula.InStrictNormalForm] at occurrenceNormal
                  | or left right => simp [AnnotatedOccurrence.InStrictNormalForm,
                      Stlsat.Occurrence.InStrictNormalForm,
                      Stlsat.Formula.InStrictNormalForm] at occurrenceNormal
                  | eventually interval body => simp [AnnotatedOccurrence.InStrictNormalForm,
                      Stlsat.Occurrence.InStrictNormalForm,
                      Stlsat.Formula.InStrictNormalForm] at occurrenceNormal
                  | always interval body => simp [AnnotatedOccurrence.InStrictNormalForm,
                      Stlsat.Occurrence.InStrictNormalForm,
                      Stlsat.Formula.InStrictNormalForm] at occurrenceNormal
                  | strictUntil interval invariant target =>
                      simp [AnnotatedOccurrence.InStrictNormalForm,
                        Stlsat.Occurrence.InStrictNormalForm,
                        Stlsat.Formula.InStrictNormalForm] at occurrenceNormal
                  | strictRelease interval target invariant =>
                      simp [AnnotatedOccurrence.InStrictNormalForm,
                        Stlsat.Occurrence.InStrictNormalForm,
                        Stlsat.Formula.InStrictNormalForm] at occurrenceNormal
              | and left right => exact False.elim (poised ⟨_, Expansion.conjunction
                    ⟨id, .unmarked (.and left right), parent⟩ left right rfl sourceMem⟩)
              | or left right => exact False.elim (poised ⟨_, Expansion.disjunction
                    ⟨id, .unmarked (.or left right), parent⟩ left right rfl sourceMem⟩)
              | eventually interval body => simp_all [AnnotatedOccurrence.isTemporal,
                  Stlsat.Occurrence.isTemporal, Stlsat.Formula.isTemporal]
              | always interval body => simp_all [AnnotatedOccurrence.isTemporal,
                  Stlsat.Occurrence.isTemporal, Stlsat.Formula.isTemporal]
              | strictUntil interval invariant target => simp_all
                  [AnnotatedOccurrence.isTemporal,
                    Stlsat.Occurrence.isTemporal, Stlsat.Formula.isTemporal]
              | strictRelease interval target invariant => simp_all
                  [AnnotatedOccurrence.isTemporal,
                    Stlsat.Occurrence.isTemporal, Stlsat.Formula.isTemporal]
          | markedEventually interval body => simp_all [AnnotatedOccurrence.isTemporal,
              Stlsat.Occurrence.isTemporal]
          | markedAlways interval body => simp_all [AnnotatedOccurrence.isTemporal,
              Stlsat.Occurrence.isTemporal]
          | markedStrictUntil interval invariant target => simp_all
              [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal]
          | markedStrictRelease interval target invariant => simp_all
              [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal]

/-- An intermediate target has already been moved to the current extraction
time while the complete live node remains satisfied.  This is the certificate
returned upward through the same-time expansion phase when a JUMP successor
does not inherit the chosen model. -/
structure TargetEscape (node : Node Atom)
    (semantics : Stlsat.AtomicSemantics Atom) where
  source : AnnotatedOccurrence Atom
  sourceMem : source ∈ node.label
  edge : Nat
  target : Stlsat.Formula Atom
  shape : source.postponedTarget? = some (edge, target)
  signal : Stlsat.Signal semantics
  nodeHolds : node.SatisfiedBy semantics signal
  targetHolds : target.Satisfies semantics signal node.time

/-- Transport an escape to an earlier node of the same expansion phase. -/
def TargetEscape.lift {node child : Node Atom}
    {semantics : Stlsat.AtomicSemantics Atom}
    (escape : child.TargetEscape semantics) (sameTime : node.time = child.time)
    (sourceMem : escape.source ∈ node.label)
    (nodeHolds : node.SatisfiedBy semantics escape.signal) :
    node.TargetEscape semantics where
  source := escape.source
  sourceMem := sourceMem
  edge := escape.edge
  target := escape.target
  shape := escape.shape
  signal := escape.signal
  nodeHolds := nodeHolds
  targetHolds := by simpa [sameTime] using escape.targetHolds

/-- If none of the replacement occurrences can itself postpone a target, an
escape in the replacement node necessarily comes from an unchanged old
occurrence. -/
theorem TargetEscape.lift_of_replace {node : Node Atom}
    {semantics : Stlsat.AtomicSemantics Atom}
    {selected : AnnotatedOccurrence Atom}
    {replacement : List (AnnotatedOccurrence Atom)}
    (escape : (node.replace selected replacement).TargetEscape semantics)
    (replacementNoTarget : ∀ fresh ∈ replacement,
      fresh.postponedTarget? = none)
    (nodeHolds : node.SatisfiedBy semantics escape.signal) :
    Nonempty (node.TargetEscape semantics) := by
  have sourceMem := escape.sourceMem
  change escape.source ∈ node.label.erase selected ∪ replacement.toFinset at sourceMem
  rcases Finset.mem_union.mp sourceMem with old | fresh
  · exact ⟨escape.lift rfl (Finset.mem_of_mem_erase old) nodeHolds⟩
  · have none := replacementNoTarget escape.source (by simpa using fresh)
    have shape := escape.shape
    rw [none] at shape
    simp at shape

omit [DecidableEq Atom] in
theorem postponedTarget_eq_none_of_unmark (occurrence : AnnotatedOccurrence Atom) :
    occurrence.unmark.postponedTarget? = none := by
  cases occurrence with
  | mk id payload parent =>
      cases payload <;> simp [AnnotatedOccurrence.unmark,
        AnnotatedOccurrence.relabel, AnnotatedOccurrence.postponedTarget?,
        Stlsat.Occurrence.unmark]

omit [DecidableEq Atom] in
theorem isUnmarkedTemporal_eq_false_of_postponedTarget
    (occurrence : AnnotatedOccurrence Atom) {edge : Nat}
    {target : Stlsat.Formula Atom}
    (shape : occurrence.postponedTarget? = some (edge, target)) :
    occurrence.isUnmarkedTemporal = false := by
  cases occurrence with
  | mk id payload parent =>
      cases payload <;> simp_all [AnnotatedOccurrence.postponedTarget?,
        AnnotatedOccurrence.isUnmarkedTemporal,
        Stlsat.Occurrence.isUnmarkedTemporal]

/-- A time advance unmarks every residual, so an escape certificate cannot
cross a `STEP` boundary. -/
theorem no_targetEscape_step (node : Node Atom)
    (semantics : Stlsat.AtomicSemantics Atom) :
    ¬Nonempty (node.step.TargetEscape semantics) := by
  rintro ⟨escape⟩
  have sourceMem := escape.sourceMem
  change escape.source ∈ node.stepLabel at sourceMem
  simp only [Node.stepLabel, Finset.mem_union] at sourceMem
  rcases sourceMem with unmarked | retained
  · have temporal := (Finset.mem_filter.mp unmarked).2
    have notTemporal := isUnmarkedTemporal_eq_false_of_postponedTarget
      escape.source escape.shape
    rw [notTemporal] at temporal
    contradiction
  · rcases Finset.mem_image.mp retained with ⟨source, _, equal⟩
    have shape := escape.shape
    rw [← equal] at shape
    rw [postponedTarget_eq_none_of_unmark] at shape
    simp at shape

/-- A JUMP likewise unmarks every survivor, so an escape arising in a later
phase cannot leak backward through a JUMP. -/
theorem no_targetEscape_jump (node : Node Atom) (size : Nat)
    (semantics : Stlsat.AtomicSemantics Atom) :
    ¬Nonempty ((node.jump size).TargetEscape semantics) := by
  rintro ⟨escape⟩
  have sourceMem := escape.sourceMem
  change escape.source ∈ node.jumpLabel size at sourceMem
  rcases Finset.mem_image.mp sourceMem with ⟨source, _, equal⟩
  have shape := escape.shape
  rw [← equal] at shape
  rw [postponedTarget_eq_none_of_unmark] at shape
  simp at shape

omit [DecidableEq Atom] in
theorem eventually_later_to {interval : Stlsat.Interval}
    {body : Stlsat.Formula Atom} {semantics : Stlsat.AtomicSemantics Atom}
    {signal : Stlsat.Signal semantics} {start distance : Nat}
    (notPastLower : start + distance ≤ interval.lower)
    (holds : (Stlsat.Formula.eventually interval body).SatisfiesFrom
      semantics signal start) :
    (Stlsat.Formula.eventually interval body).SatisfiesFrom
      semantics signal (start + distance) := by
  induction distance with
  | zero => simpa using holds
  | succ distance ih =>
      apply Stlsat.Formula.eventually_later_of_beforeLower (time := start + distance)
      · omega
      · exact ih (by omega)

omit [DecidableEq Atom] in
theorem always_later_to {interval : Stlsat.Interval}
    {body : Stlsat.Formula Atom} {semantics : Stlsat.AtomicSemantics Atom}
    {signal : Stlsat.Signal semantics} {start distance : Nat}
    (notPastLower : start + distance ≤ interval.lower)
    (holds : (Stlsat.Formula.always interval body).SatisfiesFrom
      semantics signal start) :
    (Stlsat.Formula.always interval body).SatisfiesFrom
      semantics signal (start + distance) := by
  induction distance with
  | zero => simpa using holds
  | succ distance ih =>
      apply Stlsat.Formula.always_later_of_beforeLower (time := start + distance)
      · omega
      · exact ih (by omega)

omit [DecidableEq Atom] in
theorem strictUntil_later_to {interval : Stlsat.Interval}
    {invariant target : Stlsat.Formula Atom}
    {semantics : Stlsat.AtomicSemantics Atom}
    {signal : Stlsat.Signal semantics} {start distance : Nat}
    (notPastLower : start + distance ≤ interval.lower)
    (holds : (Stlsat.Formula.strictUntil interval invariant target).SatisfiesFrom
      semantics signal start) :
    (Stlsat.Formula.strictUntil interval invariant target).SatisfiesFrom
      semantics signal (start + distance) := by
  induction distance with
  | zero => simpa using holds
  | succ distance ih =>
      apply Stlsat.Formula.strictUntil_later_of_beforeLower
        (time := start + distance)
      · omega
      · exact ih (by omega)

omit [DecidableEq Atom] in
theorem strictRelease_later_to {interval : Stlsat.Interval}
    {target invariant : Stlsat.Formula Atom}
    {semantics : Stlsat.AtomicSemantics Atom}
    {signal : Stlsat.Signal semantics} {start distance : Nat}
    (notPastLower : start + distance ≤ interval.lower)
    (holds : (Stlsat.Formula.strictRelease interval target invariant).SatisfiesFrom
      semantics signal start) :
    (Stlsat.Formula.strictRelease interval target invariant).SatisfiesFrom
      semantics signal (start + distance) := by
  induction distance with
  | zero => simpa using holds
  | succ distance ih =>
      apply Stlsat.Formula.strictRelease_later_of_beforeLower
        (time := start + distance)
      · omega
      · exact ih (by omega)

/-- One witnessed target of a marked obligation, at an offset after the
current node. -/
structure TargetOrigin (node : Node Atom)
    (semantics : Stlsat.AtomicSemantics Atom) where
  source : AnnotatedOccurrence Atom
  sourceMem : source ∈ node.label
  edge : Nat
  target : Stlsat.Formula Atom
  shape : source.postponedTarget? = some (edge, target)
  offset : Nat
  positive : 0 < offset
  signal : Stlsat.Signal semantics
  holds : target.Satisfies semantics signal (node.time + offset)

/-- A live survivor either remains true at the JUMP destination or one of its
marked target alternatives was witnessed strictly inside the skipped phase.
The latter is precisely the information needed to return to the corresponding
satisfy branch. -/
theorem unmark_satisfiedBy_at_jump_or_targetOrigin_of_admissible (node : Node Atom)
    {size : Nat} {semantics : Stlsat.AtomicSemantics Atom}
    (admissible : node.JumpSizeAdmissible size) (poised : node.Poised)
    (timely : node.Timely) (model : node.Model semantics)
    (source : AnnotatedOccurrence Atom) (sourceMem : source ∈ node.label)
    (survives : survivesJump (node.time + size) source = true) :
    source.unmark.SatisfiedBy semantics model.signal (node.time + size) ∨
      Nonempty (node.TargetOrigin semantics) := by
  have sourceHolds := (Node.satisfiedBy_iff node semantics model.signal).1
    model.satisfies source sourceMem
  have sizePositive := admissible.1
  cases source with
  | mk id payload parent =>
      cases payload with
      | unmarked formula =>
          cases formula with
          | truth => simp [Node.survivesJump, AnnotatedOccurrence.interval?] at survives
          | atom atom => simp [Node.survivesJump, AnnotatedOccurrence.interval?] at survives
          | neg body => simp [Node.survivesJump, AnnotatedOccurrence.interval?] at survives
          | and left right =>
              simp [Node.survivesJump, AnnotatedOccurrence.interval?] at survives
          | or left right =>
              simp [Node.survivesJump, AnnotatedOccurrence.interval?] at survives
          | eventually interval body =>
              have beforeLower : node.time < interval.lower := by
                by_contra notBefore
                have active : interval.lower ≤ node.time := by omega
                have sourceTimely := (Node.timely_iff node).mp timely
                  ⟨id, .unmarked (.eventually interval body), parent⟩ sourceMem
                have upper : node.time ≤ interval.upper := by
                  simpa [AnnotatedOccurrence.Timely, Stlsat.Occurrence.Timely,
                    Stlsat.Formula.Timely] using sourceTimely
                apply poised
                by_cases beforeEnd : node.time < interval.upper
                · exact ⟨_, Expansion.eventuallyBeforeEnd
                    ⟨id, .unmarked (.eventually interval body), parent⟩
                    interval body rfl sourceMem active beforeEnd⟩
                · exact ⟨_, Expansion.eventuallyAtEnd
                    ⟨id, .unmarked (.eventually interval body), parent⟩
                    interval body rfl sourceMem (by omega)⟩
              have destination := node.jump_destination_le_lower_of_admissible
                ⟨id, .unmarked (.eventually interval body), parent⟩ interval
                sourceMem rfl admissible beforeLower
              left
              change (Stlsat.Formula.eventually interval body).SatisfiesFrom
                semantics model.signal (node.time + size)
              exact eventually_later_to destination sourceHolds
          | always interval body =>
              have beforeLower : node.time < interval.lower := by
                by_contra notBefore
                have active : interval.lower ≤ node.time := by omega
                have sourceTimely := (Node.timely_iff node).mp timely
                  ⟨id, .unmarked (.always interval body), parent⟩ sourceMem
                have upper : node.time ≤ interval.upper := by
                  simpa [AnnotatedOccurrence.Timely, Stlsat.Occurrence.Timely,
                    Stlsat.Formula.Timely] using sourceTimely
                apply poised
                by_cases beforeEnd : node.time < interval.upper
                · exact ⟨_, Expansion.alwaysBeforeEnd
                    ⟨id, .unmarked (.always interval body), parent⟩
                    interval body rfl sourceMem active beforeEnd⟩
                · exact ⟨_, Expansion.alwaysAtEnd
                    ⟨id, .unmarked (.always interval body), parent⟩
                    interval body rfl sourceMem (by omega)⟩
              have destination := node.jump_destination_le_lower_of_admissible
                ⟨id, .unmarked (.always interval body), parent⟩ interval
                sourceMem rfl admissible beforeLower
              left
              change (Stlsat.Formula.always interval body).SatisfiesFrom
                semantics model.signal (node.time + size)
              exact always_later_to destination sourceHolds
          | strictUntil interval invariant target =>
              have beforeLower : node.time < interval.lower := by
                by_contra notBefore
                have active : interval.lower ≤ node.time := by omega
                have sourceTimely := (Node.timely_iff node).mp timely
                  ⟨id, .unmarked (.strictUntil interval invariant target), parent⟩ sourceMem
                have upper : node.time ≤ interval.upper := by
                  simpa [AnnotatedOccurrence.Timely, Stlsat.Occurrence.Timely,
                    Stlsat.Formula.Timely] using sourceTimely
                apply poised
                by_cases beforeEnd : node.time < interval.upper
                · exact ⟨_, Expansion.strictUntilBeforeEnd
                    ⟨id, .unmarked (.strictUntil interval invariant target), parent⟩
                    interval invariant target rfl sourceMem active beforeEnd⟩
                · exact ⟨_, Expansion.strictUntilAtEnd
                    ⟨id, .unmarked (.strictUntil interval invariant target), parent⟩
                    interval invariant target rfl sourceMem (by omega)⟩
              have destination := node.jump_destination_le_lower_of_admissible
                ⟨id, .unmarked (.strictUntil interval invariant target), parent⟩ interval
                sourceMem rfl admissible beforeLower
              left
              change (Stlsat.Formula.strictUntil interval invariant target).SatisfiesFrom
                semantics model.signal (node.time + size)
              exact strictUntil_later_to destination sourceHolds
          | strictRelease interval target invariant =>
              have beforeLower : node.time < interval.lower := by
                by_contra notBefore
                have active : interval.lower ≤ node.time := by omega
                have sourceTimely := (Node.timely_iff node).mp timely
                  ⟨id, .unmarked (.strictRelease interval target invariant), parent⟩ sourceMem
                have upper : node.time ≤ interval.upper := by
                  simpa [AnnotatedOccurrence.Timely, Stlsat.Occurrence.Timely,
                    Stlsat.Formula.Timely] using sourceTimely
                apply poised
                by_cases beforeEnd : node.time < interval.upper
                · exact ⟨_, Expansion.strictReleaseBeforeEnd
                    ⟨id, .unmarked (.strictRelease interval target invariant), parent⟩
                    interval target invariant rfl sourceMem active beforeEnd⟩
                · exact ⟨_, Expansion.strictReleaseAtEnd
                    ⟨id, .unmarked (.strictRelease interval target invariant), parent⟩
                    interval target invariant rfl sourceMem (by omega)⟩
              have destination := node.jump_destination_le_lower_of_admissible
                ⟨id, .unmarked (.strictRelease interval target invariant), parent⟩ interval
                sourceMem rfl admissible beforeLower
              left
              change (Stlsat.Formula.strictRelease interval target invariant).SatisfiesFrom
                semantics model.signal (node.time + size)
              exact strictRelease_later_to destination sourceHolds
      | markedEventually interval body =>
          change (Stlsat.Formula.eventually interval body).SatisfiesFrom
            semantics model.signal (node.time + 1) at sourceHolds
          simp only [Stlsat.Formula.SatisfiesFrom] at sourceHolds
          rcases sourceHolds with ⟨offset, contained, bodyHolds⟩
          by_cases skipped : node.time + 1 + offset < node.time + size
          · right
            refine ⟨⟨⟨id, .markedEventually interval body, parent⟩, sourceMem,
              0, body, rfl, offset + 1, by omega, model.signal, ?_⟩⟩
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bodyHolds
          · left
            change (Stlsat.Formula.eventually interval body).SatisfiesFrom
              semantics model.signal (node.time + size)
            simp only [Stlsat.Formula.SatisfiesFrom]
            let shifted := node.time + 1 + offset - (node.time + size)
            refine ⟨shifted, ?_, ?_⟩
            · have equal : node.time + size + shifted = node.time + 1 + offset := by
                dsimp [shifted]
                omega
              simpa [equal] using contained
            · have equal : node.time + size + shifted = node.time + 1 + offset := by
                dsimp [shifted]
                omega
              simpa [equal] using bodyHolds
      | markedAlways interval body =>
          left
          change (Stlsat.Formula.always interval body).SatisfiesFrom
            semantics model.signal (node.time + size)
          change (Stlsat.Formula.always interval body).SatisfiesFrom
            semantics model.signal (node.time + 1) at sourceHolds
          simp only [Stlsat.Formula.SatisfiesFrom] at sourceHolds ⊢
          intro offset contained
          let shifted := node.time + size + offset - (node.time + 1)
          have equal : node.time + 1 + shifted = node.time + size + offset := by
            dsimp [shifted]
            omega
          have holds := sourceHolds shifted (by simpa [equal] using contained)
          simpa [equal] using holds
      | markedStrictUntil interval invariant target =>
          change (Stlsat.Formula.strictUntil interval invariant target).SatisfiesFrom
            semantics model.signal (node.time + 1) at sourceHolds
          simp only [Stlsat.Formula.SatisfiesFrom] at sourceHolds
          rcases sourceHolds with ⟨offset, contained, targetHolds, invariantHolds⟩
          by_cases skipped : node.time + 1 + offset < node.time + size
          · right
            refine ⟨⟨⟨id, .markedStrictUntil interval invariant target, parent⟩,
              sourceMem, 1, target, rfl, offset + 1, by omega, model.signal, ?_⟩⟩
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using targetHolds
          · left
            change (Stlsat.Formula.strictUntil interval invariant target).SatisfiesFrom
              semantics model.signal (node.time + size)
            simp only [Stlsat.Formula.SatisfiesFrom]
            let shifted := node.time + 1 + offset - (node.time + size)
            have targetEqual : node.time + size + shifted = node.time + 1 + offset := by
              dsimp [shifted]
              omega
            refine ⟨shifted, by simpa [targetEqual] using contained,
              by simpa [targetEqual] using targetHolds, ?_⟩
            intro invariantOffset lower beforeTarget
            let oldOffset := node.time + size + invariantOffset - (node.time + 1)
            have invariantEqual : node.time + 1 + oldOffset =
                node.time + size + invariantOffset := by
              dsimp [oldOffset]
              omega
            have holds := invariantHolds oldOffset
              (by simpa [invariantEqual] using lower) (by
                dsimp [oldOffset, shifted] at *
                omega)
            simpa [invariantEqual] using holds
      | markedStrictRelease interval target invariant =>
          change (Stlsat.Formula.strictRelease interval target invariant).SatisfiesFrom
            semantics model.signal (node.time + 1) at sourceHolds
          simp only [Stlsat.Formula.SatisfiesFrom] at sourceHolds
          by_cases destinationHolds :
              (Stlsat.Formula.strictRelease interval target invariant).SatisfiesFrom
                semantics model.signal (node.time + size)
          · exact Or.inl destinationHolds
          · simp only [Stlsat.Formula.SatisfiesFrom] at destinationHolds
            have violation := Classical.not_not.mp destinationHolds
            rcases violation with ⟨violatingOffset, contained, invariantFails, targetsFail⟩
            by_cases early : ∃ offset, 0 < offset ∧ offset < size ∧
                interval.lower ≤ node.time + offset ∧
                  target.Satisfies semantics model.signal (node.time + offset)
            · rcases early with ⟨offset, positive, before, _, targetHolds⟩
              right
              exact ⟨⟨⟨id, .markedStrictRelease interval target invariant, parent⟩,
                sourceMem, 0, target, rfl, offset, positive, model.signal, targetHolds⟩⟩
            · exfalso
              apply sourceHolds
              let oldOffset := node.time + size + violatingOffset - (node.time + 1)
              have violatingEqual : node.time + 1 + oldOffset =
                  node.time + size + violatingOffset := by
                dsimp [oldOffset]
                omega
              refine ⟨oldOffset, by simpa [violatingEqual] using contained,
                by simpa [violatingEqual] using invariantFails, ?_⟩
              intro targetOffset lower beforeViolation
              let absolute := node.time + 1 + targetOffset
              by_cases beforeDestination : absolute < node.time + size
              · intro targetAtAbsolute
                apply early
                let offset := absolute - node.time
                refine ⟨offset, ?_, ?_, ?_, ?_⟩
                · dsimp [offset, absolute]
                  omega
                · dsimp [offset, absolute]
                  omega
                · dsimp [offset, absolute] at *
                  omega
                · have equal : node.time + offset = absolute := by
                    dsimp [offset, absolute]
                    omega
                  simpa [equal] using targetAtAbsolute
              · let newOffset := absolute - (node.time + size)
                have targetEqual : node.time + size + newOffset = absolute := by
                  dsimp [newOffset]
                  omega
                have failed := targetsFail newOffset
                  (by simpa [targetEqual, absolute] using lower) (by
                    dsimp [newOffset, oldOffset, absolute] at *
                    omega)
                simpa [targetEqual, absolute] using failed

/-- Compatibility wrapper for the conservative JUMP calculation. -/
theorem unmark_satisfiedBy_at_jump_or_targetOrigin (node : Node Atom)
    {size : Nat} {semantics : Stlsat.AtomicSemantics Atom}
    (computed : node.jumpSize? = some size) (poised : node.Poised)
    (timely : node.Timely) (model : node.Model semantics)
    (source : AnnotatedOccurrence Atom) (sourceMem : source ∈ node.label)
    (survives : survivesJump (node.time + size) source = true) :
    source.unmark.SatisfiedBy semantics model.signal (node.time + size) ∨
      Nonempty (node.TargetOrigin semantics) :=
  node.unmark_satisfiedBy_at_jump_or_targetOrigin_of_admissible
    (node.jumpSizeAdmissible_of_computed computed) poised timely model source sourceMem survives

/-- Node-level JUMP dichotomy.  A current model either models the unique
JUMP successor directly, or exposes an intermediate postponed target. -/
theorem hasModel_jump_or_targetOrigin_of_admissible (node : Node Atom)
    {size : Nat} {semantics : Stlsat.AtomicSemantics Atom}
    (admissible : node.JumpSizeAdmissible size) (poised : node.Poised)
    (timely : node.Timely) (model : node.Model semantics) :
    (node.jump size).HasModel semantics ∨
      Nonempty (node.TargetOrigin semantics) := by
  classical
  by_cases allHold : ∀ occurrence ∈ (node.jump size).label,
      occurrence.SatisfiedBy semantics model.signal (node.time + size)
  · left
    refine ⟨⟨model.signal,
      (Node.satisfiedBy_iff (node.jump size) semantics model.signal).2 ?_⟩⟩
    intro occurrence occurrenceMem
    simpa [Node.jump] using allHold occurrence occurrenceMem
  · right
    push Not at allHold
    rcases allHold with ⟨occurrence, occurrenceMem, occurrenceFails⟩
    change occurrence ∈ node.jumpLabel size at occurrenceMem
    rcases Finset.mem_image.mp occurrenceMem with ⟨source, retained, rfl⟩
    rcases Finset.mem_filter.mp retained with ⟨sourceMem, survives⟩
    rcases node.unmark_satisfiedBy_at_jump_or_targetOrigin_of_admissible admissible poised timely
        model source sourceMem survives with destinationHolds | origin
    · exact False.elim (occurrenceFails destinationHolds)
    · exact origin

/-- Compatibility wrapper for the conservative JUMP calculation. -/
theorem hasModel_jump_or_targetOrigin (node : Node Atom)
    {size : Nat} {semantics : Stlsat.AtomicSemantics Atom}
    (computed : node.jumpSize? = some size) (poised : node.Poised)
    (timely : node.Timely) (model : node.Model semantics) :
    (node.jump size).HasModel semantics ∨ Nonempty (node.TargetOrigin semantics) :=
  node.hasModel_jump_or_targetOrigin_of_admissible
    (node.jumpSizeAdmissible_of_computed computed) poised timely model

/-- Package a semantic node model as one heterogeneous requirement, omitting
only vacuous truth leaves. -/
noncomputable def modelRequirement {node : Node Atom}
    {semantics : Stlsat.AtomicSemantics Atom}
    (normal : node.InStrictNormalForm) (model : node.Model semantics) :
    FormulaValidity.SemanticRequirement semantics where
  root := []
  leaves := node.demandingLiveLeaves
  signal := model.signal
  Accepts := node.SatisfiedBy semantics
  holds := model.satisfies
  preserves := by
    intro right preserves
    rw [Node.satisfiedBy_iff]
    intro occurrence present
    have old := (Node.satisfiedBy_iff node semantics model.signal).1
      model.satisfies occurrence present
    have occurrenceNormal := (Node.normal_iff node).mp normal occurrence present
    have formulaNormal : occurrence.formula.InStrictNormalForm := by
      cases occurrence with
      | mk id payload parent =>
          cases payload <;> simpa [AnnotatedOccurrence.formula,
            AnnotatedOccurrence.InStrictNormalForm,
            Stlsat.Occurrence.InStrictNormalForm] using occurrenceNormal
    have transport (isTemporal : occurrence.isTemporal = true) (time : Nat)
        (formulaHolds : occurrence.formula.SatisfiesFrom semantics model.signal time) :
        occurrence.formula.SatisfiesFrom semantics right time := by
      apply satisfiesFrom_of_demandingPreserves occurrence.formula formulaNormal
        semantics formulaHolds
      intro leaf leafMem instant lower upper leafHolds
      have temporal : occurrence.formula.isTemporal = true :=
        (AnnotatedOccurrence.formula_isTemporal occurrence).trans isTemporal
      have stored : leaf ∈ demandingLeaves
          (FormulaValidity.semanticFrom node.time occurrence.formula) := by
        unfold demandingLeaves at leafMem ⊢
        rw [FormulaValidity.semanticFrom_eq_of_temporal occurrence.formula temporal
          node.time time]
        exact leafMem
      apply preserves (leaf.reroot occurrence.id)
      · have storedData : leaf ∈
            FormulaValidity.semanticFrom node.time occurrence.formula ∧
            Demanding leaf := by
            unfold demandingLeaves at stored
            rcases List.mem_filter.mp stored with ⟨member, selected⟩
            exact ⟨member, by simpa using selected⟩
        exact node.reroot_mem_demandingLiveLeaves occurrence present leaf
          storedData.1 storedData.2
      · simpa [FormulaValidity.SemanticOccurrence.reroot] using lower
      · simpa [FormulaValidity.SemanticOccurrence.reroot] using upper
      · simpa [FormulaValidity.SemanticOccurrence.reroot] using leafHolds
    cases occurrence with
    | mk id payload parent =>
        cases payload with
        | unmarked formula =>
            exact satisfiesFrom_of_demandingPreserves formula formulaNormal semantics old
              (by
                intro leaf leafMem instant lower upper leafHolds
                apply preserves (leaf.reroot id)
                · have leafData : leaf ∈
                      FormulaValidity.semanticFrom node.time formula ∧
                      Demanding leaf := by
                      unfold demandingLeaves at leafMem
                      rcases List.mem_filter.mp leafMem with ⟨member, selected⟩
                      exact ⟨member, by simpa using selected⟩
                  exact node.reroot_mem_demandingLiveLeaves
                    ⟨id, .unmarked formula, parent⟩ present leaf
                      leafData.1 leafData.2
                · simpa [FormulaValidity.SemanticOccurrence.reroot] using lower
                · simpa [FormulaValidity.SemanticOccurrence.reroot] using upper
                · simpa [FormulaValidity.SemanticOccurrence.reroot] using leafHolds)
        | markedEventually interval body =>
            simpa [AnnotatedOccurrence.SatisfiedBy, Stlsat.Occurrence.SatisfiedBy,
              AnnotatedOccurrence.formula] using transport (by simp
                [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal])
              (node.time + 1) (by
                simpa [AnnotatedOccurrence.SatisfiedBy, Stlsat.Occurrence.SatisfiedBy,
                  AnnotatedOccurrence.formula] using old)
        | markedAlways interval body =>
            simpa [AnnotatedOccurrence.SatisfiedBy, Stlsat.Occurrence.SatisfiedBy,
              AnnotatedOccurrence.formula] using transport (by simp
                [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal])
              (node.time + 1) (by
                simpa [AnnotatedOccurrence.SatisfiedBy, Stlsat.Occurrence.SatisfiedBy,
                  AnnotatedOccurrence.formula] using old)
        | markedStrictUntil interval invariant target =>
            simpa [AnnotatedOccurrence.SatisfiedBy, Stlsat.Occurrence.SatisfiedBy,
              AnnotatedOccurrence.formula] using transport (by simp
                [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal])
              (node.time + 1) (by
                simpa [AnnotatedOccurrence.SatisfiedBy, Stlsat.Occurrence.SatisfiedBy,
                  AnnotatedOccurrence.formula] using old)
        | markedStrictRelease interval target invariant =>
            simpa [AnnotatedOccurrence.SatisfiedBy, Stlsat.Occurrence.SatisfiedBy,
              AnnotatedOccurrence.formula] using transport (by simp
                [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal])
              (node.time + 1) (by
                simpa [AnnotatedOccurrence.SatisfiedBy, Stlsat.Occurrence.SatisfiedBy,
                  AnnotatedOccurrence.formula] using old)

namespace TargetOrigin

variable {node : Node Atom} {semantics : Stlsat.AtomicSemantics Atom}

theorem target_normal (origin : node.TargetOrigin semantics)
    (normal : node.InStrictNormalForm) : origin.target.InStrictNormalForm :=
  postponedTarget_normal origin.source
    ((Node.normal_iff node).mp normal origin.source origin.sourceMem) origin.shape

noncomputable def semanticLeaves (origin : node.TargetOrigin semantics) :
    List (FormulaValidity.SemanticOccurrence Atom) :=
  (demandingLeaves (FormulaValidity.semanticOccurrences origin.target)).map
    fun leaf => (leaf.shift node.time).reroot (origin.source.id ++ [origin.edge])

/-- Moving a witnessed target back to the current extraction time gives a
semantic requirement whose windows are exactly its members of `M(u)`. -/
noncomputable def requirement (origin : node.TargetOrigin semantics)
    (normal : node.InStrictNormalForm) :
    FormulaValidity.SemanticRequirement semantics := by
  let translated := pullSignal origin.signal origin.offset
  have translatedHolds : origin.target.Satisfies semantics translated node.time :=
    satisfies_pull origin.target semantics origin.signal node.time origin.offset origin.holds
  exact {
    root := []
    leaves := origin.semanticLeaves
    signal := translated
    Accepts := fun right => origin.target.Satisfies semantics right node.time
    holds := translatedHolds
    preserves := by
      intro right preserves
      apply satisfies_of_demandingPreserves origin.target
        (origin.target_normal normal) semantics translatedHolds
      intro leaf leafMem instant support leafHolds
      apply preserves ((leaf.shift node.time).reroot
        (origin.source.id ++ [origin.edge]))
      · exact List.mem_map.mpr ⟨leaf, leafMem, rfl⟩
      · rcases support with ⟨lower, upper⟩
        simpa [FormulaValidity.SemanticOccurrence.reroot,
          FormulaValidity.SemanticOccurrence.shift, Stlsat.Interval.shift,
          Nat.add_comm] using lower
      · rcases support with ⟨lower, upper⟩
        simpa [FormulaValidity.SemanticOccurrence.reroot,
          FormulaValidity.SemanticOccurrence.shift, Stlsat.Interval.shift,
          Nat.add_comm] using upper
      · simpa [FormulaValidity.SemanticOccurrence.reroot,
          FormulaValidity.SemanticOccurrence.shift] using leafHolds }

/-- A witnessed postponed target can be imposed at the current time without
destroying a model of the live label.  Equal canonical paths carry the same
signed leaf; unequal paths cannot overlap because `CompleteSafe` compares the
target window with the revised, exhaustive `S(u)`. -/
theorem requirement_compatible_model (origin : node.TargetOrigin semantics)
    (derivation : node.FullDerivationValid) (timely : node.Timely)
    (poised : node.Poised) (normal : node.InStrictNormalForm)
    (complete : node.CompleteSafe) (model : node.Model semantics) :
    (origin.requirement normal).Compatible (node.modelRequirement normal model) := by
  intro targetOccurrence targetMem liveOccurrence liveMem instant
    targetLower targetUpper liveLower liveUpper
  change targetOccurrence ∈ origin.semanticLeaves at targetMem
  change liveOccurrence ∈ node.demandingLiveLeaves at liveMem
  rcases List.mem_map.mp targetMem with ⟨targetLeaf, targetLeafDemandingMem, rfl⟩
  unfold demandingLeaves at targetLeafDemandingMem
  rcases List.mem_filter.mp targetLeafDemandingMem with
    ⟨targetLeafMem, targetLeafSelected⟩
  have targetDemanding : Demanding targetLeaf := by simpa using targetLeafSelected
  unfold demandingLiveLeaves demandingLeaves at liveMem
  rcases List.mem_filter.mp liveMem with ⟨liveMem, liveSelected⟩
  have liveDemanding : Demanding liveOccurrence := by simpa using liveSelected
  unfold Node.liveSemanticLeaves at liveMem
  rcases List.mem_flatMap.mp liveMem with ⟨other, otherListMem, liveMem⟩
  have otherMem : other ∈ node.label := Finset.mem_toList.mp otherListMem
  rcases List.mem_map.mp liveMem with ⟨liveLeaf, liveLeafMem, rfl⟩
  have liveLeafDemanding : Demanding liveLeaf := by
    simpa [Demanding, FormulaValidity.SemanticOccurrence.reroot] using liveDemanding
  simp only [FormulaValidity.SemanticOccurrence.reroot]
  by_cases canonical : origin.source.id ++ [origin.edge] ++ targetLeaf.path =
      other.id ++ liveLeaf.path
  · refine ⟨canonical, ?_⟩
    change targetLeaf.leaf = liveLeaf.leaf
    have activeAtNode := node.postponedTarget_active derivation.1.1 timely
      origin.source origin.sourceMem origin.shape
    have active : match origin.source.interval? with
        | some interval => interval.lower < interval.upper
        | none => False := by
      cases intervalEq : origin.source.interval? with
      | none => simp [intervalEq] at activeAtNode
      | some interval =>
          rw [intervalEq] at activeAtNode
          simp only
          omega
    rcases postponedTarget_semantic_source origin.source origin.shape active
        targetLeaf targetLeafMem with
      ⟨targetSourceLeaf, targetSourceMem, targetSourceId, targetSourceEq⟩
    rcases FormulaValidity.semanticFrom_source other.formula node.time liveLeaf
        liveLeafMem with
      ⟨liveSourceLeaf, liveSourceMem, liveSourcePath, liveSourceEq⟩
    rw [← targetSourceEq, ← liveSourceEq]
    apply derivation.2 origin.source origin.sourceMem other otherMem
      targetSourceLeaf targetSourceMem liveSourceLeaf liveSourceMem
    rw [targetSourceId, liveSourcePath]
    exact canonical
  · exfalso
    have targetValidityMem := FormulaValidity.toValidity_mem_validityOccurrences
      origin.target targetLeaf targetLeafMem
    let targetWindow : WindowOccurrence :=
      (WindowOccurrence.ofValidity (origin.source.id ++ [origin.edge])
        targetLeaf.toValidity).shift node.time
    have targetWindowMem : targetWindow ∈ node.targetWindows := by
      exact node.targetWindow_mem origin.source origin.sourceMem origin.edge
        origin.target origin.shape targetLeaf.toValidity targetValidityMem
    rcases node.demandingLeaf_covered_by_conflictWindows derivation.1.1.1 poised
        normal model other otherMem liveLeaf liveLeafMem liveLeafDemanding with
      ⟨conflictWindow, conflictMem, conflictId, conflictLower, conflictUpper⟩
    have distinct : DistinctAtoms targetWindow conflictWindow := by
      intro equal
      apply canonical
      have targetConflict : origin.source.id ++ [origin.edge] ++ targetLeaf.path =
          conflictWindow.id := by
        simpa [DistinctAtoms, targetWindow, WindowOccurrence.ofValidity,
          WindowOccurrence.shift, FormulaValidity.SemanticOccurrence.toValidity]
          using equal
      exact targetConflict.trans conflictId
    apply complete targetWindow targetWindowMem conflictWindow conflictMem distinct
    refine ⟨?_, ?_⟩
    · simp only [FormulaValidity.SemanticOccurrence.shift,
        FormulaValidity.SemanticOccurrence.toValidity,
        FormulaValidity.SemanticOccurrence.reroot, Stlsat.Interval.shift,
        targetWindow, WindowOccurrence.ofValidity, WindowOccurrence.shift] at *
      omega
    · simp only [FormulaValidity.SemanticOccurrence.shift,
        FormulaValidity.SemanticOccurrence.toValidity,
        FormulaValidity.SemanticOccurrence.reroot, Stlsat.Interval.shift,
        targetWindow, WindowOccurrence.ofValidity, WindowOccurrence.shift] at *
      omega

/-- The completeness guard therefore supports a single signal satisfying
both the whole current node and an intermediate witnessed target. -/
theorem exists_signal_satisfying_node_and_target
    (origin : node.TargetOrigin semantics)
    (derivation : node.FullDerivationValid) (timely : node.Timely)
    (poised : node.Poised) (normal : node.InStrictNormalForm)
    (complete : node.CompleteSafe) (model : node.Model semantics) :
    ∃ signal : Stlsat.Signal semantics,
      node.SatisfiedBy semantics signal ∧
        origin.target.Satisfies semantics signal node.time := by
  classical
  let requirement : Bool → FormulaValidity.SemanticRequirement semantics
    | false => origin.requirement normal
    | true => node.modelRequirement normal model
  have cross := origin.requirement_compatible_model derivation timely poised
    normal complete model
  have compatible : ∀ first second,
      (requirement first).signal = (requirement second).signal ∨
        (requirement first).Compatible (requirement second) := by
    intro first second
    cases first <;> cases second
    · exact Or.inl rfl
    · exact Or.inr cross
    · exact Or.inr cross.symm
    · exact Or.inl rfl
  rcases FormulaValidity.exists_signal_accepting_semanticRequirement_family
      requirement compatible with ⟨signal, accepts⟩
  refine ⟨signal, ?_, ?_⟩
  · exact accepts true
  · exact accepts false

/-- The spliced signal is equivalently a same-phase escape certificate. -/
theorem exists_targetEscape (origin : node.TargetOrigin semantics)
    (derivation : node.FullDerivationValid) (timely : node.Timely)
    (poised : node.Poised) (normal : node.InStrictNormalForm)
    (complete : node.CompleteSafe) (model : node.Model semantics) :
    Nonempty (node.TargetEscape semantics) := by
  rcases origin.exists_signal_satisfying_node_and_target derivation timely poised
      normal complete model with ⟨signal, nodeHolds, targetHolds⟩
  exact ⟨⟨origin.source, origin.sourceMem, origin.edge, origin.target,
    origin.shape, signal, nodeHolds, targetHolds⟩⟩

end TargetOrigin

/-- The final local completeness alternative for JUMP: either its successor
inherits a model, or a same-phase satisfy alternative inherits one after
guarded target splicing. -/
theorem hasModel_jump_or_targetEscape (node : Node Atom)
    {size : Nat} {semantics : Stlsat.AtomicSemantics Atom}
    (computed : node.jumpSize? = some size)
    (derivation : node.FullDerivationValid) (timely : node.Timely)
    (poised : node.Poised) (normal : node.InStrictNormalForm)
    (complete : node.CompleteSafe) (model : node.Model semantics) :
    (node.jump size).HasModel semantics ∨ Nonempty (node.TargetEscape semantics) := by
  rcases node.hasModel_jump_or_targetOrigin computed poised timely model with
    childModel | origin
  · exact Or.inl childModel
  · rcases origin with ⟨origin⟩
    exact Or.inr (TargetOrigin.exists_targetEscape origin derivation timely
      poised normal complete model)

end Node
end Stlsat.Tableau
