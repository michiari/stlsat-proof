/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.Variable.Coverage

/-! # Variable-aware rank-stratified splicing -/

namespace Stlsat.Tableau

universe u w

namespace Node

variable {Atom : Type u} [DecidableEq Atom]
  {Var : Type w} [DecidableEq Var]

namespace SkippedOrigin

variable {node : Node Atom} {size rank : Nat}
  {semantics : Stlsat.AtomicSemantics Atom}

/-- Two skipped requirements either repeat one canonical signed leaf or place
their simultaneous atomic demands on disjoint variable supports. -/
theorem requirements_supportCompatible
    (support : AtomicSupport semantics Var)
    (first second : node.SkippedOrigin size rank)
    (derivation : node.FullDerivationValid) (timely : node.Timely)
    (normal : node.InStrictNormalForm)
    {signal : Stlsat.Signal semantics}
    (holds : node.RankedHolds size (rank - 1) semantics signal)
    (computed : node.variableJumpSize? support.atomSupport = some size)
    (sound : node.VariableSoundSafe support.atomSupport) :
    (first.requirement derivation normal holds).SupportCompatible support.atomSupport
      (second.requirement derivation normal holds) := by
  intro left leftMem right rightMem instant leftLower leftUpper rightLower rightUpper
  change left ∈ first.semanticLeaves at leftMem
  change right ∈ second.semanticLeaves at rightMem
  rcases List.mem_map.mp leftMem with ⟨leftLeaf, leftLeafMem, rfl⟩
  rcases List.mem_map.mp rightMem with ⟨rightLeaf, rightLeafMem, rfl⟩
  simp only [FormulaValidity.SemanticOccurrence.reroot]
  by_cases canonical : first.source.id ++ [first.edge] ++ leftLeaf.path =
      second.source.id ++ [second.edge] ++ rightLeaf.path
  · apply Or.inl
    refine ⟨canonical, ?_⟩
    change leftLeaf.leaf = rightLeaf.leaf
    rcases first.semantic_source derivation timely leftLeaf leftLeafMem with
      ⟨firstSourceLeaf, firstSourceMem, firstId, firstLeafEq⟩
    rcases second.semantic_source derivation timely rightLeaf rightLeafMem with
      ⟨secondSourceLeaf, secondSourceMem, secondId, secondLeafEq⟩
    rw [← firstLeafEq, ← secondLeafEq]
    apply derivation.2 first.source first.sourceMem second.source second.sourceMem
      firstSourceLeaf firstSourceMem secondSourceLeaf secondSourceMem
    rw [firstId, secondId]
    exact canonical
  · apply Or.inr
    by_contra notDisjoint
    let firstWindow :=
      (FormulaValidity.SupportedWindowOccurrence.ofSemantic
        (first.source.id ++ [first.edge]) leftLeaf).shift node.time
    have firstWindowMem : firstWindow ∈ node.supportedInvariantWindows :=
      node.supportedInvariantWindow_mem first.source first.sourceMem first.edge
        first.invariant first.shape leftLeaf leftLeafMem
    have secondActive := node.postponedInvariant_active derivation.1.1 timely
      second.source second.sourceMem second.shape
    rcases node.skippedSemantic_covered_by_supportedIndependentAncestor
        (node.variableJumpSizeAdmissible support.atomSupport computed)
        second.skipped derivation second.source second.sourceMem second.edge
        second.invariant second.shape rightLeaf rightLeafMem secondActive with
      ⟨secondWindow, secondWindowMem, secondId, secondLeafEq, secondLower,
        secondUpper⟩
    have identifier : firstWindow.id ≠ secondWindow.id := by
      intro equal
      apply canonical
      simpa [firstWindow, FormulaValidity.SupportedWindowOccurrence.shift,
        FormulaValidity.SupportedWindowOccurrence.ofSemantic, secondId,
        List.append_assoc] using equal
    have supportOverlap : ¬SupportDisjoint support.atomSupport
        firstWindow secondWindow := by
      simpa [Node.SupportDisjoint, firstWindow,
        FormulaValidity.SupportedWindowOccurrence.shift,
        FormulaValidity.SupportedWindowOccurrence.ofSemantic,
        FormulaValidity.SemanticOccurrence.shift,
        FormulaValidity.SemanticOccurrence.reroot, secondLeafEq] using
          notDisjoint
    have separated := node.shiftedSupportedInvariant_safe support.atomSupport computed sound
      first.skipped firstWindow secondWindow firstWindowMem secondWindowMem
      ⟨identifier, supportOverlap⟩
    apply separated
    constructor
    · simp only [firstWindow, FormulaValidity.SupportedWindowOccurrence.shift,
        FormulaValidity.SupportedWindowOccurrence.ofSemantic,
        FormulaValidity.SemanticOccurrence.reroot,
        FormulaValidity.SemanticOccurrence.shift, Stlsat.Interval.shift] at *
      omega
    · simp only [firstWindow, FormulaValidity.SupportedWindowOccurrence.shift,
        FormulaValidity.SupportedWindowOccurrence.ofSemantic,
        FormulaValidity.SemanticOccurrence.reroot,
        FormulaValidity.SemanticOccurrence.shift, Stlsat.Interval.shift] at *
      omega

/-- The already constructed ranked model and a new skipped requirement have
the same support-compatibility relation. -/
theorem ranked_supportCompatible_requirement
    (support : AtomicSupport semantics Var)
    (origin : node.SkippedOrigin size rank)
    (derivation : node.FullDerivationValid) (timely : node.Timely)
    (poised : node.Poised) (normal : node.InStrictNormalForm)
    {signal : Stlsat.Signal semantics}
    (holds : node.RankedHolds size (rank - 1) semantics signal)
    (computed : node.variableJumpSize? support.atomSupport = some size)
    (sound : node.VariableSoundSafe support.atomSupport) :
    (node.rankedRequirement normal holds).SupportCompatible support.atomSupport
      (origin.requirement derivation normal holds) := by
  intro live liveMem shifted shiftedMem instant liveLower liveUpper shiftedLower shiftedUpper
  change live ∈ node.liveSemanticLeaves at liveMem
  change shifted ∈ origin.semanticLeaves at shiftedMem
  unfold Node.liveSemanticLeaves at liveMem
  rcases List.mem_flatMap.mp liveMem with ⟨other, otherListMem, liveMem⟩
  have otherMem : other ∈ node.label := Finset.mem_toList.mp otherListMem
  rcases List.mem_map.mp liveMem with ⟨liveLeaf, liveLeafMem, rfl⟩
  rcases List.mem_map.mp shiftedMem with ⟨shiftedLeaf, shiftedLeafMem, rfl⟩
  simp only [FormulaValidity.SemanticOccurrence.reroot]
  by_cases otherTemporal : other.isTemporal = true
  · have formulaTemporal : other.formula.isTemporal = true :=
      (AnnotatedOccurrence.formula_isTemporal other).trans otherTemporal
    have liveSemanticMem : liveLeaf ∈
        FormulaValidity.semanticOccurrences other.formula := by
      rw [← FormulaValidity.semanticFrom_eq_semanticOccurrences_of_temporal
        other.formula formulaTemporal node.time]
      exact liveLeafMem
    by_cases canonical : other.id ++ liveLeaf.path =
        origin.source.id ++ [origin.edge] ++ shiftedLeaf.path
    · apply Or.inl
      refine ⟨canonical, ?_⟩
      change liveLeaf.leaf = shiftedLeaf.leaf
      rcases origin.semantic_source derivation timely shiftedLeaf shiftedLeafMem with
        ⟨sourceLeaf, sourceLeafMem, sourceId, sourceLeafEq⟩
      rw [← sourceLeafEq]
      apply derivation.2 other otherMem origin.source origin.sourceMem
        liveLeaf liveSemanticMem sourceLeaf sourceLeafMem
      rw [sourceId]
      exact canonical
    · apply Or.inr
      by_contra notDisjoint
      let invariantWindow :=
        (FormulaValidity.SupportedWindowOccurrence.ofSemantic
          (origin.source.id ++ [origin.edge]) shiftedLeaf).shift node.time
      have invariantWindowMem : invariantWindow ∈ node.supportedInvariantWindows :=
        node.supportedInvariantWindow_mem origin.source origin.sourceMem origin.edge
          origin.invariant origin.shape shiftedLeaf shiftedLeafMem
      rcases node.semantic_covered_by_supportedIndependentAncestor derivation.1.1.1
          derivation.2 other otherMem otherTemporal liveLeaf liveSemanticMem with
        ⟨liveWindow, liveWindowMem, liveId, liveLeafEq, coveringLower, coveringUpper⟩
      have identifier : invariantWindow.id ≠ liveWindow.id := by
        intro equal
        apply canonical
        have : origin.source.id ++ [origin.edge] ++ shiftedLeaf.path =
            other.id ++ liveLeaf.path := by
          simpa [invariantWindow, FormulaValidity.SupportedWindowOccurrence.shift,
            FormulaValidity.SupportedWindowOccurrence.ofSemantic, liveId,
            List.append_assoc] using equal
        exact this.symm
      have supportOverlap : ¬SupportDisjoint support.atomSupport
          invariantWindow liveWindow := by
        intro disjoint
        apply notDisjoint
        simpa [Node.SupportDisjoint, invariantWindow,
          FormulaValidity.SupportedWindowOccurrence.shift,
          FormulaValidity.SupportedWindowOccurrence.ofSemantic,
          FormulaValidity.SemanticOccurrence.shift,
          FormulaValidity.SemanticOccurrence.reroot, liveLeafEq] using
            disjoint.symm
      have separated := node.shiftedSupportedInvariant_safe support.atomSupport computed sound
        origin.skipped invariantWindow liveWindow invariantWindowMem liveWindowMem
        ⟨identifier, supportOverlap⟩
      apply separated
      constructor
      · simp only [invariantWindow, FormulaValidity.SupportedWindowOccurrence.shift,
          FormulaValidity.SupportedWindowOccurrence.ofSemantic,
          FormulaValidity.SemanticOccurrence.reroot,
          FormulaValidity.SemanticOccurrence.shift,
          Stlsat.Interval.shift] at *
        omega
      · simp only [invariantWindow, FormulaValidity.SupportedWindowOccurrence.shift,
          FormulaValidity.SupportedWindowOccurrence.ofSemantic,
          FormulaValidity.SemanticOccurrence.reroot,
          FormulaValidity.SemanticOccurrence.shift,
          Stlsat.Interval.shift] at *
        omega
  · have notTemporal : other.isTemporal = false :=
      Bool.eq_false_of_not_eq_true otherTemporal
    have atCurrent := node.semanticFrom_window_eq_time_of_nonTemporal poised normal
      other otherMem notTemporal liveLeaf liveLeafMem
    rcases atCurrent with ⟨liveWindowLower, liveWindowUpper⟩
    have positive := origin.positive
    exfalso
    simp only [FormulaValidity.SemanticOccurrence.reroot,
      FormulaValidity.SemanticOccurrence.shift, Stlsat.Interval.shift] at *
    omega

end SkippedOrigin

/-- One variable-aware splicing round adds every marked obligation at a fixed
positive structural rank. -/
theorem exists_variableRankedHolds_of_previous
    {node : Node Atom} {size rank : Nat}
    {semantics : Stlsat.AtomicSemantics Atom}
    (support : AtomicSupport semantics Var)
    (_rankPositive : 0 < rank)
    (derivation : node.FullDerivationValid)
    (poised : node.Poised) (timely : node.Timely)
    (normal : node.InStrictNormalForm)
    (computed : node.variableJumpSize? support.atomSupport = some size)
    (sound : node.VariableSoundSafe support.atomSupport)
    {signal : Stlsat.Signal semantics}
    (previous : node.RankedHolds size (rank - 1) semantics signal) :
    ∃ next : Stlsat.Signal semantics,
      node.RankedHolds size rank semantics next ∧
      ∀ origin : node.SkippedOrigin size rank,
        origin.invariant.Satisfies semantics next (node.time + origin.offset) := by
  classical
  let requirement : Unit ⊕ node.SkippedOrigin size rank →
      FormulaValidity.SemanticRequirement semantics
    | .inl _ => node.rankedRequirement normal previous
    | .inr origin => origin.requirement derivation normal previous
  have compatible : ∀ first second,
      (requirement first).signal = (requirement second).signal ∨
        (requirement first).SupportCompatible support.atomSupport (requirement second) := by
    intro first second
    cases first with
    | inl _ =>
        cases second with
        | inl _ => exact Or.inl rfl
        | inr origin =>
            exact Or.inr (origin.ranked_supportCompatible_requirement support derivation
              timely poised normal previous computed sound)
    | inr firstOrigin =>
        cases second with
        | inl _ =>
            exact Or.inr (firstOrigin.ranked_supportCompatible_requirement support derivation
              timely poised normal previous computed sound).symm
        | inr secondOrigin =>
            exact Or.inr (firstOrigin.requirements_supportCompatible support secondOrigin
              derivation timely normal previous computed sound)
  rcases FormulaValidity.exists_signal_accepting_supportCompatible_family
      support (Index := Unit ⊕ node.SkippedOrigin size rank) requirement compatible with
    ⟨next, accepts⟩
  have old : node.RankedHolds size (rank - 1) semantics next := by
    have accepted := accepts (Sum.inl ())
    change node.RankedHolds size (rank - 1) semantics next at accepted
    exact accepted
  have skipped (origin : node.SkippedOrigin size rank) :
      origin.invariant.Satisfies semantics next (node.time + origin.offset) := by
    have accepted := accepts (Sum.inr origin)
    change origin.invariant.Satisfies semantics next
      (node.time + origin.offset) at accepted
    exact accepted
  refine ⟨next, ⟨old.1, ?_⟩, skipped⟩
  intro occurrence present marked bounded
  by_cases already : formulaRank occurrence.formula ≤ rank - 1
  · exact old.2 occurrence present marked already
  have positiveSize := node.variableJumpSize_pos support.atomSupport computed
  have later := old.1.2 occurrence present (by
    cases occurrence with
    | mk id payload parent =>
        cases payload <;> simp_all [AnnotatedOccurrence.isTemporal,
          Stlsat.Occurrence.isTemporal])
  have invariantAt (edge : Nat) (invariant : Stlsat.Formula Atom)
      (shape : occurrence.postponedInvariant? = some (edge, invariant))
      (instant : Nat) (after : node.time + 1 ≤ instant)
      (before : instant < node.time + size) :
      invariant.Satisfies semantics next instant := by
    let origin : node.SkippedOrigin size rank := {
      source := occurrence
      sourceMem := present
      edge := edge
      invariant := invariant
      shape := shape
      offset := instant - node.time
      positive := by omega
      skipped := by omega
      bounded := bounded }
    have supplied := skipped origin
    have instantEq : node.time + origin.offset = instant := by
      simp only [origin]
      omega
    simpa [instantEq] using supplied
  cases occurrence with
  | mk id payload parent =>
      cases payload with
      | unmarked formula => simp at marked
      | markedEventually interval body => simp at marked
      | markedAlways interval body =>
          apply always_satisfiedFrom_earlier
            (start := node.time + 1) (finish := node.time + size) (by omega)
          · intro instant after before
            exact invariantAt 0 body rfl instant after before
          · exact later
      | markedStrictUntil interval invariant target =>
          apply strictUntil_satisfiedFrom_earlier
            (start := node.time + 1) (finish := node.time + size) (by omega)
          · intro instant after before
            exact invariantAt 0 invariant rfl instant after before
          · exact later
      | markedStrictRelease interval target invariant =>
          apply strictRelease_satisfiedFrom_earlier
            (start := node.time + 1) (finish := node.time + size) (by omega)
          · intro instant after before
            exact invariantAt 1 invariant rfl instant after before
          · exact later

/-- Iterate variable-aware rank promotion to any requested structural rank. -/
theorem exists_variableRankedHolds {node : Node Atom} {size : Nat}
    {semantics : Stlsat.AtomicSemantics Atom}
    (support : AtomicSupport semantics Var)
    (derivation : node.FullDerivationValid)
    (poised : node.Poised) (timely : node.Timely)
    (normal : node.InStrictNormalForm)
    (computed : node.variableJumpSize? support.atomSupport = some size)
    (sound : node.VariableSoundSafe support.atomSupport)
    {baseSignal : Stlsat.Signal semantics}
    (base : node.BaseHolds size semantics baseSignal) (rank : Nat) :
    ∃ signal : Stlsat.Signal semantics, node.RankedHolds size rank semantics signal := by
  induction rank with
  | zero => exact ⟨baseSignal, rankedHolds_zero_of_base base⟩
  | succ rank ih =>
      rcases ih with ⟨signal, holds⟩
      rcases node.exists_variableRankedHolds_of_previous support
          (rank := rank + 1) (by omega) derivation poised timely normal computed sound
          (by simpa using holds) with ⟨next, nextHolds, skipped⟩
      exact ⟨next, nextHolds⟩

/-- The last variable-aware promotion round supplies every skipped invariant. -/
theorem exists_fullVariableRankedHolds_with_skipped
    {node : Node Atom} {size : Nat}
    {semantics : Stlsat.AtomicSemantics Atom}
    (support : AtomicSupport semantics Var)
    (derivation : node.FullDerivationValid)
    (poised : node.Poised) (timely : node.Timely)
    (normal : node.InStrictNormalForm)
    (computed : node.variableJumpSize? support.atomSupport = some size)
    (sound : node.VariableSoundSafe support.atomSupport)
    {baseSignal : Stlsat.Signal semantics}
    (base : node.BaseHolds size semantics baseSignal) :
    ∃ signal : Stlsat.Signal semantics,
      node.RankedHolds size (node.maxFormulaRank + 1) semantics signal ∧
      ∀ origin : node.SkippedOrigin size (node.maxFormulaRank + 1),
        origin.invariant.Satisfies semantics signal (node.time + origin.offset) := by
  rcases node.exists_variableRankedHolds support derivation poised timely normal computed
      sound base node.maxFormulaRank with ⟨signal, holds⟩
  simpa using node.exists_variableRankedHolds_of_previous support
    (rank := node.maxFormulaRank + 1) (by omega) derivation poised timely normal
    computed sound (by simpa using holds)

end Node
end Stlsat.Tableau
