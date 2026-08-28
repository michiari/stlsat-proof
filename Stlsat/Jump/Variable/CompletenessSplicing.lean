/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.Variable.Soundness
import Stlsat.Jump.CompletenessSplicing

/-! # Target splicing for variable-aware JUMP completeness -/

namespace Stlsat.Tableau

universe u w

namespace Node

variable {Atom : Type u} [DecidableEq Atom]
  {Var : Type w} [DecidableEq Var]
  {node : Node Atom} {semantics : Stlsat.AtomicSemantics Atom}

namespace TargetOrigin

/-- A witnessed postponed target and the current live model either repeat one
canonical signed leaf or constrain disjoint variable supports. -/
theorem requirement_supportCompatible_model
    (support : AtomicSupport semantics Var)
    (origin : node.TargetOrigin semantics)
    (derivation : node.FullDerivationValid) (timely : node.Timely)
    (poised : node.Poised) (normal : node.InStrictNormalForm)
    (complete : node.VariableCompleteSafe support.atomSupport)
    (model : node.Model semantics) :
    (origin.requirement normal).SupportCompatible support.atomSupport
      (node.modelRequirement normal model) := by
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
  · apply Or.inl
    refine ⟨canonical, ?_⟩
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
  · apply Or.inr
    by_contra notDisjoint
    let targetWindow : FormulaValidity.SupportedWindowOccurrence Atom :=
      (FormulaValidity.SupportedWindowOccurrence.ofSemantic
        (origin.source.id ++ [origin.edge]) targetLeaf).shift node.time
    have targetWindowMem : targetWindow ∈ node.supportedTargetWindows :=
      node.supportedTargetWindow_mem origin.source origin.sourceMem origin.edge
        origin.target origin.shape targetLeaf targetLeafMem
    rcases node.demandingLeaf_covered_by_conflictWindows derivation.1.1.1 poised
        normal model other otherMem liveLeaf liveLeafMem liveLeafDemanding with
      ⟨baseConflict, baseConflictMem, baseConflictId, baseLower, baseUpper⟩
    rcases FormulaValidity.semanticFrom_source other.formula node.time liveLeaf
        liveLeafMem with
      ⟨liveSourceLeaf, liveSourceMem, liveSourcePath, liveSourceEq⟩
    have sourceConflictId : baseConflict.id = other.id ++ liveSourceLeaf.path := by
      rw [baseConflictId, liveSourcePath]
    rcases node.semanticSource_covered_by_supportedConflict derivation.2 other otherMem
        liveSourceLeaf liveSourceMem baseConflict baseConflictMem sourceConflictId with
      ⟨conflictWindow, conflictMem, conflictErase, conflictLeafEq⟩
    have conflictLiveLeaf : conflictWindow.leaf = liveLeaf.leaf :=
      conflictLeafEq.trans liveSourceEq
    have identifier : targetWindow.id ≠ conflictWindow.id := by
      intro equal
      apply canonical
      have targetConflict : origin.source.id ++ [origin.edge] ++ targetLeaf.path =
          conflictWindow.id := by
        simpa [targetWindow, FormulaValidity.SupportedWindowOccurrence.ofSemantic,
          FormulaValidity.SupportedWindowOccurrence.shift] using equal
      have conflictBase : conflictWindow.id = baseConflict.id :=
        congrArg WindowOccurrence.id conflictErase
      exact targetConflict.trans (conflictBase.trans baseConflictId)
    have supportOverlap : ¬SupportDisjoint support.atomSupport
        targetWindow conflictWindow := by
      simpa [SupportDisjoint, targetWindow,
        FormulaValidity.SupportedWindowOccurrence.ofSemantic,
        FormulaValidity.SupportedWindowOccurrence.shift,
        FormulaValidity.SemanticOccurrence.shift,
        FormulaValidity.SemanticOccurrence.reroot, conflictLiveLeaf] using notDisjoint
    have separated := complete targetWindow targetWindowMem conflictWindow conflictMem
      ⟨identifier, supportOverlap⟩
    apply separated
    have conflictWindowEq : conflictWindow.window = baseConflict.window :=
      congrArg WindowOccurrence.window conflictErase
    constructor
    · simp only [targetWindow, FormulaValidity.SupportedWindowOccurrence.ofSemantic,
        FormulaValidity.SupportedWindowOccurrence.shift,
        FormulaValidity.SemanticOccurrence.shift,
        FormulaValidity.SemanticOccurrence.reroot, Stlsat.Interval.shift] at *
      rw [conflictWindowEq]
      omega
    · simp only [targetWindow, FormulaValidity.SupportedWindowOccurrence.ofSemantic,
        FormulaValidity.SupportedWindowOccurrence.shift,
        FormulaValidity.SemanticOccurrence.shift,
        FormulaValidity.SemanticOccurrence.reroot, Stlsat.Interval.shift] at *
      rw [conflictWindowEq]
      omega

/-- Variable support amalgamation yields one signal satisfying the current
node and the witnessed intermediate target. -/
theorem exists_signal_satisfying_node_and_target_variable
    (support : AtomicSupport semantics Var)
    (origin : node.TargetOrigin semantics)
    (derivation : node.FullDerivationValid) (timely : node.Timely)
    (poised : node.Poised) (normal : node.InStrictNormalForm)
    (complete : node.VariableCompleteSafe support.atomSupport)
    (model : node.Model semantics) :
    ∃ signal : Stlsat.Signal semantics,
      node.SatisfiedBy semantics signal ∧
        origin.target.Satisfies semantics signal node.time := by
  classical
  let requirement : ULift.{u} Bool →
      FormulaValidity.SemanticRequirement semantics
    | ⟨false⟩ => origin.requirement normal
    | ⟨true⟩ => node.modelRequirement normal model
  have cross := origin.requirement_supportCompatible_model support derivation timely poised
    normal complete model
  have compatible : ∀ first second,
      (requirement first).signal = (requirement second).signal ∨
        (requirement first).SupportCompatible support.atomSupport (requirement second) := by
    intro first second
    rcases first with ⟨first⟩
    rcases second with ⟨second⟩
    cases first <;> cases second
    · exact Or.inl rfl
    · exact Or.inr cross
    · exact Or.inr cross.symm
    · exact Or.inl rfl
  rcases FormulaValidity.exists_signal_accepting_supportCompatible_family
      support requirement compatible with ⟨signal, accepts⟩
  refine ⟨signal, accepts (ULift.up true), accepts (ULift.up false)⟩

theorem exists_variableTargetEscape
    (support : AtomicSupport semantics Var)
    (origin : node.TargetOrigin semantics)
    (derivation : node.FullDerivationValid) (timely : node.Timely)
    (poised : node.Poised) (normal : node.InStrictNormalForm)
    (complete : node.VariableCompleteSafe support.atomSupport)
    (model : node.Model semantics) : Nonempty (node.TargetEscape semantics) := by
  rcases origin.exists_signal_satisfying_node_and_target_variable support derivation timely
      poised normal complete model with ⟨signal, nodeHolds, targetHolds⟩
  exact ⟨⟨origin.source, origin.sourceMem, origin.edge, origin.target,
    origin.shape, signal, nodeHolds, targetHolds⟩⟩

end TargetOrigin

/-- Local completeness alternative for a variable-aware JUMP. -/
theorem hasModel_variableJump_or_targetEscape
    (support : AtomicSupport semantics Var)
    (node : Node Atom) {size : Nat}
    (computed : node.jumpSize? = some size)
    (derivation : node.FullDerivationValid) (timely : node.Timely)
    (poised : node.Poised) (normal : node.InStrictNormalForm)
    (complete : node.VariableCompleteSafe support.atomSupport)
    (model : node.Model semantics) :
    (node.jump size).HasModel semantics ∨ Nonempty (node.TargetEscape semantics) := by
  rcases node.hasModel_jump_or_targetOrigin computed poised timely model with
    childModel | origin
  · exact Or.inl childModel
  · rcases origin with ⟨origin⟩
    exact Or.inr (origin.exists_variableTargetEscape support derivation timely poised normal
      complete model)

end Node
end Stlsat.Tableau
