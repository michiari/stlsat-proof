/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.RankedConstruction
import Stlsat.Jump.AncestorCoverage

/-! # Rank-stratified splicing across a JUMP -/

namespace Stlsat.Jump
universe u

namespace Node

variable {Atom : Type u} [DecidableEq Atom]

omit [DecidableEq Atom] in
theorem postponedInvariant_rank_lt (source : AnnotatedOccurrence Atom)
    {edge : Nat} {invariant : Stlsat.Formula Atom}
    (shape : source.postponedInvariant? = some (edge, invariant)) :
    formulaRank invariant < formulaRank source.formula := by
  cases source with
  | mk id payload parent =>
      cases payload <;> simp_all [AnnotatedOccurrence.postponedInvariant?,
        AnnotatedOccurrence.formula, formulaRank] <;> omega

omit [DecidableEq Atom] in
theorem postponedInvariant_normal (source : AnnotatedOccurrence Atom)
    {edge : Nat} {invariant : Stlsat.Formula Atom}
    (sourceNormal : source.InStrictNormalForm)
    (shape : source.postponedInvariant? = some (edge, invariant)) :
    invariant.InStrictNormalForm := by
  cases source with
  | mk id payload parent =>
      cases payload <;> simp_all [AnnotatedOccurrence.postponedInvariant?,
        AnnotatedOccurrence.InStrictNormalForm, Stlsat.Occurrence.InStrictNormalForm,
        Stlsat.Formula.InStrictNormalForm]

omit [DecidableEq Atom] in
/-- A signed leaf of an emitted invariant embeds into the signed syntax tree
of the marked source occurrence. -/
theorem postponedInvariant_semantic_source
    (source : AnnotatedOccurrence Atom) {edge : Nat}
    {invariant : Stlsat.Formula Atom}
    (shape : source.postponedInvariant? = some (edge, invariant))
    (active : match source.interval? with
      | some interval => interval.lower < interval.upper
      | none => False)
    (leaf : FormulaValidity.SemanticOccurrence Atom)
    (leafMem : leaf ∈ FormulaValidity.semanticOccurrences invariant) :
    ∃ sourceLeaf ∈ FormulaValidity.semanticOccurrences source.formula,
      source.id ++ sourceLeaf.path = source.id ++ [edge] ++ leaf.path ∧
        sourceLeaf.leaf = leaf.leaf := by
  cases source with
  | mk id payload parent =>
      cases payload with
      | unmarked formula => simp [AnnotatedOccurrence.postponedInvariant?] at shape
      | markedEventually interval body =>
          simp [AnnotatedOccurrence.postponedInvariant?] at shape
      | markedAlways interval body =>
          simp only [AnnotatedOccurrence.postponedInvariant?, Option.some.injEq,
            Prod.mk.injEq] at shape
          rcases shape with ⟨rfl, rfl⟩
          refine ⟨(leaf.through interval).prefixPath 0, ?_, ?_, rfl⟩
          · exact List.mem_map.mpr ⟨leaf, leafMem, rfl⟩
          · simp [FormulaValidity.SemanticOccurrence.prefixPath,
              FormulaValidity.SemanticOccurrence.through, List.append_assoc]
      | markedStrictUntil interval left right =>
          simp only [AnnotatedOccurrence.postponedInvariant?, Option.some.injEq,
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
      | markedStrictRelease interval target invariant =>
          simp only [AnnotatedOccurrence.postponedInvariant?, Option.some.injEq,
            Prod.mk.injEq] at shape
          rcases shape with ⟨rfl, rfl⟩
          refine ⟨(leaf.through interval).prefixPath 1, ?_, ?_, rfl⟩
          · simp only [AnnotatedOccurrence.formula,
              FormulaValidity.semanticOccurrences, List.mem_append]
            exact Or.inr (List.mem_map.mpr ⟨leaf, leafMem, rfl⟩)
          · simp [FormulaValidity.SemanticOccurrence.prefixPath,
              FormulaValidity.SemanticOccurrence.through, List.append_assoc]

/-- Data naming one invariant instance at a strictly skipped instant. -/
structure SkippedOrigin (node : Node Atom) (size rank : Nat) where
  source : AnnotatedOccurrence Atom
  sourceMem : source ∈ node.label
  edge : Nat
  invariant : Stlsat.Formula Atom
  shape : source.postponedInvariant? = some (edge, invariant)
  offset : Nat
  positive : 0 < offset
  skipped : offset < size
  bounded : formulaRank source.formula ≤ rank

/-- All signed leaves needed to preserve the already constructed ranked
obligations.  Canonical occurrence identifiers are stored directly in paths. -/
noncomputable def liveSemanticLeaves (node : Node Atom) :
    List (FormulaValidity.SemanticOccurrence Atom) := by
  classical
  exact node.label.toList.flatMap fun occurrence =>
    (FormulaValidity.semanticFrom node.time occurrence.formula).map
      (FormulaValidity.SemanticOccurrence.reroot occurrence.id)

omit [DecidableEq Atom] in
theorem reroot_mem_liveSemanticLeaves (node : Node Atom)
    (occurrence : AnnotatedOccurrence Atom) (present : occurrence ∈ node.label)
    (leaf : FormulaValidity.SemanticOccurrence Atom)
    (leafMem : leaf ∈ FormulaValidity.semanticFrom node.time occurrence.formula) :
    leaf.reroot occurrence.id ∈ node.liveSemanticLeaves := by
  classical
  unfold liveSemanticLeaves
  apply List.mem_flatMap.mpr
  exact ⟨occurrence, Finset.mem_toList.mpr present,
    List.mem_map.mpr ⟨leaf, leafMem, rfl⟩⟩

/-- At a poised strict-normal node, every non-temporal live occurrence is a
literal (or truth/falsity), hence its absolute leaves live exactly at the
current instant. -/
theorem semanticFrom_window_eq_time_of_nonTemporal (node : Node Atom)
    (poised : node.Poised) (normal : node.InStrictNormalForm)
    (occurrence : AnnotatedOccurrence Atom) (present : occurrence ∈ node.label)
    (notTemporal : occurrence.isTemporal = false)
    (leaf : FormulaValidity.SemanticOccurrence Atom)
    (leafMem : leaf ∈ FormulaValidity.semanticFrom node.time occurrence.formula) :
    leaf.window.lower = node.time ∧ leaf.window.upper = node.time := by
  have occurrenceNormal := (normal_iff node).mp normal occurrence present
  cases occurrence with
  | mk id payload parent =>
      cases payload with
      | unmarked formula =>
          cases formula with
          | truth =>
              simp only [AnnotatedOccurrence.formula, FormulaValidity.semanticFrom,
                List.mem_singleton] at leafMem
              subst leaf
              simp
          | atom atom =>
              simp only [AnnotatedOccurrence.formula, FormulaValidity.semanticFrom,
                List.mem_singleton] at leafMem
              subst leaf
              simp
          | neg body =>
              cases body with
              | truth =>
                  rcases List.mem_map.mp leafMem with ⟨child, childMem, rfl⟩
                  simp only [FormulaValidity.semanticFrom, List.mem_singleton] at childMem
                  subst child
                  simp [FormulaValidity.SemanticOccurrence.negate,
                    FormulaValidity.SemanticOccurrence.prefixPath]
              | atom atom =>
                  rcases List.mem_map.mp leafMem with ⟨child, childMem, rfl⟩
                  simp only [FormulaValidity.semanticFrom, List.mem_singleton] at childMem
                  subst child
                  simp [FormulaValidity.SemanticOccurrence.negate,
                    FormulaValidity.SemanticOccurrence.prefixPath]
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
              | strictUntil interval left right =>
                  simp [AnnotatedOccurrence.InStrictNormalForm,
                    Stlsat.Occurrence.InStrictNormalForm,
                    Stlsat.Formula.InStrictNormalForm] at occurrenceNormal
              | strictRelease interval left right =>
                  simp [AnnotatedOccurrence.InStrictNormalForm,
                    Stlsat.Occurrence.InStrictNormalForm,
                    Stlsat.Formula.InStrictNormalForm] at occurrenceNormal
          | and left right =>
              exfalso
              exact poised ⟨_, Expansion.conjunction _ left right rfl present⟩
          | or left right =>
              exfalso
              exact poised ⟨_, Expansion.disjunction _ left right rfl present⟩
          | eventually interval body =>
              simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal,
                Stlsat.Formula.isTemporal] at notTemporal
          | always interval body =>
              simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal,
                Stlsat.Formula.isTemporal] at notTemporal
          | strictUntil interval invariant target =>
              simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal,
                Stlsat.Formula.isTemporal] at notTemporal
          | strictRelease interval target invariant =>
              simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal,
                Stlsat.Formula.isTemporal] at notTemporal
      | markedEventually interval body =>
          simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal] at notTemporal
      | markedAlways interval body =>
          simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal] at notTemporal
      | markedStrictUntil interval invariant target =>
          simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal] at notTemporal
      | markedStrictRelease interval target invariant =>
          simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal] at notTemporal

/-- Package all obligations already available at a rank as one heterogeneous
semantic requirement. -/
noncomputable def rankedRequirement {node : Node Atom} {size rank : Nat}
    {semantics : Stlsat.AtomicSemantics Atom}
    {signal : Stlsat.Signal semantics}
    (normal : node.InStrictNormalForm)
    (holds : node.RankedHolds size rank semantics signal) :
    FormulaValidity.SemanticRequirement semantics where
  root := []
  leaves := node.liveSemanticLeaves
  signal := signal
  Accepts := node.RankedHolds size rank semantics
  holds := holds
  preserves := by
    intro right preserves
    have current (occurrence : AnnotatedOccurrence Atom) (present : occurrence ∈ node.label)
        (sourceHolds : occurrence.formula.SatisfiesFrom semantics signal node.time) :
        occurrence.formula.SatisfiesFrom semantics right node.time := by
      have formulaNormal : occurrence.formula.InStrictNormalForm := by
        have occurrenceNormal := (normal_iff node).mp normal occurrence present
        cases occurrence with
        | mk id payload parent =>
            cases payload <;> simpa [AnnotatedOccurrence.formula,
              AnnotatedOccurrence.InStrictNormalForm,
              Stlsat.Occurrence.InStrictNormalForm] using occurrenceNormal
      apply FormulaValidity.satisfiesFrom_of_absoluteAtomicallyPreserves
        occurrence.formula formulaNormal semantics sourceHolds
      intro leaf leafMem instant lower upper leafHolds
      apply preserves (leaf.reroot occurrence.id)
      · exact node.reroot_mem_liveSemanticLeaves occurrence present leaf leafMem
      · simpa [FormulaValidity.SemanticOccurrence.reroot] using lower
      · simpa [FormulaValidity.SemanticOccurrence.reroot] using upper
      · simpa [FormulaValidity.SemanticOccurrence.reroot] using leafHolds
    have temporal (occurrence : AnnotatedOccurrence Atom)
        (present : occurrence ∈ node.label) (temporal : occurrence.isTemporal = true)
        (time : Nat) (sourceHolds : occurrence.formula.SatisfiesFrom semantics signal time) :
        occurrence.formula.SatisfiesFrom semantics right time := by
      have formulaNormal : occurrence.formula.InStrictNormalForm := by
        have occurrenceNormal := (normal_iff node).mp normal occurrence present
        cases occurrence with
        | mk id payload parent =>
            cases payload <;> simpa [AnnotatedOccurrence.formula,
              AnnotatedOccurrence.InStrictNormalForm,
              Stlsat.Occurrence.InStrictNormalForm] using occurrenceNormal
      apply FormulaValidity.satisfiesFrom_of_absoluteAtomicallyPreserves
        occurrence.formula formulaNormal semantics sourceHolds
      intro leaf leafMem instant lower upper leafHolds
      have formulaTemporal : occurrence.formula.isTemporal = true :=
        (AnnotatedOccurrence.formula_isTemporal occurrence).trans temporal
      have storedMem : leaf ∈
          FormulaValidity.semanticFrom node.time occurrence.formula := by
        rw [FormulaValidity.semanticFrom_eq_of_temporal occurrence.formula formulaTemporal
          node.time time]
        exact leafMem
      apply preserves (leaf.reroot occurrence.id)
      · exact node.reroot_mem_liveSemanticLeaves occurrence present leaf storedMem
      · simpa [FormulaValidity.SemanticOccurrence.reroot] using lower
      · simpa [FormulaValidity.SemanticOccurrence.reroot] using upper
      · simpa [FormulaValidity.SemanticOccurrence.reroot] using leafHolds
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro occurrence present
      have old := holds.1.1 occurrence present
      cases occurrence with
      | mk id payload parent =>
          cases payload with
          | unmarked formula => exact current _ present old
          | markedEventually interval body =>
              have transported := temporal _ present (by
                simp [AnnotatedOccurrence.isTemporal, Stlsat.Occurrence.isTemporal])
                (node.time + 1) (by
                  simpa [AnnotatedOccurrence.SatisfiedBy,
                    Stlsat.Occurrence.SatisfiedBy, AnnotatedOccurrence.formula] using old)
              simpa [AnnotatedOccurrence.SatisfiedBy,
                Stlsat.Occurrence.SatisfiedBy, AnnotatedOccurrence.formula] using transported
          | markedAlways interval body => trivial
          | markedStrictUntil interval invariant target => trivial
          | markedStrictRelease interval target invariant => trivial
    · intro occurrence present isTemporal
      have old := holds.1.2 occurrence present isTemporal
      have oldFormula : occurrence.formula.SatisfiesFrom semantics signal
          (node.time + size) := by
        cases occurrence with
        | mk id payload parent =>
            cases payload <;> exact old
      have transported := temporal occurrence present isTemporal (node.time + size) oldFormula
      cases occurrence with
      | mk id payload parent =>
          cases payload <;> exact transported
    · intro occurrence present marked bounded
      have old := holds.2 occurrence present marked bounded
      have transported := temporal occurrence present (by
        cases occurrence with
        | mk id payload parent =>
            cases payload <;> simp_all [AnnotatedOccurrence.isTemporal,
              Stlsat.Occurrence.isTemporal]) (node.time + 1) (by
                cases occurrence with
                | mk id payload parent =>
                    cases payload <;> simp_all [AnnotatedOccurrence.SatisfiedBy,
                      Stlsat.Occurrence.SatisfiedBy, AnnotatedOccurrence.formula])
      cases occurrence with
      | mk id payload parent =>
          cases payload <;> simp_all [AnnotatedOccurrence.SatisfiedBy,
            Stlsat.Occurrence.SatisfiedBy, AnnotatedOccurrence.formula]

namespace SkippedOrigin

variable {node : Node Atom} {size rank : Nat}
  {semantics : Stlsat.AtomicSemantics Atom}

theorem invariant_normal (origin : node.SkippedOrigin size rank)
    (normal : node.InStrictNormalForm) : origin.invariant.InStrictNormalForm := by
  exact postponedInvariant_normal origin.source
    ((normal_iff node).mp normal origin.source origin.sourceMem) origin.shape

theorem invariant_rank_le (origin : node.SkippedOrigin size rank) :
    formulaRank origin.invariant < rank :=
  (postponedInvariant_rank_lt origin.source origin.shape).trans_le origin.bounded

theorem semantic_source (origin : node.SkippedOrigin size rank)
    (derivation : node.FullDerivationValid) (timely : node.Timely)
    (leaf : FormulaValidity.SemanticOccurrence Atom)
    (leafMem : leaf ∈ FormulaValidity.semanticOccurrences origin.invariant) :
    ∃ sourceLeaf ∈ FormulaValidity.semanticOccurrences origin.source.formula,
      origin.source.id ++ sourceLeaf.path =
        origin.source.id ++ [origin.edge] ++ leaf.path ∧
      sourceLeaf.leaf = leaf.leaf := by
  have active := node.postponedInvariant_active derivation.1.1 timely
    origin.source origin.sourceMem origin.shape
  apply postponedInvariant_semantic_source origin.source origin.shape
  · cases intervalEq : origin.source.interval? with
    | none => simp [intervalEq] at active
    | some interval =>
        rw [intervalEq] at active
        simp only
        omega
  · exact leafMem

noncomputable def semanticLeaves (origin : node.SkippedOrigin size rank) :
    List (FormulaValidity.SemanticOccurrence Atom) :=
  (FormulaValidity.semanticOccurrences origin.invariant).map fun leaf =>
    (leaf.shift (node.time + origin.offset)).reroot
      (origin.source.id ++ [origin.edge])

/-- The recorded expansion frontier supplies a model of the invariant at the
source instant; translating that model supplies the skipped copy. -/
noncomputable def requirement (origin : node.SkippedOrigin size rank)
    (derivation : node.FullDerivationValid) (normal : node.InStrictNormalForm)
    {signal : Stlsat.Signal semantics}
    (holds : node.RankedHolds size (rank - 1) semantics signal) :
    FormulaValidity.SemanticRequirement semantics := by
  have bounded : formulaRank origin.invariant ≤ rank - 1 := by
    have := origin.invariant_rank_le
    omega
  have frontier := derivation.1.2 origin.source origin.sourceMem origin.edge
    origin.invariant origin.shape
  have expandedHolds := frontier.satisfiedBy_of_ranked holds (by
    simpa [rank_temporalExpansion] using bounded)
  have invariantHolds : origin.invariant.Satisfies semantics signal node.time :=
    (Stlsat.Formula.satisfiesFrom_temporalExpansion origin.invariant semantics signal
      node.time).mp expandedHolds
  have shiftedHolds : origin.invariant.Satisfies semantics
      (shiftSignal signal origin.offset) (node.time + origin.offset) :=
    satisfies_shift origin.invariant semantics signal node.time origin.offset invariantHolds
  exact {
    root := []
    leaves := origin.semanticLeaves
    signal := shiftSignal signal origin.offset
    Accepts := fun right =>
      origin.invariant.Satisfies semantics right (node.time + origin.offset)
    holds := shiftedHolds
    preserves := by
      intro right preserves
      apply FormulaValidity.satisfies_of_atomicallyPreserves origin.invariant
        (origin.invariant_normal normal) semantics shiftedHolds
      intro leaf leafMem instant supported leafHolds
      apply preserves
        ((leaf.shift (node.time + origin.offset)).reroot
          (origin.source.id ++ [origin.edge]))
      · exact List.mem_map.mpr ⟨leaf, leafMem, rfl⟩
      · rcases supported with ⟨lower, upper⟩
        simpa [FormulaValidity.SemanticOccurrence.reroot,
          FormulaValidity.SemanticOccurrence.shift, Stlsat.Interval.shift,
          Nat.add_comm] using lower
      · rcases supported with ⟨lower, upper⟩
        simpa [FormulaValidity.SemanticOccurrence.reroot,
          FormulaValidity.SemanticOccurrence.shift, Stlsat.Interval.shift,
          Nat.add_comm] using upper
      · simpa [FormulaValidity.SemanticOccurrence.reroot,
          FormulaValidity.SemanticOccurrence.shift] using leafHolds }

/-- Two skipped copies are compatible: equal canonical paths denote the same
signed leaf, while distinct paths are separated by `SoundSafe`. -/
theorem requirements_compatible (first second : node.SkippedOrigin size rank)
    (derivation : node.FullDerivationValid) (timely : node.Timely)
    (normal : node.InStrictNormalForm)
    {signal : Stlsat.Signal semantics}
    (holds : node.RankedHolds size (rank - 1) semantics signal)
    (computed : node.jumpSize? = some size) (sound : node.SoundSafe) :
    (first.requirement derivation normal holds).Compatible
      (second.requirement derivation normal holds) := by
  intro left leftMem right rightMem instant leftLower leftUpper rightLower rightUpper
  change left ∈ first.semanticLeaves at leftMem
  change right ∈ second.semanticLeaves at rightMem
  rcases List.mem_map.mp leftMem with ⟨leftLeaf, leftLeafMem, rfl⟩
  rcases List.mem_map.mp rightMem with ⟨rightLeaf, rightLeafMem, rfl⟩
  simp only [FormulaValidity.SemanticRequirement.root,
    FormulaValidity.SemanticOccurrence.reroot, List.nil_append]
  by_cases canonical : first.source.id ++ [first.edge] ++ leftLeaf.path =
      second.source.id ++ [second.edge] ++ rightLeaf.path
  · refine ⟨canonical, ?_⟩
    change leftLeaf.leaf = rightLeaf.leaf
    rcases first.semantic_source derivation timely leftLeaf leftLeafMem with
      ⟨firstSourceLeaf, firstSourceMem, firstId, firstLeaf⟩
    rcases second.semantic_source derivation timely rightLeaf rightLeafMem with
      ⟨secondSourceLeaf, secondSourceMem, secondId, secondLeaf⟩
    rw [← firstLeaf, ← secondLeaf]
    apply derivation.2 first.source first.sourceMem second.source second.sourceMem
      firstSourceLeaf firstSourceMem secondSourceLeaf secondSourceMem
    rw [firstId, secondId]
    exact canonical
  · exfalso
    have leftValidityMem := FormulaValidity.toValidity_mem_validityOccurrences
      first.invariant leftLeaf leftLeafMem
    have rightValidityMem := FormulaValidity.toValidity_mem_validityOccurrences
      second.invariant rightLeaf rightLeafMem
    have secondActive := node.postponedInvariant_active derivation.1.1 timely
      second.source second.sourceMem second.shape
    apply node.skippedInvariants_disjoint computed sound derivation.1.1.1 first.skipped
      second.skipped first.source first.sourceMem first.edge first.invariant first.shape
      leftLeaf.toValidity leftValidityMem second.source second.sourceMem second.edge
      second.invariant second.shape rightLeaf.toValidity rightValidityMem secondActive canonical
    refine ⟨instant, ?_, ?_, ?_, ?_⟩ <;>
      (simp only [FormulaValidity.SemanticOccurrence.reroot,
        FormulaValidity.SemanticOccurrence.shift,
        FormulaValidity.SemanticOccurrence.toValidity,
        Stlsat.Interval.shift] at * <;> omega)

/-- The obligations already satisfied by the ranked signal are compatible
with every new skipped invariant copy. -/
theorem ranked_compatible_requirement (origin : node.SkippedOrigin size rank)
    (derivation : node.FullDerivationValid) (timely : node.Timely)
    (poised : node.Poised) (normal : node.InStrictNormalForm)
    {signal : Stlsat.Signal semantics}
    (holds : node.RankedHolds size (rank - 1) semantics signal)
    (computed : node.jumpSize? = some size) (sound : node.SoundSafe) :
    (node.rankedRequirement normal holds).Compatible
      (origin.requirement derivation normal holds) := by
  intro live liveMem shifted shiftedMem instant liveLower liveUpper shiftedLower shiftedUpper
  change live ∈ node.liveSemanticLeaves at liveMem
  change shifted ∈ origin.semanticLeaves at shiftedMem
  unfold Node.liveSemanticLeaves at liveMem
  rcases List.mem_flatMap.mp liveMem with ⟨other, otherListMem, liveMem⟩
  have otherMem : other ∈ node.label := Finset.mem_toList.mp otherListMem
  rcases List.mem_map.mp liveMem with ⟨liveLeaf, liveLeafMem, rfl⟩
  rcases List.mem_map.mp shiftedMem with ⟨shiftedLeaf, shiftedLeafMem, rfl⟩
  simp only [FormulaValidity.SemanticOccurrence.reroot, List.nil_append]
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
    · refine ⟨canonical, ?_⟩
      change liveLeaf.leaf = shiftedLeaf.leaf
      rcases origin.semantic_source derivation timely shiftedLeaf shiftedLeafMem with
        ⟨sourceLeaf, sourceLeafMem, sourceId, sourceLeafEq⟩
      rw [← sourceLeafEq]
      apply derivation.2 other otherMem origin.source origin.sourceMem
        liveLeaf liveSemanticMem sourceLeaf sourceLeafMem
      rw [sourceId]
      exact canonical
    · exfalso
      have shiftedValidityMem := FormulaValidity.toValidity_mem_validityOccurrences
        origin.invariant shiftedLeaf shiftedLeafMem
      have liveValidityMem := FormulaValidity.toValidity_mem_validityOccurrences
        other.formula liveLeaf liveSemanticMem
      apply node.skippedInvariant_disjoint_from_liveTemporal computed sound
        derivation.1.1.1 origin.skipped origin.source origin.sourceMem origin.edge
        origin.invariant origin.shape shiftedLeaf.toValidity shiftedValidityMem other
        otherMem otherTemporal liveLeaf.toValidity liveValidityMem (by
          intro equal
          exact canonical equal.symm)
      refine ⟨instant, ?_, ?_, ?_, ?_⟩ <;>
        (simp only [FormulaValidity.SemanticOccurrence.reroot,
          FormulaValidity.SemanticOccurrence.shift,
          FormulaValidity.SemanticOccurrence.toValidity,
          Stlsat.Interval.shift] at * <;> omega)
  · have notTemporal : other.isTemporal = false := by
      exact Bool.eq_false_of_not_eq_true otherTemporal
    have atCurrent := node.semanticFrom_window_eq_time_of_nonTemporal poised normal
      other otherMem notTemporal liveLeaf liveLeafMem
    rcases atCurrent with ⟨liveWindowLower, liveWindowUpper⟩
    have positive := origin.positive
    exfalso
    simp only [FormulaValidity.SemanticOccurrence.reroot,
      FormulaValidity.SemanticOccurrence.shift, Stlsat.Interval.shift] at *
    omega

end SkippedOrigin

/-- One splicing round adds every marked obligation at a fixed positive
structural rank. -/
theorem exists_rankedHolds_of_previous {node : Node Atom} {size rank : Nat}
    {semantics : Stlsat.AtomicSemantics Atom}
    (rankPositive : 0 < rank)
    (derivation : node.FullDerivationValid)
    (poised : node.Poised) (timely : node.Timely)
    (normal : node.InStrictNormalForm)
    (computed : node.jumpSize? = some size) (sound : node.SoundSafe)
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
        (requirement first).Compatible (requirement second) := by
    intro first second
    cases first with
    | inl unit =>
        cases second with
        | inl unit => exact Or.inl rfl
        | inr origin =>
            exact Or.inr (origin.ranked_compatible_requirement derivation timely poised
              normal previous computed sound)
    | inr firstOrigin =>
        cases second with
        | inl unit =>
            exact Or.inr (firstOrigin.ranked_compatible_requirement derivation timely poised
              normal previous computed sound).symm
        | inr secondOrigin =>
            exact Or.inr (firstOrigin.requirements_compatible secondOrigin derivation timely
              normal previous computed sound)
  rcases FormulaValidity.exists_signal_accepting_semanticRequirement_family
      requirement compatible with ⟨next, accepts⟩
  have old : node.RankedHolds size (rank - 1) semantics next := by
    have := accepts (Sum.inl ())
    change node.RankedHolds size (rank - 1) semantics next at this
    exact this
  have skipped (origin : node.SkippedOrigin size rank) :
      origin.invariant.Satisfies semantics next (node.time + origin.offset) := by
    have := accepts (Sum.inr origin)
    change origin.invariant.Satisfies semantics next
      (node.time + origin.offset) at this
    exact this
  refine ⟨next, ⟨old.1, ?_⟩, skipped⟩
  intro occurrence present marked bounded
  by_cases already : formulaRank occurrence.formula ≤ rank - 1
  · exact old.2 occurrence present marked already
  have positiveSize := node.jumpSize_pos computed
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

theorem rankedHolds_zero_of_base {node : Node Atom} {size : Nat}
    {semantics : Stlsat.AtomicSemantics Atom} {signal : Stlsat.Signal semantics}
    (base : node.BaseHolds size semantics signal) :
    node.RankedHolds size 0 semantics signal := by
  refine ⟨base, ?_⟩
  intro occurrence present marked bounded
  cases occurrence with
  | mk id payload parent =>
      cases payload <;> simp_all [AnnotatedOccurrence.formula, formulaRank]

/-- Iterating the rank promotion constructs the obligations of any requested
finite structural rank. -/
theorem exists_rankedHolds {node : Node Atom} {size : Nat}
    {semantics : Stlsat.AtomicSemantics Atom}
    (derivation : node.FullDerivationValid)
    (poised : node.Poised) (timely : node.Timely)
    (normal : node.InStrictNormalForm)
    (computed : node.jumpSize? = some size) (sound : node.SoundSafe)
    {baseSignal : Stlsat.Signal semantics}
    (base : node.BaseHolds size semantics baseSignal) (rank : Nat) :
    ∃ signal : Stlsat.Signal semantics, node.RankedHolds size rank semantics signal := by
  induction rank with
  | zero => exact ⟨baseSignal, rankedHolds_zero_of_base base⟩
  | succ rank ih =>
      rcases ih with ⟨signal, holds⟩
      rcases node.exists_rankedHolds_of_previous (rank := rank + 1) (by omega)
          derivation poised timely normal computed sound (by simpa using holds) with
        ⟨next, nextHolds, skipped⟩
      exact ⟨next, nextHolds⟩

/-- A uniform rank bound for all formulas in the finite live label. -/
noncomputable def maxFormulaRank (node : Node Atom) : Nat := by
  classical
  exact node.label.toList.foldr (fun occurrence rank =>
    max (formulaRank occurrence.formula) rank) 0

theorem formulaRank_le_maxFormulaRank (node : Node Atom)
    (occurrence : AnnotatedOccurrence Atom) (present : occurrence ∈ node.label) :
    formulaRank occurrence.formula ≤ node.maxFormulaRank := by
  classical
  have listLemma (list : List (AnnotatedOccurrence Atom))
      (membership : occurrence ∈ list) :
      formulaRank occurrence.formula ≤
        list.foldr (fun item rank => max (formulaRank item.formula) rank) 0 := by
    induction list with
    | nil => simp at membership
    | cons head tail ih =>
        simp only [List.mem_cons] at membership
        rcases membership with rfl | membership
        · exact Nat.le_max_left _ _
        · exact (ih membership).trans (Nat.le_max_right _ _)
  exact listLemma node.label.toList (Finset.mem_toList.mpr present)

/-- The last promotion round simultaneously supplies every skipped invariant,
because its rank is strictly above every live source rank. -/
theorem exists_fullRankedHolds_with_skipped {node : Node Atom} {size : Nat}
    {semantics : Stlsat.AtomicSemantics Atom}
    (derivation : node.FullDerivationValid)
    (poised : node.Poised) (timely : node.Timely)
    (normal : node.InStrictNormalForm)
    (computed : node.jumpSize? = some size) (sound : node.SoundSafe)
    {baseSignal : Stlsat.Signal semantics}
    (base : node.BaseHolds size semantics baseSignal) :
    ∃ signal : Stlsat.Signal semantics,
      node.RankedHolds size (node.maxFormulaRank + 1) semantics signal ∧
      ∀ origin : node.SkippedOrigin size (node.maxFormulaRank + 1),
        origin.invariant.Satisfies semantics signal (node.time + origin.offset) := by
  rcases node.exists_rankedHolds derivation poised timely normal computed sound base
      node.maxFormulaRank with ⟨signal, holds⟩
  simpa using node.exists_rankedHolds_of_previous
    (rank := node.maxFormulaRank + 1) (by omega) derivation poised timely normal
    computed sound (by simpa using holds)

end Node
end Stlsat.Jump
