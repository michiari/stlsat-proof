/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Mathlib.Data.Nat.Find
import Stlsat.Semantics

/-!
# Equivalences between ordinary and strict STL operators

This file proves the temporal equivalences stated in the paper's Background
section.  Ordinary until and release are semantic predicates (rather than
constructors of `Formula`), so a nested expression such as
`F_[a,a] (phi U_[0,b-a] psi)` is written as an existential over the singleton
interval whose body is `Formula.SatisfiesUntil`.
-/

namespace Stlsat

universe u

namespace Interval

/-- The singleton closed interval `[instant, instant]`. -/
def singleton (instant : ℕ) : Interval where
  lower := instant
  upper := instant
  lower_le_upper := le_rfl

/-- The interval `[0, upper]`. -/
def zeroTo (upper : ℕ) : Interval where
  lower := 0
  upper := upper
  lower_le_upper := Nat.zero_le upper

/-- Translate an interval to start at zero while retaining its length. -/
def normalized (interval : Interval) : Interval :=
  zeroTo (interval.upper - interval.lower)

@[simp]
theorem singleton_contains_iff {instant offset : ℕ} :
    (singleton instant).Contains offset ↔ offset = instant := by
  simp only [singleton, Contains]
  omega

@[simp]
theorem zeroTo_contains_iff {upper offset : ℕ} :
    (zeroTo upper).Contains offset ↔ offset ≤ upper := by
  simp [zeroTo, Contains]

@[simp]
theorem normalized_contains_iff {interval : Interval} {offset : ℕ} :
    interval.normalized.Contains offset ↔ offset ≤ interval.upper - interval.lower := by
  simp [normalized]

end Interval

namespace Formula

variable {Atom : Type u}

/-- `¬(φ sU_I ψ) ≡ (¬φ) sR_I (¬ψ)`. -/
theorem neg_strictUntil_iff_strictRelease (interval : Interval)
    (invariant target : Formula Atom) (semantics : AtomicSemantics Atom)
    (signal : Signal semantics) (time : ℕ) :
    (neg (strictUntil interval invariant target)).Satisfies semantics signal time ↔
      (strictRelease interval (neg invariant) (neg target)).Satisfies
        semantics signal time := by
  classical
  simp [Satisfies]

/-- `¬(φ sR_I ψ) ≡ (¬φ) sU_I (¬ψ)`. -/
theorem neg_strictRelease_iff_strictUntil (interval : Interval)
    (target invariant : Formula Atom) (semantics : AtomicSemantics Atom)
    (signal : Signal semantics) (time : ℕ) :
    (neg (strictRelease interval target invariant)).Satisfies semantics signal time ↔
      (strictUntil interval (neg target) (neg invariant)).Satisfies
        semantics signal time := by
  classical
  simp [Satisfies]

/-- `¬(φ U_I ψ) ≡ (¬φ) R_I (¬ψ)`. -/
theorem neg_until_iff_release (interval : Interval)
    (invariant target : Formula Atom) (semantics : AtomicSemantics Atom)
    (signal : Signal semantics) (time : ℕ) :
    ¬SatisfiesUntil invariant target semantics signal time interval ↔
      SatisfiesRelease (neg invariant) (neg target) semantics signal time interval := by
  classical
  simp [SatisfiesUntil, SatisfiesRelease, Satisfies]

/-- `¬(φ R_I ψ) ≡ (¬φ) U_I (¬ψ)`. -/
theorem neg_release_iff_until (interval : Interval)
    (target invariant : Formula Atom) (semantics : AtomicSemantics Atom)
    (signal : Signal semantics) (time : ℕ) :
    ¬SatisfiesRelease target invariant semantics signal time interval ↔
      SatisfiesUntil (neg target) (neg invariant) semantics signal time interval := by
  classical
  simp [SatisfiesUntil, SatisfiesRelease, Satisfies]

/-- `φ sU_[a,b] ψ ≡ F_[a,a] ((φ ∨ ψ) U_[0,b-a] ψ)`. -/
theorem strictUntil_iff_eventually_until (interval : Interval)
    (invariant target : Formula Atom) (semantics : AtomicSemantics Atom)
    (signal : Signal semantics) (time : ℕ) :
    (strictUntil interval invariant target).Satisfies semantics signal time ↔
      ∃ offset,
        (Interval.singleton interval.lower).Contains offset ∧
          SatisfiesUntil (or invariant target) target semantics signal (time + offset)
            interval.normalized := by
  classical
  simp only [Satisfies, SatisfiesUntil]
  constructor
  · rintro ⟨targetOffset, targetIn, targetHolds, invariantPrefix⟩
    have targetAfterLower := targetIn.1
    have targetBeforeUpper := targetIn.2
    refine ⟨interval.lower, by simp, targetOffset - interval.lower, ?_, ?_, ?_⟩
    · simp only [Interval.normalized_contains_iff]
      omega
    · convert targetHolds using 1
      omega
    · intro prefixOffset prefixBeforeTarget
      by_cases atTarget : interval.lower + prefixOffset = targetOffset
      · right
        convert targetHolds using 1
        omega
      · left
        convert invariantPrefix (interval.lower + prefixOffset) (by omega) (by omega) using 1
        omega
  · rintro ⟨offset, offsetIn, targetOffset, targetIn, targetHolds, prefixHolds⟩
    have offset_eq : offset = interval.lower :=
      Interval.singleton_contains_iff.mp offsetIn
    subst offset
    have targetExists : ∃ candidate,
        candidate ≤ targetOffset ∧
          target.Satisfies semantics signal (time + interval.lower + candidate) :=
      ⟨targetOffset, le_rfl, targetHolds⟩
    let targetOffset' := Nat.find targetExists
    have targetOffset'_spec :
        targetOffset' ≤ targetOffset ∧
          target.Satisfies semantics signal (time + interval.lower + targetOffset') :=
      Nat.find_spec targetExists
    refine ⟨interval.lower + targetOffset', ?_, ?_, ?_⟩
    · constructor
      · omega
      · simp only [Interval.normalized_contains_iff] at targetIn
        have := interval.lower_le_upper
        omega
    · convert targetOffset'_spec.2 using 1
      omega
    · intro invariantOffset invariantAfterLower invariantBeforeTarget
      have relativeBefore : invariantOffset - interval.lower < targetOffset' := by
        omega
      have relativeBeforeOriginal : invariantOffset - interval.lower ≤ targetOffset := by
        omega
      rcases prefixHolds (invariantOffset - interval.lower) relativeBeforeOriginal with
        invariantHolds | targetHoldsEarlier
      · convert invariantHolds using 1
        omega
      · exact False.elim ((Nat.find_min targetExists relativeBefore)
          ⟨relativeBeforeOriginal, targetHoldsEarlier⟩)

/-- `φ sR_[a,b] ψ ≡ F_[a,a] ((φ ∧ ψ) R_[0,b-a] ψ)`. -/
theorem strictRelease_iff_eventually_release (interval : Interval)
    (target invariant : Formula Atom) (semantics : AtomicSemantics Atom)
    (signal : Signal semantics) (time : ℕ) :
    (strictRelease interval target invariant).Satisfies semantics signal time ↔
      ∃ offset,
        (Interval.singleton interval.lower).Contains offset ∧
          SatisfiesRelease (and target invariant) invariant semantics signal (time + offset)
            interval.normalized := by
  classical
  have strictNeg :
      ¬(strictRelease interval target invariant).Satisfies semantics signal time ↔
        (strictUntil interval (neg target) (neg invariant)).Satisfies
          semantics signal time := by
    simpa only [Satisfies] using
      neg_strictRelease_iff_strictUntil interval target invariant semantics signal time
  have until_iff_notRelease (instant : ℕ) :
      SatisfiesUntil (or (neg target) (neg invariant)) (neg invariant)
          semantics signal instant interval.normalized ↔
        ¬SatisfiesRelease (and target invariant) invariant
          semantics signal instant interval.normalized := by
    rw [neg_release_iff_until]
    simp only [SatisfiesUntil]
    apply exists_congr
    intro targetOffset
    apply and_congr_right
    intro _
    apply and_congr Iff.rfl
    apply forall_congr'
    intro prefixOffset
    apply imp_congr_right
    intro _
    simp only [Satisfies]
    constructor
    · rintro (targetFails | invariantFails) ⟨targetHolds, invariantHolds⟩
      · exact targetFails targetHolds
      · exact invariantFails invariantHolds
    · intro conjunctionFails
      by_cases targetHolds : target.Satisfies semantics signal (instant + prefixOffset)
      · exact Or.inr fun invariantHolds => conjunctionFails ⟨targetHolds, invariantHolds⟩
      · exact Or.inl targetHolds
  have nestedUntil_iff_nestedNotRelease :
      (∃ offset,
          (Interval.singleton interval.lower).Contains offset ∧
            SatisfiesUntil (or (neg target) (neg invariant)) (neg invariant)
              semantics signal (time + offset) interval.normalized) ↔
        ∃ offset,
          (Interval.singleton interval.lower).Contains offset ∧
            ¬SatisfiesRelease (and target invariant) invariant
              semantics signal (time + offset) interval.normalized := by
    apply exists_congr
    intro offset
    apply and_congr_right
    intro _
    exact until_iff_notRelease (time + offset)
  have singletonNotRelease :
      (∃ offset,
          (Interval.singleton interval.lower).Contains offset ∧
            ¬SatisfiesRelease (and target invariant) invariant
              semantics signal (time + offset) interval.normalized) ↔
        ¬∃ offset,
          (Interval.singleton interval.lower).Contains offset ∧
            SatisfiesRelease (and target invariant) invariant
              semantics signal (time + offset) interval.normalized := by
    simp
  have negEquivalence :
      ¬(strictRelease interval target invariant).Satisfies semantics signal time ↔
        ¬∃ offset,
          (Interval.singleton interval.lower).Contains offset ∧
            SatisfiesRelease (and target invariant) invariant
              semantics signal (time + offset) interval.normalized :=
    strictNeg.trans ((strictUntil_iff_eventually_until interval
      (neg target) (neg invariant) semantics signal time).trans
        (nestedUntil_iff_nestedNotRelease.trans singletonNotRelease))
  constructor
  · intro strictReleaseHolds
    exact Classical.byContradiction fun nestedReleaseFails =>
      (negEquivalence.mpr nestedReleaseFails) strictReleaseHolds
  · intro nestedReleaseHolds
    exact Classical.byContradiction fun strictReleaseFails =>
      (negEquivalence.mp strictReleaseFails) nestedReleaseHolds

/-- `φ U_[a,b] ψ ≡ G_[0,a] φ ∧ φ sU_[a,b] (φ ∧ ψ)`. -/
theorem until_iff_always_and_strictUntil (interval : Interval)
    (invariant target : Formula Atom) (semantics : AtomicSemantics Atom)
    (signal : Signal semantics) (time : ℕ) :
    SatisfiesUntil invariant target semantics signal time interval ↔
      (and (always (Interval.zeroTo interval.lower) invariant)
        (strictUntil interval invariant (and invariant target))).Satisfies
          semantics signal time := by
  simp only [SatisfiesUntil, Satisfies]
  constructor
  · rintro ⟨targetOffset, targetIn, targetHolds, invariantThroughTarget⟩
    refine ⟨?_, targetOffset, targetIn, ⟨invariantThroughTarget targetOffset le_rfl,
      targetHolds⟩, ?_⟩
    · intro initialOffset initialIn
      apply invariantThroughTarget initialOffset
      simp only [Interval.zeroTo_contains_iff] at initialIn
      exact initialIn.trans targetIn.1
    · intro invariantOffset _ invariantBeforeTarget
      exact invariantThroughTarget invariantOffset invariantBeforeTarget.le
  · rintro ⟨initialInvariant, targetOffset, targetIn,
      ⟨invariantAtTarget, targetHolds⟩, strictPrefix⟩
    refine ⟨targetOffset, targetIn, targetHolds, ?_⟩
    intro invariantOffset invariantBeforeOrAtTarget
    by_cases beforeLower : invariantOffset ≤ interval.lower
    · exact initialInvariant invariantOffset (by simpa using beforeLower)
    by_cases beforeTarget : invariantOffset < targetOffset
    · exact strictPrefix invariantOffset (by omega) beforeTarget
    · have : invariantOffset = targetOffset := by omega
      simpa [this] using invariantAtTarget

/-- `φ R_[a,b] ψ ≡ F_[0,a] φ ∨ ψ sU_[a,b] φ ∨ G_[a,b] ψ`. -/
theorem release_iff_eventually_or_strictUntil_or_always (interval : Interval)
    (target invariant : Formula Atom) (semantics : AtomicSemantics Atom)
    (signal : Signal semantics) (time : ℕ) :
    SatisfiesRelease target invariant semantics signal time interval ↔
      (or (eventually (Interval.zeroTo interval.lower) target)
        (or (strictUntil interval invariant target)
          (always interval invariant))).Satisfies semantics signal time := by
  classical
  simp only [SatisfiesRelease, Satisfies]
  constructor
  · intro releaseHolds
    by_cases targetBeforeLower : ∃ offset,
        (Interval.zeroTo interval.lower).Contains offset ∧
          target.Satisfies semantics signal (time + offset)
    · exact Or.inl targetBeforeLower
    by_cases invariantThroughout : ∀ offset,
        interval.Contains offset → invariant.Satisfies semantics signal (time + offset)
    · exact Or.inr (Or.inr invariantThroughout)
    have invariantViolation : ∃ offset,
        interval.Contains offset ∧ ¬invariant.Satisfies semantics signal (time + offset) := by
      by_contra noViolation
      apply invariantThroughout
      intro offset offsetIn
      by_contra invariantFails
      exact noViolation ⟨offset, offsetIn, invariantFails⟩
    rcases invariantViolation with ⟨violatingOffset, violatingIn, invariantFails⟩
    have targetExists : ∃ offset,
        offset ≤ violatingOffset ∧ target.Satisfies semantics signal (time + offset) := by
      by_contra noTarget
      apply releaseHolds
      refine ⟨violatingOffset, violatingIn, invariantFails, ?_⟩
      simpa only [not_exists, not_and, not_not] using noTarget
    let firstTarget := Nat.find targetExists
    have firstTarget_spec :
        firstTarget ≤ violatingOffset ∧
          target.Satisfies semantics signal (time + firstTarget) :=
      Nat.find_spec targetExists
    have firstTarget_afterLower : interval.lower < firstTarget := by
      by_contra notAfterLower
      apply targetBeforeLower
      refine ⟨firstTarget, ?_, firstTarget_spec.2⟩
      simpa only [Interval.zeroTo_contains_iff] using Nat.le_of_not_gt notAfterLower
    refine Or.inr (Or.inl ⟨firstTarget, ⟨firstTarget_afterLower.le,
      firstTarget_spec.1.trans violatingIn.2⟩, firstTarget_spec.2, ?_⟩)
    intro prefixOffset prefixAfterLower prefixBeforeTarget
    by_contra invariantFailsAtPrefix
    apply releaseHolds
    refine ⟨prefixOffset, ⟨prefixAfterLower, ?_⟩, invariantFailsAtPrefix, ?_⟩
    · exact prefixBeforeTarget.le.trans (firstTarget_spec.1.trans violatingIn.2)
    · intro earlierOffset earlierBeforeOrAtPrefix targetHoldsEarlier
      exact (Nat.find_min targetExists (earlierBeforeOrAtPrefix.trans_lt prefixBeforeTarget))
        ⟨by omega, targetHoldsEarlier⟩
  · rintro (targetBeforeLower | strictUntilHolds | invariantThroughout)
    · rintro ⟨violatingOffset, violatingIn, _, allTargetsFail⟩
      rcases targetBeforeLower with ⟨targetOffset, targetIn, targetHolds⟩
      apply allTargetsFail targetOffset
      · simp only [Interval.zeroTo_contains_iff] at targetIn
        exact targetIn.trans violatingIn.1
      · exact targetHolds
    · rintro ⟨violatingOffset, violatingIn, invariantFails, allTargetsFail⟩
      rcases strictUntilHolds with
        ⟨targetOffset, targetIn, targetHolds, invariantBeforeTarget⟩
      by_cases targetBeforeOrAtViolation : targetOffset ≤ violatingOffset
      · exact allTargetsFail targetOffset targetBeforeOrAtViolation targetHolds
      · exact invariantFails
          (invariantBeforeTarget violatingOffset violatingIn.1 (by omega))
    · rintro ⟨violatingOffset, violatingIn, invariantFails, _⟩
      exact invariantFails (invariantThroughout violatingOffset violatingIn)

/-- `φ R_[a,b] ψ ≡ F_[0,a-1] φ ∨ ψ sU_[a,b] φ ∨ G_[a,b] ψ`. -/
theorem release_iff_eventually_before_or_strictUntil_or_always (interval : Interval)
    (target invariant : Formula Atom) (semantics : AtomicSemantics Atom)
    (signal : Signal semantics) (time : ℕ) :
    SatisfiesRelease target invariant semantics signal time interval ↔
      (or (eventually (Interval.zeroTo (interval.lower - 1)) target)
        (or (strictUntil interval invariant target)
          (always interval invariant))).Satisfies semantics signal time := by
  rw [release_iff_eventually_or_strictUntil_or_always]
  simp only [Satisfies]
  constructor
  · rintro (⟨targetOffset, targetIn, targetHolds⟩ |
      strictUntilHolds | invariantThroughout)
    · simp only [Interval.zeroTo_contains_iff] at targetIn
      by_cases targetBeforeLower : targetOffset < interval.lower
      · exact Or.inl ⟨targetOffset, by simpa using (show targetOffset ≤ interval.lower - 1 by
          omega), targetHolds⟩
      · have targetAtLower : targetOffset = interval.lower := by omega
        exact Or.inr (Or.inl ⟨interval.lower,
          ⟨le_rfl, interval.lower_le_upper⟩, by simpa [targetAtLower] using targetHolds,
          by omega⟩)
    · exact Or.inr (Or.inl strictUntilHolds)
    · exact Or.inr (Or.inr invariantThroughout)
  · rintro (⟨targetOffset, targetIn, targetHolds⟩ |
      strictUntilHolds | invariantThroughout)
    · exact Or.inl ⟨targetOffset, by
        simp only [Interval.zeroTo_contains_iff] at targetIn ⊢
        omega, targetHolds⟩
    · exact Or.inr (Or.inl strictUntilHolds)
    · exact Or.inr (Or.inr invariantThroughout)

end Formula

end Stlsat
