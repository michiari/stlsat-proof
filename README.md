# A verified tableau for Signal Temporal Logic

This repository contains a Lean 4 formalization of the tree-shaped tableau in
the paper

> **stlsat—An Improved Tableau for Satisfiability Checking of Signal Temporal
> Logic Formulas**

The development covers bounded, discrete-time Signal Temporal Logic (STL), the
ordinary **basic tableau**, and the corrected **JUMP** optimization. It proves
construction, termination, soundness, and completeness without `sorry`, new
axioms, or unsafe proof mechanisms.

An additional variable-aware JUMP configuration ignores overlapping validity
windows when their signed atoms have disjoint variable supports.  Its
correctness is explicit about the semantic locality/amalgamation property
which this optimization needs.

The corrected paper source is [`human/stlsat/main.tex`](human/stlsat/main.tex).
Its tableau section begins at
[`\section{Tree-Shaped Tableau}`](human/stlsat/main.tex#L344), and the detailed
proofs are in the
[`Theorem Proofs` appendix](human/stlsat/main.tex#L1173).

## Main results

A tableau is represented by `Stlsat.Tableau.Development`, parameterized by its
rule relation. Thus Basic and JUMP developments use the same nodes, ordinary
expansions, trees, acceptance condition, and semantic interpretation.

| Result | Lean declaration | Paper correspondence |
|---|---|---|
| Basic soundness | [`Stlsat.Tableau.Basic.Development.soundness`](Stlsat/Tableau/Basic/Soundness.lean#L86) | Accepting-branch-to-satisfiability implication of the Basic Tableau theorem at [`main.tex:486–489`](human/stlsat/main.tex#L486) |
| Basic completeness | [`Stlsat.Tableau.Basic.Development.completeness`](Stlsat/Tableau/Basic/Completeness.lean#L64) | Satisfiability-to-accepting-branch implication of the same Basic Tableau theorem |
| JUMP soundness | [`Stlsat.Tableau.Jump.Development.soundness`](Stlsat/Jump/Soundness.lean#L185) | Theorem `thm:jump-sound` at [`main.tex:769–772`](human/stlsat/main.tex#L769), followed by Basic soundness |
| JUMP completeness | [`Stlsat.Tableau.Jump.Development.completeness`](Stlsat/Jump/Completeness.lean#L541) | Theorem `thm:jump-complete` at [`main.tex:774–777`](human/stlsat/main.tex#L774), combined with Basic completeness |
| Basic/JUMP correspondence | [`Stlsat.Tableau.Jump.Development.hasAcceptingBranch_iff_basic`](Stlsat/Jump/Construction.lean#L129) | The two paper theorems `thm:jump-sound` and `thm:jump-complete` as one equivalence |
| Variable-aware JUMP soundness | [`Stlsat.Tableau.VariableJump.Development.soundness`](Stlsat/Jump/Variable/Soundness.lean) | Soundness of the support-sensitive relaxation, under `AtomicSupport` |
| Variable-aware JUMP completeness | [`Stlsat.Tableau.VariableJump.Development.completeness`](Stlsat/Jump/Variable/Completeness.lean) | Completeness of the same optimized configuration |

The paper phrases JUMP soundness and completeness as implications between
accepting branches of the JUMP and basic tableaux. Lean proves them in the
following direct semantic form:

```text
JUMP accepting branch  →  formula satisfiable
formula satisfiable    →  JUMP accepting branch
```

The theorem `hasAcceptingBranch_iff_basic` then recovers the paper's exact
branch correspondence.

### Existence and termination

The headline correctness theorems quantify over fully developed finite
tableaux. Their existence is established rather than assumed vacuously:

- [`Stlsat.Tableau.Basic.Development.exists_of_strictNormalForm`](Stlsat/Tableau/Basic/Construction.lean#L71)
- [`Stlsat.Tableau.Jump.Development.exists_of_strictNormalForm`](Stlsat/Jump/Construction.lean#L109)
- [`Stlsat.Tableau.Jump.Development.exists_hasAcceptingBranch_iff_satisfiable`](Stlsat/Jump/Construction.lean#L118)
- [`Stlsat.Tableau.VariableJump.Development.exists_of_strictNormalForm`](Stlsat/Jump/Variable/Construction.lean)
- [`Stlsat.Tableau.VariableJump.Development.exists_hasAcceptingBranch_iff_satisfiable`](Stlsat/Jump/Variable/Construction.lean)

There are no infinite rule-generated branches from an initial node:

- [`Stlsat.Tableau.Basic.no_infinite_branch`](Stlsat/Tableau/Basic/Termination.lean#L119)
- [`Stlsat.Tableau.Jump.no_infinite_branch`](Stlsat/Jump/Termination.lean#L148)
- [`Stlsat.Tableau.VariableJump.no_infinite_branch`](Stlsat/Jump/Variable/Termination.lean)

## Correspondence with the paper

The formalization follows the corrected version of
[`human/stlsat/main.tex`](human/stlsat/main.tex). The main correspondences are:

| Paper material | Lean formalization |
|---|---|
| Background syntax and discrete-time semantics, Section `sec:background` | [`Stlsat/Tableau/Syntax.lean`](Stlsat/Tableau/Syntax.lean), [`Stlsat/Semantics.lean`](Stlsat/Semantics.lean) |
| Strict normal form, around [`main.tex:340–342`](human/stlsat/main.tex#L340) | `Formula.InStrictNormalForm` in [`Syntax.lean`](Stlsat/Tableau/Syntax.lean) |
| Node labels, parent occurrences, expansion rules, STEP, and acceptance, [`main.tex:353–489`](human/stlsat/main.tex#L353) | [`Stlsat/Tableau/Core.lean`](Stlsat/Tableau/Core.lean) |
| Basic rule configuration | [`Stlsat/Tableau/Basic.lean`](Stlsat/Tableau/Basic.lean) |
| Proposition-validity intervals `tinv` and Lemma `lemma:te-limit`, [`main.tex:594–605`](human/stlsat/main.tex#L594) | [`Stlsat/Jump/Tableau.lean`](Stlsat/Jump/Tableau.lean), [`Stlsat/Jump/Validity.lean`](Stlsat/Jump/Validity.lean), [`Stlsat/Jump/Provenance.lean`](Stlsat/Jump/Provenance.lean) |
| Corrected sets `K(u)`, `N(u)`, `O(u)`, `M(u)`, and `S(u)`, the soundness limit, and the completeness no-overlap guard, [`main.tex:615–731`](human/stlsat/main.tex#L615) | Window, limit, and guard definitions in [`Stlsat/Jump/Tableau.lean`](Stlsat/Jump/Tableau.lean#L148); the paper's numerical completeness limit is unnecessary for the formal completeness proof and is not part of `Node.jumpSize?` |
| Corrected JUMP rule, beginning near [`main.tex:736`](human/stlsat/main.tex#L736) | `Node.jump`, `Node.CanJump`, and `Stlsat.Tableau.Jump.Rule` in [`Stlsat/Jump/Tableau.lean`](Stlsat/Jump/Tableau.lean#L689) |
| Soundness proof, [`main.tex:1243–1308`](human/stlsat/main.tex#L1243) | [`Stlsat/Jump/Soundness.lean`](Stlsat/Jump/Soundness.lean) and the soundness-support modules listed below |
| Completeness proof, [`main.tex:1311–1372`](human/stlsat/main.tex#L1311) | [`Stlsat/Jump/Completeness.lean`](Stlsat/Jump/Completeness.lean) and [`CompletenessSplicing.lean`](Stlsat/Jump/CompletenessSplicing.lean) |

The older source in `human/stltree/` was useful during development and uses
some different notation. The correspondence above targets the current,
corrected paper in `human/stlsat/`.

## Formalization architecture

The distinction between Basic and JUMP belongs only at the rule layer:

```text
STL syntax and semantics
          │
          ▼
shared occurrences, nodes, expansion, trees, acceptance, models
          │
          ├── Basic.Rule: ordinary expansion + STEP
          ├── Jump.Rule: ordinary expansion + conservative guarded STEP/JUMP
          └── VariableJump.Rule: the same JUMP operation with support-aware guards
```

The shared core is [`Stlsat/Tableau/Core.lean`](Stlsat/Tableau/Core.lean). Its
central type is:

```lean
Stlsat.Tableau.Development semantics formula rules
```

The two configurations are aliases obtained by supplying a rule relation:

- `Stlsat.Tableau.Basic.Development`
- `Stlsat.Tableau.Jump.Development`
- `Stlsat.Tableau.VariableJump.Development`

Occurrence identifiers and parent provenance are present in the canonical
node representation. Basic rules do not inspect them; JUMP uses them to relate
validity windows to their generating temporal occurrences. `ObligationSet` is
only a semantic projection that forgets this metadata, not a second tableau
implementation.

## Suggested reading order

1. **Syntax and semantics**
   - [`Stlsat/Tableau/Syntax.lean`](Stlsat/Tableau/Syntax.lean)
   - [`Stlsat/Semantics.lean`](Stlsat/Semantics.lean)
   - [`Stlsat/Tableau/SemanticsBase.lean`](Stlsat/Tableau/SemanticsBase.lean)

2. **Shared tableau definition**
   - [`Stlsat/Tableau/Core.lean`](Stlsat/Tableau/Core.lean)
   - [`Stlsat/Tableau/Semantics.lean`](Stlsat/Tableau/Semantics.lean)

3. **Basic configuration**
   - Rules: [`Stlsat/Tableau/Basic.lean`](Stlsat/Tableau/Basic.lean)
   - Soundness: [`Stlsat/Tableau/Basic/Soundness.lean`](Stlsat/Tableau/Basic/Soundness.lean)
   - Completeness: [`Stlsat/Tableau/Basic/Completeness.lean`](Stlsat/Tableau/Basic/Completeness.lean)
   - Termination and construction:
     [`Termination.lean`](Stlsat/Tableau/Basic/Termination.lean),
     [`Construction.lean`](Stlsat/Tableau/Basic/Construction.lean)

4. **JUMP definition**
   - [`Stlsat/Jump/Tableau.lean`](Stlsat/Jump/Tableau.lean)
   - [`Stlsat/Jump/Validity.lean`](Stlsat/Jump/Validity.lean)
   - [`Stlsat/Jump/Provenance.lean`](Stlsat/Jump/Provenance.lean)
   - [`Stlsat/Jump/AncestorCoverage.lean`](Stlsat/Jump/AncestorCoverage.lean)

5. **JUMP soundness**
   - Local semantic transport: [`LocalSoundness.lean`](Stlsat/Jump/LocalSoundness.lean)
   - Expansion/provenance invariants: [`Frontier.lean`](Stlsat/Jump/Frontier.lean),
     [`Canonical.lean`](Stlsat/Jump/Canonical.lean)
   - Compatible signal construction:
     [`CompatibleSplicing.lean`](Stlsat/Jump/CompatibleSplicing.lean),
     [`RankedConstruction.lean`](Stlsat/Jump/RankedConstruction.lean),
     [`RankedSplicing.lean`](Stlsat/Jump/RankedSplicing.lean)
   - Main theorem: [`Soundness.lean`](Stlsat/Jump/Soundness.lean)

6. **JUMP completeness**
   - Target reconstruction: [`CompletenessSplicing.lean`](Stlsat/Jump/CompletenessSplicing.lean)
   - Main theorem: [`Completeness.lean`](Stlsat/Jump/Completeness.lean)
   - Finite construction and Basic/JUMP correspondence:
     [`Construction.lean`](Stlsat/Jump/Construction.lean)

7. **Variable-aware validity windows**
   - Semantic support/amalgamation and Boolean/LRA instances:
     [`AtomicSupport.lean`](Stlsat/AtomicSupport.lean)
   - Signed window representation and optimized guards:
     [`Support.lean`](Stlsat/Jump/Variable/Support.lean)
   - Soundness splicing and main theorem:
     [`Splicing.lean`](Stlsat/Jump/Variable/Splicing.lean),
     [`Soundness.lean`](Stlsat/Jump/Variable/Soundness.lean)
   - Completeness and construction:
     [`Completeness.lean`](Stlsat/Jump/Variable/Completeness.lean),
     [`Construction.lean`](Stlsat/Jump/Variable/Construction.lean)
   - Formal limits/counterexamples:
     [`AtomicSupportCounterexamples.lean`](Stlsat/AtomicSupportCounterexamples.lean)

The umbrella module [`Stlsat/Tableau.lean`](Stlsat/Tableau.lean) exposes the
complete development.

## Modeling choices

- Time is discrete and represented by `Nat`.
- Temporal intervals are nonempty closed intervals of natural numbers.
- Input formulas are required to be in strict normal form. A proof of this is
  stored in every `Development` as `root_normal`.
- Atomic constraints are abstracted by `AtomicSemantics`. Consequently, the
  basic and conservative-JUMP correctness results apply to any nonempty
  valuation type and atomic satisfaction relation, not only real-valued
  inequalities.
- The conservative tableau remains generic over `AtomicSemantics`.  The
  variable-aware configuration additionally takes `AtomicSupport`, whose
  global `amalgamate` field says that requirements carried by equal signed
  leaves or disjoint supports can be satisfied by one valuation. Coordinate
  locality proves this property for propositional variables and finite-support
  linear real-arithmetic inequalities. The theorem
  `AtomicSupport.amalgamate_of_components` also records the more general
  component-wise principle: jointly modeled overlap components with disjoint
  aggregate supports can be combined.
- Pairwise satisfiability is deliberately not used: it does not imply global
  satisfiability, even for Boolean constraints or LRA.  The corresponding
  counterexamples are kernel-checked in `AtomicSupportCounterexamples`.
- The optimized guards ignore disjoint supports. Jump-size calculation still
  uses the shared conservative ordered-window gaps, which may shorten a jump
  but cannot remove accepting behavior or compromise correctness.
- The syntax retains native `F` and `G` operators in addition to strict until
  and strict release. The JUMP window definitions include the corresponding
  direct cases.
- Soundness and completeness apply to every fully developed tableau satisfying
  the configured rule relation, rather than relying on a particular traversal
  algorithm.

## Building

The project pins Lean and Mathlib versions in [`lean-toolchain`](lean-toolchain)
and [`lakefile.toml`](lakefile.toml). With `elan` installed, run:

```sh
lake build
```

The default target builds the complete formalization through `Stlsat.lean`.

To inspect the trusted dependencies of a main result, a Lean file may contain,
for example:

```lean
import Stlsat

#print axioms Stlsat.Tableau.Basic.Development.soundness
#print axioms Stlsat.Tableau.Basic.Development.completeness
#print axioms Stlsat.Tableau.Jump.Development.soundness
#print axioms Stlsat.Tableau.Jump.Development.completeness
#print axioms Stlsat.Tableau.VariableJump.Development.soundness
#print axioms Stlsat.Tableau.VariableJump.Development.completeness
```

At present these declarations use only the standard Lean/Mathlib principles
`propext`, `Classical.choice`, and `Quot.sound`.

## License

This project is released under the [MIT License](LICENSE).
