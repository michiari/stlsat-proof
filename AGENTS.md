# Lean formalization instructions

This repository formalizes a theorem from a research paper using Lean 4
and Mathlib.

## Verification

After modifying Lean files, run:

    lake build

Do not claim that a proof is complete unless `lake build` succeeds.

## Style

- Prefer existing Mathlib definitions and lemmas.
- Search Mathlib before introducing new abstractions.
- Keep theorem statements close to the mathematical formulation.
- Break long proofs into named intermediate lemmas.
- Avoid `sorry`, `admit`, new axioms, and `unsafe`.
- Do not weaken or alter theorem assumptions merely to make the proof compile.
- Explain any mismatch between the paper statement and the Lean statement.

## Workflow

1. Inspect the definitions and theorem statement.
2. Identify existing relevant Mathlib lemmas.
3. Formalize one intermediate lemma at a time.
4. Compile after every substantial change.
5. When blocked, leave a precise comment describing:
   - the current goal;
   - the missing mathematical fact;
   - candidate Mathlib lemmas already investigated.
