/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Basic.Tableau
import Stlsat.Tableau.Basic.Soundness

/-!
# Soundness of the basic tableau

This compatibility entry point exposes the paper-facing theorem name.  The
proof is the basic rule-set instance of the shared backward-model induction in
`Stlsat.Tableau.Soundness`.
-/

namespace Stlsat.BasicTableau

universe u

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : AtomicSemantics Atom} {formula : Formula Atom}

theorem hasModel_of_acceptingBranch (tableau : BasicTableau semantics formula)
    (accepted : tableau.HasAcceptingBranch) : formula.HasModel semantics := by
  exact Stlsat.Tableau.Basic.Development.hasModel_of_acceptingBranch tableau accepted

/-- Every accepted basic tableau has a satisfying signal. -/
theorem soundness (tableau : BasicTableau semantics formula)
    (accepted : tableau.HasAcceptingBranch) : formula.Satisfiable semantics := by
  exact Stlsat.Tableau.Basic.Development.soundness tableau accepted

end Stlsat.BasicTableau
