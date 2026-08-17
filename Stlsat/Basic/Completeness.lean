/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Basic.Soundness
import Stlsat.Tableau.Basic.Completeness

/-!
# Completeness of the basic tableau

This paper-facing entry point instantiates the shared model-guided finite-tree
induction with the ordinary expansion/STEP rule set.
-/

namespace Stlsat.BasicTableau

universe u

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : AtomicSemantics Atom} {formula : Formula Atom}

theorem hasAcceptingBranch_of_hasModel (tableau : BasicTableau semantics formula)
    (model : formula.HasModel semantics) : tableau.HasAcceptingBranch := by
  exact Stlsat.Tableau.Basic.Development.hasAcceptingBranch_of_hasModel tableau model

/-- Every satisfiable formula has an accepted branch in every fully developed
basic tableau for it. -/
theorem completeness (tableau : BasicTableau semantics formula)
    (satisfiable : formula.Satisfiable semantics) : tableau.HasAcceptingBranch := by
  exact Stlsat.Tableau.Basic.Development.completeness tableau satisfiable

end Stlsat.BasicTableau
