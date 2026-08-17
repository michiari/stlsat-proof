/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.Soundness
import Stlsat.Jump.Completeness
import Stlsat.Jump.Termination
import Stlsat.Jump.Construction

/-!
# The STL tableau with JUMP

This umbrella module exposes the soundness, completeness, termination, and
construction theorems for the corrected JUMP tableau.  Every strict-normal-form
formula has a finite, fully developed tableau, and acceptance is equivalent to
satisfiability.
-/

/-! The implementation now lives in the shared `Stlsat.Tableau` framework.
The aliases below preserve the original paper-facing API. -/

namespace Stlsat.Jump

universe u

abbrev Tableau {Atom : Type u} [DecidableEq Atom] :=
  Stlsat.Tableau.Jump.Development (Atom := Atom)

namespace Tableau

abbrev HasAcceptingBranch {Atom : Type u} [DecidableEq Atom]
    {semantics : Stlsat.AtomicSemantics Atom} {formula : Stlsat.Formula Atom}
    (tableau : Tableau semantics formula) : Prop :=
  Stlsat.Tableau.Development.HasAcceptingBranch tableau

theorem soundness {Atom : Type u} [DecidableEq Atom]
    {semantics : Stlsat.AtomicSemantics Atom} {formula : Stlsat.Formula Atom}
    (tableau : Tableau semantics formula) (accepted : tableau.HasAcceptingBranch) :
    formula.Satisfiable semantics :=
  Stlsat.Tableau.Jump.Development.soundness tableau accepted

theorem completeness {Atom : Type u} [DecidableEq Atom]
    {semantics : Stlsat.AtomicSemantics Atom} {formula : Stlsat.Formula Atom}
    (tableau : Tableau semantics formula) (satisfiable : formula.Satisfiable semantics) :
    tableau.HasAcceptingBranch :=
  Stlsat.Tableau.Jump.Development.completeness tableau satisfiable

theorem exists_of_strictNormalForm {Atom : Type u} [DecidableEq Atom]
    {semantics : Stlsat.AtomicSemantics Atom} {formula : Stlsat.Formula Atom}
    (normal : formula.InStrictNormalForm) : Nonempty (Tableau semantics formula) :=
  Stlsat.Tableau.Jump.Development.exists_of_strictNormalForm normal

theorem exists_hasAcceptingBranch_iff_satisfiable
    {Atom : Type u} [DecidableEq Atom]
    {semantics : Stlsat.AtomicSemantics Atom} {formula : Stlsat.Formula Atom}
    (normal : formula.InStrictNormalForm) :
    ∃ tableau : Tableau semantics formula,
      tableau.HasAcceptingBranch ↔ formula.Satisfiable semantics :=
  Stlsat.Tableau.Jump.Development.exists_hasAcceptingBranch_iff_satisfiable normal

theorem exists_hasAcceptingBranch_iff_basic
    {Atom : Type u} [DecidableEq Atom]
    {semantics : Stlsat.AtomicSemantics Atom} {formula : Stlsat.Formula Atom}
    (basic : Stlsat.BasicTableau semantics formula) :
    ∃ tableau : Tableau semantics formula,
      tableau.HasAcceptingBranch ↔ basic.HasAcceptingBranch :=
  Stlsat.Tableau.Jump.Development.exists_hasAcceptingBranch_iff_basic basic

end Tableau

end Stlsat.Jump
