/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Tableau.Basic

/-!
# Basic tableau configuration

The basic tableau is the ordinary rule set instantiated on the project's
single provenance-aware node, expansion, raw-tree, and developed-tableau
representation. Provenance fields are semantically inert in this mode and
impose no JUMP guards or proof obligations.
-/

namespace Stlsat

universe u

/-- Backwards-compatible public name for the ordinary rule relation. -/
abbrev BasicRule {Atom : Type u} [DecidableEq Atom] :=
  Stlsat.Tableau.Basic.Rule (Atom := Atom)

/-- Both configurations use the same raw finite tableau tree. -/
abbrev TableauTree := Stlsat.Tableau.TableauTree

/-- The basic configuration of the shared developed-tableau structure. -/
abbrev BasicTableau {Atom : Type u} [DecidableEq Atom] :=
  Stlsat.Tableau.Basic.Development (Atom := Atom)

namespace BasicTableau

abbrev HasAcceptingBranch {Atom : Type u} [DecidableEq Atom]
    {semantics : AtomicSemantics Atom} {formula : Formula Atom}
    (tableau : BasicTableau semantics formula) : Prop :=
  Stlsat.Tableau.Development.HasAcceptingBranch tableau

end BasicTableau

end Stlsat
