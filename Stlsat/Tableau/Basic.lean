/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Tableau.Core

/-!
# The basic rule set on the shared tableau core

Both tableau variants use `Stlsat.Tableau.Node`, `Stlsat.Tableau.Expansion`, and
`Stlsat.Tableau.TableauTree`.  The basic configuration differs only in its
advancement rule: every poised temporal node takes one `STEP`.  The JUMP
configuration in `Stlsat.Tableau.Jump` replaces that advancement relation by
the mutually exclusive `STEP`/`JUMP` alternatives. Both configurations are
instances of the same `Stlsat.Tableau.Development` structure.
-/

namespace Stlsat.Tableau.Basic

universe u

/-- Ordinary expansion and one-instant `STEP`, with no JUMP-specific guard. -/
inductive Rule {Atom : Type u} [DecidableEq Atom]
    (semantics : Stlsat.AtomicSemantics Atom) (node : Stlsat.Tableau.Node Atom) :
    List (Stlsat.Tableau.Node Atom) → Prop where
  | expand {children : List (Stlsat.Tableau.Node Atom)}
      (notRejected : ¬node.Rejected semantics)
      (expansion : Stlsat.Tableau.Expansion node children) : Rule semantics node children
  | step (notRejected : ¬node.Rejected semantics) (poised : node.Poised)
      (hasTemporal : node.ContainsTemporal) :
      Rule semantics node [node.step]

/-- The basic configuration of the shared developed-tableau container. -/
abbrev Development {Atom : Type u} [DecidableEq Atom]
    (semantics : Stlsat.AtomicSemantics Atom) (formula : Stlsat.Formula Atom) :=
  Stlsat.Tableau.Development semantics formula (Rule semantics)

end Stlsat.Tableau.Basic
