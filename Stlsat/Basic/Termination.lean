/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Basic.Tableau
import Stlsat.Tableau.Basic.Termination

/-!
# Termination of the basic tableau

The basic rule set uses the same canonical node measure as the JUMP rule set.
This module preserves the original paper-facing termination theorem name.
-/

namespace Stlsat

universe u

abbrev BasicChild {Atom : Type u} [DecidableEq Atom] :=
  Stlsat.Tableau.Basic.Child (Atom := Atom)

theorem basicChild_initial_accessible {Atom : Type u} [DecidableEq Atom]
    (semantics : AtomicSemantics Atom) (formula : Formula Atom) :
    Acc (BasicChild semantics) (Stlsat.Tableau.Node.initial formula) :=
  Stlsat.Tableau.Basic.child_initial_accessible semantics formula

/-- No infinite branch of ordinary expansion/STEP rules begins at the initial
node. -/
theorem no_infinite_basic_tableau_branch {Atom : Type u} [DecidableEq Atom]
    (semantics : AtomicSemantics Atom) (formula : Formula Atom) :
    ¬∃ branch : Nat → Stlsat.Tableau.Node Atom,
      branch 0 = Stlsat.Tableau.Node.initial formula ∧
        ∀ index, BasicChild semantics (branch (index + 1)) (branch index) :=
  Stlsat.Tableau.Basic.no_infinite_branch semantics formula

end Stlsat
