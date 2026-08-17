/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Tableau.Basic.Completeness
import Stlsat.Tableau.Basic.Construction
import Stlsat.Jump.Construction

/-!
# STL tableaux

This is the entry point for the unified tableau formalization.

Both modes use the syntax, provenance-aware nodes, ordinary expansion,
acceptance, raw trees, semantic models, termination measure, and generic tree
inductions in `Stlsat.Tableau`.  The configured advancement relations are:

* `Stlsat.Tableau.Basic.Rule`: ordinary expansion and `STEP`;
* `Stlsat.Tableau.Jump.Rule`: the same expansion relation with mutually
  exclusive `STEP`/guarded-`JUMP` advancement.

The soundness and completeness results are
`Stlsat.Tableau.Basic.Development.soundness`,
`Stlsat.Tableau.Basic.Development.completeness`,
`Stlsat.Tableau.Jump.Development.soundness`, and
`Stlsat.Tableau.Jump.Development.completeness`.
Finite developments are supplied by
`Stlsat.Tableau.Basic.Development.exists_of_strictNormalForm` and
`Stlsat.Tableau.Jump.Development.exists_of_strictNormalForm`.
-/
