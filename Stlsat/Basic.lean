/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Basic.Tableau
import Stlsat.Basic.Termination
import Stlsat.Basic.Soundness
import Stlsat.Basic.Completeness
import Stlsat.Tableau.Basic.Construction

/-!
# The basic STL tableau

This is the compatibility umbrella for the basic configuration of the shared
tableau core. It exports construction, termination, soundness, and completeness
for ordinary expansion and `STEP`, without JUMP-specific guards.
-/
