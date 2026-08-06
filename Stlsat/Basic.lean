/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Basic.Tableau
import Stlsat.Basic.Termination
import Stlsat.Basic.Soundness
import Stlsat.Basic.Completeness

/-!
# The basic STL tableau

This is the umbrella module for the basic tableau without the `JUMP` rule. It
exports the tableau definition together with its termination, soundness, and
completeness proofs.
-/
