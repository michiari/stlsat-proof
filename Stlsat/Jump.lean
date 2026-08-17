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
