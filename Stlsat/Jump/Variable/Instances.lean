/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Jump.Variable.Construction

/-!
# Correctness instances for variable-aware JUMP

These corollaries expose the generic correctness theorem at the two concrete
coordinate-local semantics supplied by `AtomicSupport`: propositional
variables and finite-support linear real-arithmetic inequalities.
-/

namespace Stlsat.Tableau.VariableJump.Development

universe w

theorem boolean_soundness {Var : Type w} [DecidableEq Var]
    {formula : Stlsat.Formula Var}
    (tableau : VariableJump.Development (BooleanSemantics Var)
      (booleanAtomicSupport Var).atomSupport formula)
    (accepted : tableau.HasAcceptingBranch) :
    formula.Satisfiable (BooleanSemantics Var) :=
  tableau.soundness (booleanAtomicSupport Var) accepted

theorem boolean_completeness {Var : Type w} [DecidableEq Var]
    {formula : Stlsat.Formula Var}
    (tableau : VariableJump.Development (BooleanSemantics Var)
      (booleanAtomicSupport Var).atomSupport formula)
    (satisfiable : formula.Satisfiable (BooleanSemantics Var)) :
    tableau.HasAcceptingBranch :=
  tableau.completeness (booleanAtomicSupport Var) satisfiable

theorem lra_soundness {Var : Type w} [DecidableEq Var]
    {formula : Stlsat.Formula (LRAAtom Var)}
    (tableau : VariableJump.Development (LRASemantics Var)
      (lraAtomicSupport Var).atomSupport formula)
    (accepted : tableau.HasAcceptingBranch) :
    formula.Satisfiable (LRASemantics Var) :=
  tableau.soundness (lraAtomicSupport Var) accepted

theorem lra_completeness {Var : Type w} [DecidableEq Var]
    {formula : Stlsat.Formula (LRAAtom Var)}
    (tableau : VariableJump.Development (LRASemantics Var)
      (lraAtomicSupport Var).atomSupport formula)
    (satisfiable : formula.Satisfiable (LRASemantics Var)) :
    tableau.HasAcceptingBranch :=
  tableau.completeness (lraAtomicSupport Var) satisfiable

end Stlsat.Tableau.VariableJump.Development
