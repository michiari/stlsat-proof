/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Tableau.Basic.Soundness
import Stlsat.Tableau.Completeness

/-!
# Completeness of the basic rule configuration

The only local fact needed here is that a model selects a modeled child of an
ordinary expansion or survives one `STEP`.  The finite-tree traversal itself
is shared by all model-preserving rule sets.
-/

namespace Stlsat.Tableau.Basic

universe u

namespace Rule

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom}

theorem exists_child_hasModel {node : Stlsat.Tableau.Node Atom}
    {children : List (Stlsat.Tableau.Node Atom)}
    (rule : Rule semantics node children)
    (invariant : node.Timely ∧ node.InStrictNormalForm)
    (model : node.HasModel semantics) :
    ∃ child ∈ children, child.HasModel semantics := by
  cases rule with
  | expand _ expansion => exact expansion.exists_child_hasModel model
  | step _ poised _ =>
      exact ⟨node.step, by simp,
        Stlsat.Tableau.Node.hasModel_step_of_hasModel poised invariant.1 model⟩

end Rule

namespace Development

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom} {formula : Stlsat.Formula Atom}

theorem hasAcceptingBranch_of_hasModel (tableau : Development semantics formula)
    (model : formula.HasModel semantics) : tableau.HasAcceptingBranch := by
  have rootInvariant :
      tableau.tree.root.Timely ∧ tableau.tree.root.InStrictNormalForm := by
    rw [tableau.rooted_at]
    exact ⟨Stlsat.Tableau.Node.initial_timely formula,
      Stlsat.Tableau.Node.initial_normal tableau.root_normal⟩
  have rootModel : tableau.tree.root.HasModel semantics := by
    change tableau.tree.root.erase.HasModel semantics
    rw [tableau.rooted_at, Stlsat.Tableau.Node.erase_initial]
    exact model
  exact Stlsat.Tableau.TableauTree.hasAcceptingLeaf_of_model_with
    (Rule semantics) (fun node => node.Timely ∧ node.InStrictNormalForm)
    tableau.tree tableau.wellFormed tableau.frontier_terminal rootInvariant rootModel
    (fun rule invariant childMem => rule.child_invariant invariant childMem)
    (fun rule invariant parentModel => rule.exists_child_hasModel invariant parentModel)

/-- Completeness of the basic tableau, instantiated from the shared
model-guided tree induction. -/
theorem completeness (tableau : Development semantics formula)
    (satisfiable : formula.Satisfiable semantics) : tableau.HasAcceptingBranch :=
  tableau.hasAcceptingBranch_of_hasModel
    ((Stlsat.Formula.satisfiable_iff_hasModel formula semantics).mp satisfiable)

end Development

end Stlsat.Tableau.Basic
