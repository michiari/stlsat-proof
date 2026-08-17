/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Tableau.Basic
import Stlsat.Tableau.Soundness

/-!
# Soundness of the basic rule configuration

Only the local rule facts are basic-specific.  Backward propagation along an
accepting branch is the generic induction from `Stlsat.Tableau.Soundness`.
-/

namespace Stlsat.Tableau.Basic

universe u

namespace Rule

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom}

theorem child_invariant {node child : Stlsat.Tableau.Node Atom}
    {children : List (Stlsat.Tableau.Node Atom)}
    (rule : Rule semantics node children)
    (invariant : node.Timely ∧ node.InStrictNormalForm)
    (childMem : child ∈ children) :
    child.Timely ∧ child.InStrictNormalForm := by
  rcases invariant with ⟨timely, normal⟩
  cases rule with
  | expand _ expansion =>
      exact ⟨expansion.child_timely timely childMem,
        expansion.child_normal normal childMem⟩
  | step _ poised _ =>
      simp only [List.mem_singleton] at childMem
      subst child
      exact ⟨Stlsat.Tableau.Node.step_timely timely poised,
        Stlsat.Tableau.Node.step_normal normal⟩

theorem hasModel_parent_of_child {node child : Stlsat.Tableau.Node Atom}
    {children : List (Stlsat.Tableau.Node Atom)}
    (rule : Rule semantics node children)
    (invariant : node.Timely ∧ node.InStrictNormalForm)
    (childMem : child ∈ children)
    (childModel : child.HasModel semantics) : node.HasModel semantics := by
  rcases invariant with ⟨timely, normal⟩
  cases rule with
  | expand _ expansion =>
      rcases childModel with ⟨⟨signal, childSatisfied⟩⟩
      exact ⟨⟨signal, expansion.satisfiedBy_parent childMem childSatisfied⟩⟩
  | step notRejected poised _ =>
      simp only [List.mem_singleton] at childMem
      subst child
      exact Stlsat.Tableau.Node.hasModel_of_step notRejected poised timely normal childModel

end Rule

namespace Development

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom} {formula : Stlsat.Formula Atom}

theorem hasModel_of_acceptingBranch (tableau : Development semantics formula)
    (accepted : tableau.HasAcceptingBranch) : formula.HasModel semantics := by
  have rootInvariant :
      tableau.tree.root.Timely ∧ tableau.tree.root.InStrictNormalForm := by
    rw [tableau.rooted_at]
    exact ⟨Stlsat.Tableau.Node.initial_timely formula,
      Stlsat.Tableau.Node.initial_normal tableau.root_normal⟩
  have rootModel := Stlsat.Tableau.TableauTree.root_hasModel_of_acceptingLeaf_with
    (Rule semantics) (fun node => node.Timely ∧ node.InStrictNormalForm)
    tableau.tree tableau.wellFormed accepted rootInvariant
    (fun accepting invariant =>
      Stlsat.Tableau.Node.hasModel_of_accepting accepting invariant.1 invariant.2)
    (fun rule invariant childMem => rule.child_invariant invariant childMem)
    (fun rule invariant childMem childModel =>
      rule.hasModel_parent_of_child invariant childMem childModel)
  change tableau.tree.root.erase.HasModel semantics at rootModel
  rw [tableau.rooted_at, Stlsat.Tableau.Node.erase_initial] at rootModel
  exact rootModel

/-- Soundness of the basic tableau, instantiated from the shared tableau
soundness induction. -/
theorem soundness (tableau : Development semantics formula)
    (accepted : tableau.HasAcceptingBranch) : formula.Satisfiable semantics :=
  (Stlsat.Formula.satisfiable_iff_hasModel formula semantics).mpr
    (tableau.hasModel_of_acceptingBranch accepted)

end Development

end Stlsat.Tableau.Basic
