/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Tableau.ExpansionCompleteness

/-!
# Shared completeness induction for model-preserving rule sets

For any tableau rule set which preserves a semantic model into at least one
child, a model at the root selects an accepting leaf of a fully developed
finite tree.  The ordinary/basic configuration is an immediate instance of
this common model-guided induction.  JUMP uses a refinement of this traversal
which additionally records target escapes.
-/

namespace Stlsat.Tableau.TableauTree

universe u

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom}

theorem hasAcceptingLeaf_of_model_with
    (rules : Node Atom → List (Node Atom) → Prop)
    (invariant : Node Atom → Prop)
    (tree : TableauTree Atom) (wellFormed : tree.WellFormedWith rules)
    (frontierTerminal : tree.FrontierTerminal semantics)
    (rootInvariant : invariant tree.root)
    (rootModel : tree.root.HasModel semantics)
    (childInvariant : ∀ {node child children}, rules node children →
      invariant node → child ∈ children → invariant child)
    (modeledChild : ∀ {node children}, rules node children →
      invariant node → node.HasModel semantics →
      ∃ child ∈ children, child.HasModel semantics) :
    tree.HasAcceptingLeaf semantics := by
  induction tree with
  | leaf node =>
      simp only [HasAcceptingLeaf]
      simp only [FrontierTerminal] at frontierTerminal
      rcases frontierTerminal with rejected | accepting
      · exact False.elim (Stlsat.ObligationSet.notRejected_of_hasModel rootModel rejected)
      · exact accepting
  | unary node child ih =>
      rcases wellFormed with ⟨rule, childWellFormed⟩
      rcases modeledChild rule rootInvariant rootModel with
        ⟨modeled, modeledMem, childModel⟩
      simp only [List.mem_singleton] at modeledMem
      subst modeled
      have childMem : child.root ∈ [child.root] := by simp
      exact ih childWellFormed frontierTerminal
        (childInvariant rule rootInvariant childMem) childModel
  | binary node left right ihLeft ihRight =>
      rcases wellFormed with ⟨rule, leftWellFormed, rightWellFormed⟩
      rcases frontierTerminal with ⟨leftTerminal, rightTerminal⟩
      rcases modeledChild rule rootInvariant rootModel with
        ⟨modeled, modeledMem, childModel⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at modeledMem
      rcases modeledMem with rfl | rfl
      · exact Or.inl (ihLeft leftWellFormed leftTerminal
          (childInvariant rule rootInvariant (by simp)) childModel)
      · exact Or.inr (ihRight rightWellFormed rightTerminal
          (childInvariant rule rootInvariant (by simp)) childModel)

end Stlsat.Tableau.TableauTree
