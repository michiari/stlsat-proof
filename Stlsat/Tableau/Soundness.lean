/-
Copyright (c) 2026 Michele Chiari. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Michele Chiari
-/
import Stlsat.Tableau.Semantics

/-!
# Shared soundness induction for tableau rule sets

This module contains the part of tableau soundness which is independent of
the advancement policy.  A rule set supplies two local facts: its invariant is
preserved by children, and a model of a selected child reconstructs a model of
the parent.  The common tree induction then transports an accepting leaf model
back to the root.
-/

namespace Stlsat.Tableau.TableauTree

universe u

variable {Atom : Type u} [DecidableEq Atom]
  {semantics : Stlsat.AtomicSemantics Atom}

/-- Generic backward model construction along an accepting branch. -/
theorem root_hasModel_of_acceptingLeaf_with
    (rules : Node Atom → List (Node Atom) → Prop)
    (invariant : Node Atom → Prop)
    (tree : TableauTree Atom) (wellFormed : tree.WellFormedWith rules)
    (accepting : tree.HasAcceptingLeaf semantics)
    (rootInvariant : invariant tree.root)
    (acceptingModel : ∀ {node}, node.Accepting semantics →
      invariant node → node.HasModel semantics)
    (childInvariant : ∀ {node child children}, rules node children →
      invariant node → child ∈ children → invariant child)
    (parentModel : ∀ {node child children}, rules node children →
      invariant node → child ∈ children → child.HasModel semantics →
      node.HasModel semantics) :
    tree.root.HasModel semantics := by
  induction tree with
  | leaf node => exact acceptingModel accepting rootInvariant
  | unary node child ih =>
      rcases wellFormed with ⟨rule, childWellFormed⟩
      have childMem : child.root ∈ [child.root] := by simp
      have childInv := childInvariant rule rootInvariant childMem
      have childModel := ih childWellFormed accepting childInv
      exact parentModel rule rootInvariant childMem childModel
  | binary node left right ihLeft ihRight =>
      rcases wellFormed with ⟨rule, leftWellFormed, rightWellFormed⟩
      rcases accepting with leftAccepting | rightAccepting
      · have childMem : left.root ∈ [left.root, right.root] := by simp
        have childInv := childInvariant rule rootInvariant childMem
        have childModel := ihLeft leftWellFormed leftAccepting childInv
        exact parentModel rule rootInvariant childMem childModel
      · have childMem : right.root ∈ [left.root, right.root] := by simp
        have childInv := childInvariant rule rootInvariant childMem
        have childModel := ihRight rightWellFormed rightAccepting childInv
        exact parentModel rule rootInvariant childMem childModel

end Stlsat.Tableau.TableauTree
