/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E6
-/
module

public import Sheaf.Paper.QcqsOpenClosedTree
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import all Sheaf.Paper.QcqsLatticeTreeReconstruction

/-! # Finite extensions from the leaves of an open-closed tree

Source: Stacks Tag 09AH, iterated along a finite tree.
(blueprint: lem-sfb-qcqs-tree-finite-extensions)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [-instance] WeilConjectures.SixFunctors.integralModel_coefficientMonObj in
/-- Exact functors carry a module to a finite extension of its supported leaf
restrictions. No coefficient admissibility, flatness or leaf lattice is required.

Source: Stacks Tag 09AH; the coefficient-independent reconstruction argument of
lem-sfb-qcqs-lattice-tree-reconstruction.
(blueprint: lem-sfb-qcqs-tree-finite-extensions)

Proof: at an internal vertex apply the exact functor to the open-closed short
exact sequence and pass to its distinguished triangle of degree-zero objects.
Induct on the two subtrees and concatenate their finite extension products.
At a leaf the extension product has length zero. Pullback compositors identify
nested restrictions with restriction along the actual path. The existing proved
`LatticeTree.tree_reconstruct` implements precisely this argument. -/
theorem qcqs_tree_finite_extensions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {D : Type v} [Category.{w} D] [Abelian D] [HasDerivedCategory D]
    {X : Scheme.{u}} (tree : QcqsOpenClosedTree X)
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X) ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : ObjectProperty (DerivedCategory D)) [P.IsClosedUnderIsomorphisms]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hleaf : ∀ (S : Scheme.{u}) (p : tree.Path S), p.IsLeaf →
      P ((DerivedCategory.singleFunctor D 0).obj
        (F.obj ((p.extension Λ).obj ((CondensedRing.upperStar Λ p.toRoot).obj M))))) :
    ∃ n : ℕ, P.extensionProductIter n ((DerivedCategory.singleFunctor D 0).obj (F.obj M)) := by
  exact LatticeTree.tree_reconstruct Λ tree F P M
    (fun w ↦ hleaf w.1 w.2.1 w.2.2)

end AlgebraicGeometry.ProEtale
