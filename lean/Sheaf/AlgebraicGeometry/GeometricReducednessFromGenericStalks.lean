/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.RingTheory.TensorProduct.Basic
public import Sheaf.Topology.PresheafModuleStalkFunctor

import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Geometric reducedness from generic stalks

Source: Stacks Project, Varieties, Tags 04KS (3) and 035W
(blueprint: lem-pur-geometric-reducedness-from-generic-stalks).
-/

@[expose] public section

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A reduced scheme over a field is geometrically reduced if every generic stalk of
an irreducible component remains reduced after every field extension.
Source: Stacks Project, Varieties, Tags 04KS (3) and 035W.
(blueprint: lem-pur-geometric-reducedness-from-generic-stalks)

Proof:
1. For an affine open Spec A, each minimal prime gives a generic point of a global
   irreducible component. The affine stalk-localization theorem identifies its stalk with
   A localized at that prime, as a k-algebra. Thus every such localization tensor L is reduced.
2. The maps from the reduced ring A to its minimal-prime localizations jointly detect zero:
   each kernel is its minimal prime, and the intersection of these primes is the nilradical.
3. After tensoring with L these maps still jointly detect zero. Express a tensor using finitely
   many linearly independent coefficients in L, extend them to a basis, and apply the coordinate
   functionals. Every coefficient vanishes in all minimal-prime localizations, hence is zero.
   A nilpotent tensor has zero image in each reduced localization tensor L, so it is zero.
4. The affine fibre-product theorem identifies the base change of Spec A with Spec (A tensor L).
   Open immersions are stable under base change, so these reduced affine charts cover the base
   change of X. Their localizations, hence all its stalks, are reduced. Thus the base change is
   reduced for every L, as required. The empty scheme causes no exception.

The algebra structure on a stalk is bound with its defining equality to the composite
k → O(Spec k, p(x)) → O(X, x), so that the tensor uses the given structure morphism. -/
theorem geometricallyReduced_of_generic_stalks
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsReduced X]
    (h : ∀ (Z : Set X), Z ∈ irreducibleComponents X →
      ∀ (ξ : X), IsGenericPoint ξ Z →
      ∀ (L : Type u) [Field L] [Algebra k L] [Algebra k (X.presheaf.stalk ξ)],
        algebraMap k (X.presheaf.stalk ξ) =
          (StructureSheaf.toStalk k ((X ↘ Spec (.of k)) ξ) ≫
            (X ↘ Spec (.of k)).stalkMap ξ).hom →
        _root_.IsReduced ((X.presheaf.stalk ξ) ⊗[k] L)) :
    GeometricallyReduced (X ↘ Spec (.of k)) := by
  sorry

end AlgebraicGeometry
