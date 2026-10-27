/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.PicardFunctor
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.StablePointedCurve
import Sheaf.Combinatorics.FiniteGraphHomologyRigidity
import WeilConjectures.AlgebraicGeometry.DensePoints

/-! # Faithfulness of the full Picard-zero action of a stable curve

Source: Deligne--Mumford, The irreducibility of the space of curves of given genus,
Theorem 1.13 and Lemmas 1.14--1.17, printed pp. 85--87
(blueprint: lem-sfb-stable-picard-action-faithful).

Degree zero is imposed on every reduced component after its canonical normalization.
The Picard classes and their pullback are the existing scheme Picard construction.
The base equality selects a family over the field itself from the moduli category.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A field automorphism of an unpointed stable curve that fixes every multidegree-zero
Picard class is the identity, including for singular and reducible curves.

Source: Deligne--Mumford, Theorem 1.13 and Lemmas 1.14--1.17, printed pp. 85--87
(blueprint: lem-sfb-stable-picard-action-faithful).

Proof:
1. By `lem-sfb-nodal-component-picard-gluing`, restriction onto the product of the
   component Picard-zero groups is surjective and equivariant. A class supported on
   one factor shows that every component with nontrivial Picard-zero group is fixed.
2. A moved component has trivial Picard-zero group, hence is a smooth rational curve
   by the same gluing lemma. Stability requires at least three distinct intersection
   points on it. Thus every vertex of degree at most two is fixed.
3. Equivariance of the gluing torus makes the graph action trivial on all characters
   of its integral cycle lattice. Characters separate this lattice: for a nonzero
   integer coordinate n, choose a field unit z with z^n different from one, possible
   since an algebraically closed field is infinite. Hence the graph action is the
   identity on integral cycles. `lem-sfb-finite-graph-homology-rigidity` now fixes all
   components and all intersection nodes.
4. Restriction surjectivity implies identity on each component Picard-zero group.
   By `lem-sfb-integral-nodal-picard-normalization-action`, the lifted automorphism
   on each normalization fixes its Picard-zero group and all self-node branches.
   The unique preimage of each intersection node is fixed as well.
5. For a normalized component of genus at least two, `sk-thm-picard-main` gives its
   smooth separated Jacobian. Its rational points are dense by
   `lem-pc-rational-points-dense`. The equalizer of the induced automorphism with
   identity is closed and contains these points. Reducedness makes that equalizer
   the whole Jacobian. `lem-sfb-curve-polarized-jacobian-faithfulness` therefore
   makes the normalized component automorphism the identity.
6. For genus one, stability supplies a fixed special point; for genus zero, it
   supplies three distinct fixed special points. Apply the respective clauses of
   `lem-sfb-low-genus-pointed-automorphism-rigidity` to obtain identity in both cases.
7. The normalization is surjective, so the original automorphism fixes all points.
   On any affine open, functions inject into the product of the function fields
   of its reduced components: their common kernel is the nilradical, which is zero.
   Identity on the normalizations consequently implies identity on functions and
   hence on the scheme. No characteristic or automorphism-order restriction enters. -/
theorem stablePicardActionFaithful
    (k : Type u) [Field k] [IsAlgClosed k] (g : ℕ)
    (C : StablePointedModuli (Spec (.of k)) g 0)
    (_hbase : C.base = Over.mk (𝟙 (Spec (.of k))))
    (a : C.curve ≅ C.curve)
    (_ha : a.hom ≫ C.projection ≫ C.base.hom = C.projection ≫ C.base.hom)
    (_hpic : ∀ L : C.curve.Pic,
      (∀ Z : irreducibleComponents C.curve,
        (C.curve.normalizedComponentMap Z ≫ C.projection ≫ C.base.hom).picDegree
          (Scheme.Pic.map (C.curve.normalizedComponentMap Z) L) = 0) →
      Scheme.Pic.map a.hom L = L) :
    a = Iso.refl C.curve := by
  sorry

end AlgebraicGeometry
