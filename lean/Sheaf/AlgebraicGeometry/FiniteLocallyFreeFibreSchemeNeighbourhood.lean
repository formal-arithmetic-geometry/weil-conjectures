/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.SpaceInvariantOpenQuotient
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenFactorSchemeTests
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus

/-! # Scheme neighbourhoods detected by affine fibre neighbourhoods

Source: Stacks Project, Decent Spaces, Tag 0BA1, lemma-when-quotient-scheme-at-point
(blueprint: lem-sfb-finite-locally-free-fibre-scheme-neighbourhood).

Schemeness of an open subspace is expressed by an isomorphism of its subfunctor with a
scheme's Yoneda presheaf. The fibre condition is quantified over all field-valued point
representatives, using the existing point classes and their functorial images.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A point downstairs has a scheme open neighbourhood if and only if its entire fibre
lies in an affine open upstairs, for a representable surjective finite locally free map.
Source: Stacks Project, Decent Spaces, Tag 0BA1, lemma-when-quotient-scheme-at-point
(blueprint: lem-sfb-finite-locally-free-fibre-scheme-neighbourhood).

Proof:
1. From a scheme open neighbourhood choose an affine open neighbourhood of the point
   (def-pc-scheme). Its inverse image is finite locally free, hence finite and affine over
   an affine scheme (def-pc-finite-locally-free, def-weil-finite-integral-morphism,
   pqf-def-affine-morphism). By lem-a1-space-open-factor-scheme-tests it is an open subspace
   upstairs containing the whole fibre.
2. Conversely, let C be the closed complement of the given affine open upstairs. Its image
   is closed by lem-sfb-finite-space-morphism-topology. The complement O of that image is
   open and contains the point. Choose an atlas using def-trf-algebraic-space and apply
   lem-a1-space-invariant-open-quotient to obtain an open subspace N with point set O.
   The openness of the original point image uses lem-a1-space-point-open-calculus.
   Every point mapping into N belongs to the given affine open by construction.
3. By lem-a1-space-open-factor-scheme-tests the inverse image W of N factors through that
   affine open and is an open subscheme of it (def-a1-space-open-subspace). Each scheme
   test of W over N is the original scheme test of p, by the fibre-product universal
   property, and is thus surjective finite locally free. The point-surjectivity criterion
   of lem-a1-space-point-open-calculus applies. The descent criterion
   lem-sfb-finite-locally-free-open-affine-cover makes N a scheme. -/
theorem finiteLocallyFree_fibre_scheme_neighbourhood_iff {S : Scheme.{u}}
    (E B : AlgebraicSpace S) (p : E ⟶ B)
    (hp : IsRepresentableWith
      (fun _ _ q ↦ Surjective q.left ∧ q.left.IsFiniteLocallyFree) p.hom.hom)
    (b : Point B.obj.obj) :
    (∃ N : OpenSubspace B, b ∈ pointImage N.val.ι ∧
      ∃ T : Over S, Nonempty (N.val.toFunctor ≅ yoneda.obj T)) ↔
    (∃ A : OpenSubspace E,
      (∃ T : Over S, IsAffine T.left ∧ Nonempty (A.val.toFunctor ≅ yoneda.obj T)) ∧
      ∀ e : PointRepresentative E.obj.obj,
        Quot.mk _ (e.map p.hom.hom) = b → Quot.mk _ e ∈ pointImage A.val.ι) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
