/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import Sheaf.Algebra.Homology.AffineDerivedBaseChangeComparison
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.DerivedCategory
import Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh

/-! # The affine single-complex base-change criterion

Source: Stacks Project, Tag 0DJ8, affine proof, and Tag 0DJ9
(blueprint: lem-pc-rf-single-complex-affine-base-change).

The affine case of the single-complex criterion, stated with the objects of the
qcqs statement `singleComplexBaseChangeQcqsInduction`: a cartesian square of the
spectra S = Spec R, X = Spec A, S' = Spec R', X' = Spec A', objects K, K' of the
quasi-coherent derived categories (which correspond to complexes M, N of A- and
A'-modules under the affine equivalence), a derived morphism L(g')^*K -> K', the
stalkwise condition `SingleComplexBaseChange.StalkCondition`, and the derived
base-change comparison map followed by Rf'_* of the given morphism.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Stacks, Tag 0DJ8, affine proof (and the affine case of Tag 0DJ9).
(blueprint: lem-pc-rf-single-complex-affine-base-change)

For a cartesian square of affine schemes X = Spec A, S = Spec R, S' = Spec R',
X' = Spec A', objects K, K' of the quasi-coherent derived categories and a morphism
φ : L(g')^*K -> K', if the stalk maps
H^i(K_x ⊗^L_{O_{S,s}} O_{S',s'}) ⊗ O_{X',x'} -> H^i(K'_{x'}) are isomorphisms for all
x' and i, then the comparison Lg^*Rf_*K -> Rf'_*L(g')^*K -> Rf'_*K' is an isomorphism.

Proof, following the four steps of the node:
1. Write A' = A ⊗_R R'. Under the affine quasi-coherent derived equivalence
   (lem-pc-affine-qcoh-derived-equivalence, lem-pc-derived-direct-image-preserves-qcoh)
   K and K' correspond to complexes M of A-modules and N of A'-modules, and by
   lem-pc-affine-derived-pullback-tensor-tilde the comparison is represented by
   M ⊗^L_R R' -> M ⊗^L_A A' -> N in D(R'), whose first arrow is the comparison of
   lem-pc-affine-derived-base-change-comparison-map.
2. φ corresponds to M ⊗^L_A A' -> N in D(A'); composing with the comparison c, whose
   cohomology maps are A'-linear, gives A'-linear maps H^i(M ⊗^L_R R') -> H^i(N).
3. Localize at a prime x' of A'. The localization identities of
   lem-pc-affine-derived-base-change-comparison-map identify the localized first arrow;
   exact localization (lem-weil-pbc-localization-module-exact) and affine tilde stalks
   (lem-weil-pbc-spec-tilde-stalk-localization) identify the localized second arrow;
   the localized composite is the stalk map of the hypothesis.
4. Every maximal ideal is prime, so each H^i of the composite is bijective at every
   maximal localization, hence bijective
   (lem-weil-pbc-linear-map-bijective-at-maximal-localizations); the composite is a
   quasi-isomorphism, i.e. an isomorphism in D(R') (def-pc-derived-category). -/
theorem singleComplexAffineBaseChange
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    (φf : R →+* A) (φg : R →+* R') (φg' : A →+* A') (φf' : R' →+* A')
    (sq : IsPullback (Spec.map (CommRingCat.ofHom φg')) (Spec.map (CommRingCat.ofHom φf'))
      (Spec.map (CommRingCat.ofHom φf)) (Spec.map (CommRingCat.ofHom φg)))
    (K : schemeDerivedCategory (Spec (.of A)))
    (hK : schemeDerivedQCohProperty (Spec (.of A)) K)
    (K' : schemeDerivedCategory (Spec (.of A')))
    (hK' : schemeDerivedQCohProperty (Spec (.of A')) K')
    (φ : (derivedPullback (Spec.map (CommRingCat.ofHom φg'))).obj K ⟶ K')
    (h_stalk : SingleComplexBaseChange.StalkCondition (Spec.map (CommRingCat.ofHom φf))
      (Spec.map (CommRingCat.ofHom φf')) (Spec.map (CommRingCat.ofHom φg))
      (Spec.map (CommRingCat.ofHom φg')) sq K K' φ) :
    IsIso (schemeDerivedBaseChangeMap (Spec.map (CommRingCat.ofHom φf))
        (Spec.map (CommRingCat.ofHom φf')) (Spec.map (CommRingCat.ofHom φg))
        (Spec.map (CommRingCat.ofHom φg')) sq.w K ≫
      (schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φf'))).map φ) := by
  sorry

end AlgebraicGeometry
