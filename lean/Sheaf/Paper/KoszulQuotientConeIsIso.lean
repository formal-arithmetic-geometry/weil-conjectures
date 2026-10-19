/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.Paper.IntrinsicKoszulCompletion
public import Sheaf.Paper.CompletionMap
import Sheaf.RingTheory.NoetherianKoszulAugmentationProZero
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients

/-! # Invertibility of the explicit Koszul quotient cone comparison

Source: Stacks Project, Tags 0922 and 0941; blueprint order 1259, steps 1--4.
(blueprint: new-s3-koszul-quotient-cone-is-iso).
-/

@[expose] public section

universe t
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

/-- A map with the quotient augmentation in both product-cone coordinates becomes
invertible after localization. No choice of a triangle filler is involved.

Source: Stacks Project, Tags 0922, 06YU and 0941; blueprint order 1259, steps 1--4.
(blueprint: new-s3-koszul-quotient-cone-is-iso).

Proof: apply noetherian_koszul_augmentation_pro_zero to the lifted coefficient ring
and the lifted generators, identifying its span ideal with the lift of d.ideal and
using the canonical lifted-ring quotient equivalence. The given unit equation and
vanishing on all other total-tensor summands identify v
with the sheafified tensor of the quotient augmentation: the degree-zero Koszul unit
is an isomorphism, so these equations determine each summand. Exact constant-module
sheafification sends the derived zero maps between augmentation cones to zero maps.
Tensor with the K-flat complex M.complex; its flat terms compute derived tensor.
The tensor of an augmentation cone identifies with the cone of v by distributing
over its two summands and multiplying the shifted-source summand in tensor degree p
by (-1)^p. K-flatness preserves acyclic complexes and hence quasi-isomorphisms;
therefore the cone transitions of v are eventually zero in the derived category.
Apply ringedStrictTowerHomotopyLimit to the strict tensor towers and v. Its pro-zero
cone criterion makes the total derived-limit map invertible. Countable products of
pro-etale module sheaves are exact by countableProducts_exact; localization of the
termwise product thus computes the derived product.

For the map comparison, use the strict Roos functor T ↦ Cocone(1-shift_T), with both
coordinates of its action given by the product of the level maps. Exact products make
this functor preserve quasi-isomorphisms. Resolve strict towers by K-injective complexes
with injective tower terms, using grothendieckAbelian_and_functorial_kInjective_resolutions
on the tower site. An injective tower has split epimorphic transitions: extend its
identity at level n along the monomorphism from the finite constant prefix through n
to the prefix through n+1. In each complex degree choose these sections σ_n. The recursion
y_0=0, y_(n+1)=σ_n(y_n-x_n) shows 1-shift is surjective, and its kernel is the strict
inverse limit. Thus the natural map from the strict inverse-limit complex to its Roos
cocone is a quasi-isomorphism on these resolutions. The right-derived universal property
identifies the localized strict Roos functor naturally with RF. It identifies the map
with the product of v in both coordinates with RF applied to v. Finally the two given
coordinate equations identify w with that strict Roos map, since the projections jointly
determine every degree component. This proves invertibility of Q(w), without choosing
an unrelated filler between triangles.
For r=0 the coefficient augmentation is an isomorphism and its cone is acyclic;
for the zero ring all complexes are zero. Neither case requires a separate bound. -/
theorem koszulQuotientCone_isIso (X : Scheme.{t}) (Λ : Type t) [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) (r : ℕ) (f : Fin r → Λ)
    (hf : Ideal.span (Set.range f) = d.ideal)
    (K : proEtaleDerivedCategory X Λ) (M : AdicKFlatModel X Λ K)
    (v : ∀ n, koszulTensor X Λ r f M.complex n ⟶ adicReductionComplex X d M n)
    (hunit : ∀ n, koszulTensorUnit X Λ r f M.complex n ≫ v n =
      adicReductionAugmentation X d M n)
    (hzero : ∀ (n : ℕ) (p q : ℤ), q ≠ 0 →
      HomologicalComplex.ιMapBifunctor M.complex (koszulPowerSheaf X Λ r f n)
        (@curriedTensor _ _ (SheafOfModules.monoidalCategory (adicConstantRing X Λ)))
        (ComplexShape.up ℤ) p q (p + q) rfl ≫ (v n).f (p + q) = 0)
    (hstep : ∀ n, v (n + 1) ≫ adicReductionComplexStep X d M n =
      koszulTensorTransition X Λ r f M.complex n ≫ v n)
    (w : koszulCompletionComplex X Λ r f M.complex ⟶ adicCompletionComplex X d M)
    (hfst : w ≫ adicCompletionProjection X d M =
      CochainComplex.mappingCocone.fst (koszulOneSubShift X Λ r f M.complex) ≫
        Limits.Pi.map v)
    (hsnd : ∀ p : ℤ, w.f p ≫
      (CochainComplex.mappingCocone.snd (𝟙 _ - adicReductionProductShift X d M)).v
        p (p + -1) rfl =
      (CochainComplex.mappingCocone.snd (koszulOneSubShift X Λ r f M.complex)).v
        p (p + -1) rfl ≫ (Limits.Pi.map v).f (p + -1)) :
    IsIso ((adicLocalization X Λ).map w) := by
  sorry

end
end AlgebraicGeometry.Scheme
