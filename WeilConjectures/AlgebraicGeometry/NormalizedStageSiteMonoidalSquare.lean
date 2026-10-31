/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeCoefficientExtensionData
public import WeilConjectures.AlgebraicGeometry.EvaluationHomSiteComparison
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
import WeilConjectures.CategoryTheory.DerivedTensorRightExact
import WeilConjectures.Algebra.Homology.WeilSiteDerivedTensorDescent
import WeilConjectures.CategoryTheory.ModulePullbackTensorIso

/-! # The normalized scalar/site monoidal square

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-free-extension.proof.md, paragraphs 1--3.
(blueprint: lem-sf-normalized-stage-site-monoidal-square).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures.FiniteFreeCoefficients.Sites

/-- The canonical scalar/site comparison commutes with the normalized tensorators.
The tensor product of the two comparison components is written using the two actions
of the published derived tensor bifunctor.

Source: latest blueprint, lem-coef-finite-free-extension.proof.md, paragraphs 1--3.
(blueprint: lem-sf-normalized-stage-site-monoidal-square).

Proof: (1) Unpack the fixed comparison data. Both composites have source
S_pro(nu_A(U tensor V)) and target nu_B(S_et U) tensor nu_B(S_et V).
(2) On ordinary sheaves the scalar/site mate and the site tensor comparison commute
with balanced scalar tensor products: both routes send b tensor (m tensor n) to
(b tensor m) tensor (1 tensor n).
(3) Choose flat-term K-flat representatives P and Q. The ordinary square assembles
into the signed total tensor square, with the same Koszul differential on both routes.
The K-flat comparison-normalization statement identifies sigma, both mu components
and both site tensor comparisons with these cochain maps, with the same endpoint
identifications.
(4) Thus the two natural transformations agree after restriction to localized pairs
of flat-term K-flat complexes. Injectivity of this restriction, from derived tensor
descent, gives their equality everywhere. Taking the component at (U,V) gives the
assertion. No boundedness, constructibility, Tor-amplitude or flatness of the ring
map is needed. -/
theorem normalized_stage_site_monoidal_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u})
    (μet : TensorComparison false φ X) (μpro : TensorComparison true φ X)
    (hμet : NormalizedTensor false φ X μet) (hμpro : NormalizedTensor true φ X μpro)
    (U V : D false A X) :
    (scalar true φ X).map
        ((ProEtale.siteComparisonTensorIso (ModuleCat.{u + 1} A) X U).hom.app V) ≫
      μpro.hom.app ((nu A X).obj U, (nu A X).obj V) ≫
      ((tensor true B X).map ((scalarSite φ X).hom.app U)).app
        ((scalar true φ X).obj ((nu A X).obj V)) ≫
      ((tensor true B X).obj ((nu B X).obj ((scalar false φ X).obj U))).map
        ((scalarSite φ X).hom.app V) =
    (scalarSite φ X).hom.app (((tensor false A X).obj U).obj V) ≫
      (nu B X).map (μet.hom.app (U, V)) ≫
      (ProEtale.siteComparisonTensorIso (ModuleCat.{u + 1} B) X
        ((scalar false φ X).obj U)).hom.app ((scalar false φ X).obj V) := by
  sorry

end WeilConjectures.FiniteFreeCoefficients.Sites
