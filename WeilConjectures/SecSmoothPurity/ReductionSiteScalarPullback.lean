/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.ReductionExceptionalObjects

/-! # Intrinsic scalar/site/inverse-image cube -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- Scalar extension, site comparison and inverse image have the same normalized
composite. Source: blueprint latest, reduction-exceptional proof, Charts, comparison
of sites and coefficients (blueprint: lem-sp-reduction-site-scalar-pullback).

Proof: first work in fixed ModuleCat-valued sheaves. The scalar/site/pullback cube
is etaleProEtale_scalar_pullback_cube. Transport that cube through the intrinsic
module equivalences. The realization scalar arrow is the inverse mate of exact
restriction of scalars, while the realization inverse-image arrow is the derived
section-normalized openSquarePullbackModel. The two restriction squares commute
sectionwise, since both send a section and its coefficient to their identical
pullbacks. Taking their inverse mates and descending exact functors to the derived
categories identifies the transported cube with the displayed equation. Finally
use the exact-to-left-derived ordinary pullback isomorphism on both coefficient
sides. No boundedness, smoothness or choice of orientation is used. -/
theorem reductionSite_scalar_pullback
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {U X : Scheme.{u}} (i : U ⟶ X)
    (L : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) X) :
    (directImageScalarPullbackIso φ i).inv.app ((reductionSite A X).obj L) ≫
        (proEtaleConstantRingDerivedPullback B i).map
          ((reductionSiteScalarIso φ X).hom.app L) ≫
        (reductionSitePullbackIso B i).hom.app
          ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj L) =
      (scalarExtensionFunctor φ U).map ((reductionSitePullbackIso A i).hom.app L) ≫
        (reductionSiteScalarIso φ U).hom.app
          ((Etale.ordinaryFinitePullback (ULift.{u + 1, u} A) i).obj L) ≫
        (reductionSite B U).map
          ((Etale.scalarPullbackIso (RingHom.ulift.{u + 1, u + 1, u, u} φ) i).inv.app L) := by
  sorry

end AlgebraicGeometry.ProEtale
