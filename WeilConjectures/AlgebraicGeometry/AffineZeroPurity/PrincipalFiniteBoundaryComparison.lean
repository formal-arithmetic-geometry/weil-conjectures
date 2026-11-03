/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PrincipalSupportBoundary
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceCoordinateBoundaries
public import WeilConjectures.AlgebraicGeometry.KummerLocalizationSpliceDefs
public import WeilConjectures.EtaleCohomology.TateTwist.KummerLevelIndependence

/-! # Localization transport for the principal Kummer boundary

Source: finite étale-origin transport, step 4 of
`literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
cor-pur-affine-space-zero-section-purity.md`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry WeilConjectures
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.AffineZeroPurity

/-- Transport the actual principal-support boundary to the ordinary finite-site
localization splice. The input hκ supplies only the unit-class comparison; the
coefficient connecting arrow, open adjunction and closed source are transported here.

Source: step 4 of cor-pur-affine-space-zero-section-purity, compatibility of the
finite étale-origin comparison with connecting maps and the specified Tate targets.
(blueprint: lem-pur-principal-finite-boundary-comparison).

Proof: root normalization he and the scalar-extension adjunction identify the
pullback of e with the root-normalized line pullback in t. Apply the single-degree
and site-interchange comparisons to this identity. Transpose hκ along the exact
open extension-by-zero adjunction. The site-interchange mate preserves its counit,
so the resulting arrow is exact comparison of finiteKummerOpenClass, with the
constant pullback isomorphism included. The short exact coefficient sequence is
carried to the pro-étale coefficient sequence: its middle comparison is the identity,
its right comparison is the closed direct-image exchange, and its left comparison
is the open extension-by-zero mate. These three maps commute with restriction and
the open counit. Naturality of the single-degree connecting morphism gives equality
of the splices. Finally commute the two shifts through the exact comparison, cancel
the single-degree isomorphisms and use shift addition 1+1=2. This gives the displayed
identity with precisely the target comparison used in the statement module.
No Cartier condition is needed. A unit or nilpotent f and an empty X are covered
by the same exact coefficient sequence. -/
theorem principalSupportBoundary_finiteComparison
    (P : PurityFiniteSetting.{u}) (N : ℕ) (hA : (N : P.Coefficient) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient N hA)
    (e : ∀ X : Scheme.{u}, Scheme.finiteEtaleTateLine X N P.Coefficient hA ≅
      (Etale.extendScalars P.Coefficient X).obj (X.rootsOfUnitySheaf N))
    (he : ∀ X : Scheme.{u}, Etale.ordinaryFiniteRootMap P.Coefficient N hA X ≫
      (Etale.moduleAbelianForget P.Coefficient X).map (e X).hom =
        (Etale.extendScalarsAdjunction P.Coefficient X).unit.app (X.rootsOfUnitySheaf N))
    (hκ : ∀ (W : Scheme.{u}) (aW : W ⟶ Spec (.of P.field.k))
        (hW : IsUnit (N : Γ(W, ⊤))) (s : Γ(W, ⊤)ˣ),
      letI := P.coefficientNeZero
      letI := P.coefficientHasInvertibleExponent W aW
      let v := Etale.tateTwistObjectIsoSingleFunctor P.Coefficient W 1 ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          (e W ≪≫ Etale.extendScalarsRootsOfUnityIsoTateTwistSheaf
            P.Coefficient N hA hW).symm
      (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) W).hom ≫
        P.kummerClass W aW s ≫ v.hom⟦(1 : ℤ)⟧' =
          (Etale.finiteKummerUnitClass P.Coefficient N hA W hW s).hom)
    (X : Scheme.{u}) (aX : X ⟶ Spec (.of P.field.k))
    (hX : IsUnit (N : Γ(X, ⊤))) (f : Γ(X, ⊤)) :
    letI := P.coefficientNeZero
    letI := P.coefficientHasInvertibleExponent X aX
    let v := Etale.tateTwistObjectIsoSingleFunctor P.Coefficient X 1 ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        (e X ≪≫ Etale.extendScalarsRootsOfUnityIsoTateTwistSheaf
          P.Coefficient N hA hX).symm
    let F := VectorIntegrationSite.comparison P.Coefficient X
    P.principalSupportBoundary X aX f ≫
      ((F.commShiftIso (2 : ℤ)).app _).inv ≫ F.map (v.hom⟦(2 : ℤ)⟧') =
      realizeBoundary P.Coefficient (X.zeroLocusSubschemeι {f})
        (P.constantEtale (X.zeroLocusSubscheme {f}))
        (Scheme.finiteEtaleTateLine X N P.Coefficient hA)
        (Etale.finiteKummerLocalizationBoundary P.Coefficient N hA t
          (X.zeroLocusSubschemeι {f}) (X.basicOpen f)
          (by rw [Scheme.range_zeroLocusSubschemeι_singleton, Scheme.Opens.range_ι])
          hX (X.basicOpenUnit f)) := by sorry

end AlgebraicGeometry.ProEtale.AffineZeroPurity
