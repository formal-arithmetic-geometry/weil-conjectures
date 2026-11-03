/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.KummerClass
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PrincipalClosedOpenDatum
public import WeilConjectures.AlgebraicGeometry.SupportedCohomologyHomSpecified
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFramePrincipalBoundary
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import WeilConjectures.EtaleCohomology.TateTwist.KummerClass.TwistPullback

/-! # Principal-support boundaries with finite coefficients

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
def-pur-frame-class.md, the individual factors alpha_j = boundary(kappa(f_j))
(blueprint: def-pur-frame-principal-boundary).

We use the ordinary finite-coefficient presentation: the pro-etale Tate object is the
canonical inverse image of the etale Tate object. The finite Tate site comparison identifies
this with the pulled-back condensed finite-coefficient twist. The boundary is the connecting
map for the actual coefficient sequence j_! A_W -> A_X -> i_* A_D. Its single-degree boundary
is the supported-Hom presentation of the kernel-of-restriction connecting map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

/-- The finite pro-etale Tate object in its canonical etale-descent presentation.
The sheaf underlying the etale object is mu_(char A) tensor A; its canonical finite-level
comparisons identify it with mu_(ell^n) tensor A. Inverse image and finite Tate descent give
A(1)_X, with its ordinary constant A_X action. No choice of a generator is involved.
Source: def-pur-frame-class, individual finite-coefficient factors
(blueprint: def-pur-frame-principal-boundary). -/
def principalSupportTate (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj
    (@Etale.tateTwistObject P.Coefficient (coefficientCommRing P) (coefficientNeZero P) X 1)

/-- The Kummer class of a unit, followed by the canonical exact site inverse image.
On Hom from the coefficient unit this is precisely the adjunction-unit global-cohomology
comparison, with the finite Tate identification. The input is the recorded pur9 class.
Source: def-pur-frame-class, the class kappa(f_j) on the complement
(blueprint: def-pur-frame-principal-boundary). -/
def principalSupportKummer (P : PurityFiniteSetting.{u}) (W : Scheme.{u})
    (aW : W ⟶ Spec (.of P.field.k)) (t : Γ(W, ⊤)ˣ) :
    (DerivedCategory.singleFunctor _ 0).obj (P.constant W) ⟶
      (P.principalSupportTate W)⟦(1 : ℤ)⟧ :=
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) W
  (F.mapDerivedCategorySingleFunctor 0).inv.app (P.constantEtale W) ≫
    F.mapDerivedCategory.map (Etale.singleFunctorObjUnitIso
      (ModuleCat.{u + 1} P.Coefficient) W).hom ≫
    F.mapDerivedCategory.map (P.kummerClass W aW t) ≫
    (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _

/-- Pullback of the finite Tate object, using the canonical site interchange and the
root-normalized etale Tate pullback. Source: def-pur-frame-class, restriction to X_f
(blueprint: def-pur-frame-principal-boundary). -/
def principalSupportTatePullback (P : PurityFiniteSetting.{u}) {W X : Scheme.{u}}
    (j : W ⟶ X) (aX : X ⟶ Spec (.of P.field.k)) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) j).mapDerivedCategory.obj
      (P.principalSupportTate X) ≅ P.principalSupportTate W := by
  letI := coefficientNeZero P
  letI := coefficientHasInvertibleExponent P X aX
  letI := coefficientHasInvertibleExponent P W (j ≫ aX)
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) W
  exact ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} P.Coefficient) j).symm.app _) ≪≫
    (ProEtale.derivedComparisonUpperStarUpperStarIso
      (ModuleCat.{u + 1} P.Coefficient) j).app _ ≪≫
    F.mapDerivedCategory.mapIso (Etale.leftDerivedUpperStarTateTwistObjectIso P.Coefficient j 1)

/-- The class on the basic open, transposed along the exact open adjunction.
Source: def-pur-frame-class, the individual closed-open connecting map
(blueprint: def-pur-frame-principal-boundary). -/
def principalSupportOpenKummer (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (f : Γ(X, ⊤)) :
    (DerivedCategory.singleFunctor _ 0).obj
      ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient)
        (X.basicOpen f).ι).obj (P.constant (X.basicOpen f).toScheme)) ⟶
      (P.principalSupportTate X)⟦(1 : ℤ)⟧ :=
  let j := (X.basicOpen f).ι
  let L := ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) j
  let U := ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) j
  (L.mapDerivedCategorySingleFunctor 0).inv.app _ ≫
    ((ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} P.Coefficient) j).homEquiv _ _).symm
      (P.principalSupportKummer (X.basicOpen f).toScheme (j ≫ aX)
          (P.principalClosedOpenDatum (Over.mk aX) f).2.2 ≫
        (P.principalSupportTatePullback j aX).inv⟦(1 : ℤ)⟧' ≫
        (U.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app _)

/-- The principal-support boundary alpha_(X,n)(f), in the equivalent supported-Hom model.
The coefficient short exact sequence gives i_*A_D -> (j_!A_W)[1]. Compose with the shifted
Kummer class transposed from W, and combine the two cochain shifts. Applying Hom(-,I) to
that coefficient sequence identifies its connecting map with the connecting map of the
kernel-of-restriction sequence. Thus this is boundary(kappa^p(f|_W)) in H^2_D(X,A(1)).
Both i_*A_D and A(1) are sheaves in degree zero. Units, nilpotent f, and the empty scheme
are included; no Cartier, regularity, or ramification-divisibility assumption is present.
Source: def-pur-frame-class, alpha_j = partial_j kappa(f_j)
(blueprint: def-pur-frame-principal-boundary). -/
def principalSupportBoundary (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (f : Γ(X, ⊤)) :
    (DerivedCategory.singleFunctor _ 0).obj
      (ProEtale.supportedHomSource P (X.zeroLocusSubschemeι {f})) ⟶
        (P.principalSupportTate X)⟦(2 : ℤ)⟧ :=
  (P.frameCoefficientSequence_shortExact X f).singleδ ≫
    (P.principalSupportOpenKummer X aX f)⟦(1 : ℤ)⟧' ≫
    (shiftFunctorAdd' _ (1 : ℤ) 1 2 rfl).inv.app _

end WeilConjectures.PurityFiniteSetting
