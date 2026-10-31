/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PolynomialDualityAffineAtlasComparison
public import Mathlib.RingTheory.Localization.Away.Basic

/-! # Full and principal-open affine compatibility

Source: Stacks 0E2X, 0BZI, 0BZJ and 0C0H.
(blueprint: def-trf-polynomial-duality-affine-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory TopologicalSpace
namespace AlgebraicGeometry

/-- The principal-open coefficient, obtained by actual scalar extension of top forms.
Source: Stacks 0BZI, 0C0H (blueprint: def-trf-polynomial-duality-affine-compatibility). -/
def polynomialDualityLocalizedTop (R : Type u) [CommRing R] (n : ℕ)
    (h : MvPolynomial (Fin n) R) : ModuleCat.{u} (Localization.Away h) :=
  (ModuleCat.extendScalars (algebraMap (MvPolynomial (Fin n) R) (Localization.Away h))).obj
    (polynomialDualityTop R n)

/-- The localized ordered volume is one tensor the original ordered volume.
Source: Stacks 0BZI (blueprint: def-trf-polynomial-duality-affine-compatibility). -/
def polynomialDualityLocalizedVolume (R : Type u) [CommRing R] (n : ℕ)
    (h : MvPolynomial (Fin n) R) : polynomialDualityLocalizedTop R n h :=
  ((ModuleCat.extendRestrictScalarsAdj
    (algebraMap (MvPolynomial (Fin n) R) (Localization.Away h))).unit.app
    (polynomialDualityTop R n)) (polynomialDualityVolume R n)

/-- The localized coefficient retains the original relative dimension n.
Source: Stacks 0C0H (blueprint: def-trf-polynomial-duality-affine-compatibility). -/
def polynomialDualityLocalizedCoefficient (R : Type u) [CommRing R] (n : ℕ)
    (h : MvPolynomial (Fin n) R) : DerivedCategory (ModuleCat.{u} (Localization.Away h)) :=
  ((DerivedCategory.singleFunctor _ 0).obj (polynomialDualityLocalizedTop R n h))⟦(n : ℤ)⟧

/-- Adjoin the inverse of h as the last coordinate, using the actual localization inverse.
Source: Stacks 00CM, 0C0H (blueprint: def-trf-polynomial-duality-affine-compatibility). -/
def polynomialDualityLocalizationMap (R : Type u) [CommRing R] (n : ℕ)
    (h : MvPolynomial (Fin n) R) :
    MvPolynomial (Fin (n + 1)) R →+* Localization.Away h :=
  MvPolynomial.eval₂Hom
    ((algebraMap (MvPolynomial (Fin n) R) (Localization.Away h)).comp MvPolynomial.C)
    (Fin.lastCases (IsLocalization.Away.invSelf (S := Localization.Away h) h)
      (fun j : Fin n ↦ algebraMap (MvPolynomial (Fin n) R)
        (Localization.Away h) (MvPolynomial.X j)))

/-- Multiplication by h times the inverse coordinate minus one.
Source: Stacks 00CM, 0C0H (blueprint: def-trf-polynomial-duality-affine-compatibility). -/
def polynomialDualityLocalizationEquationMap (R : Type u) [CommRing R] (n : ℕ)
    (h : MvPolynomial (Fin n) R) :
    polynomialDualityTop R (n + 1) ⟶ polynomialDualityTop R (n + 1) :=
  ModuleCat.ofHom (LinearMap.lsmul _ _
    (MvPolynomial.rename Fin.castSucc h * MvPolynomial.X (Fin.last n) - 1))

/-- Principal-open contraction: d(ht-1) has last-coordinate coefficient h, so the
quotient sends the new volume to h inverse times the localized old volume. The actual
boundary of [Q --ht-1--> Q] fixes the coinduction comparison, including this factor.
Source: Stacks 0BZI, 0BZJ, 0C0H
(blueprint: def-trf-polynomial-duality-affine-compatibility). -/
def IsPolynomialDualityLocalizationContraction (R : Type u) [CommRing R] (n : ℕ)
    (h : MvPolynomial (Fin n) R)
    (e : (ModuleCat.derivedCoinduction (polynomialDualityLocalizationMap R n h)).obj
      (polynomialDualityCoefficient R (n + 1)) ≅
        polynomialDualityLocalizedCoefficient R n h) : Prop :=
  ∃ q : polynomialDualityTop R (n + 1) ⟶
      (ModuleCat.restrictScalars (polynomialDualityLocalizationMap R n h)).obj
        (polynomialDualityLocalizedTop R n h),
    q (polynomialDualityVolume R (n + 1)) =
      IsLocalization.Away.invSelf (S := Localization.Away h) h •
        polynomialDualityLocalizedVolume R n h ∧
    ∃ hz : polynomialDualityLocalizationEquationMap R n h ≫ q = 0,
    ∃ hs : (ShortComplex.mk (polynomialDualityLocalizationEquationMap R n h) q hz).ShortExact,
      e.inv = (ModuleCat.derivedCoinductionAdjunction
        (polynomialDualityLocalizationMap R n h)).homEquiv _ _
          ((Functor.commShiftIso
            (ModuleCat.restrictScalars (polynomialDualityLocalizationMap R n h)).mapDerivedCategory
              (n : ℤ)).hom.app
              ((DerivedCategory.singleFunctor _ 0).obj (polynomialDualityLocalizedTop R n h)) ≫
          (Functor.mapDerivedCategorySingleFunctor
            (ModuleCat.restrictScalars (polynomialDualityLocalizationMap R n h)) 0).hom.app
              (polynomialDualityLocalizedTop R n h)⟦(n : ℤ)⟧' ≫
          hs.singleδ⟦(n : ℤ)⟧' ≫
          (shiftFunctorAdd' _ (1 : ℤ) (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)).inv.app
            ((DerivedCategory.singleFunctor _ 0).obj (polynomialDualityTop R (n + 1))))

/-- Affine presentation identifications must realize the very same geometric chart
identification. The affine sheafification comparison is fixed on every complex by the
ordinary tilde unit, and the model map is the adjunct of evaluation at one. Together
with atlas restriction this imposes canonical localization comparisons on the affine
models. Both e and the presentation identifications occur in this nontrivial equation.
Source: Stacks 0E2U, 0E2X, 0BZI (blueprint: def-trf-polynomial-duality-affine-compatibility). -/
def IsPolynomialAffineAtlasCompatible
    [∀ Z : RingedSpace.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]
    {X S : Scheme.{u}} {f : X ⟶ S} {K : schemeDerivedCategory X}
    (atlas : PolynomialDualityChartAtlas f K)
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (jA : Spec (.of A) ⟶ X) (jR : Spec (.of R) ⟶ S) [IsOpenImmersion jA]
    (M : DerivedCategory (ModuleCat.{u} A))
    (e : (polynomialOpenRestriction jA).obj K ≅ (polynomialAffineTilde A).obj M)
    (F : PolynomialDualityPresentationSystem R A (algebraMap R A) M) : Prop :=
  ∀ (C : RelativeDualityPolynomialChart f)
    (p : MvPolynomial (Fin C.n) R →+* A) (hp : Function.Surjective p)
    (hφ : p.comp MvPolynomial.C = algebraMap R A)
    (eU : Spec (.of A) ≅ C.U.toScheme)
    (eP : Spec (.of (MvPolynomial (Fin C.n) R)) ≅ C.P)
    (hU : eU.hom ≫ C.U.ι = jA)
    (hc : eU.hom ≫ C.i = Spec.map (CommRingCat.ofHom p) ≫ eP.hom),
    eP.hom ≫ C.base = Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+*
      MvPolynomial (Fin C.n) R)) ≫ jR →
    ∀ ht : (eU.hom.toLRSHom.toShHom ≫ toDirectImageAlgebraSpace C.i) ≫
      polynomialChartAlgebraMap C.i = (eU.hom ≫ C.i).toLRSHom.toShHom,
    ∃ (dAmbient : PolynomialAffineExactData
        (tilde.functor (.of (MvPolynomial (Fin C.n) R))))
      (dAffine : PolynomialAffineExactData
        (ModuleCat.restrictScalars p ⋙ tilde.functor (.of (MvPolynomial (Fin C.n) R))))
      (dTilde : PolynomialAffineExactData (tilde.functor (.of A)))
      (dImage : ((ModuleCat.restrictScalars p ⋙
        tilde.functor (.of (MvPolynomial (Fin C.n) R))) ⋙
          Scheme.Modules.pushforward eP.hom).Additive)
      (dImage' : (tilde.functor (.of A) ⋙
        Scheme.Modules.pushforward (eU.hom ≫ C.i)).Additive),
    ∃ (σ : ModuleCat.restrictScalars p ⋙ tilde.functor (.of (MvPolynomial (Fin C.n) R)) ≅
        tilde.functor (.of A) ⋙ Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom p)))
      (q : (Scheme.Modules.pushforward eP.hom).obj (tilde (polynomialDualityTop R C.n)) ≅
        Scheme.Modules.exteriorSheaf C.base.relativeDifferentials C.n)
      (hlim : PreservesFiniteLimits (Scheme.Modules.pushforward eP.hom))
      (hcolim : PreservesFiniteColimits (Scheme.Modules.pushforward eP.hom))
      (τ : polynomialExactRealization (d := dAffine) (Spec (.of (MvPolynomial (Fin C.n) R)))
          (ModuleCat.restrictScalars p ⋙ tilde.functor (.of (MvPolynomial (Fin C.n) R))) ⋙
          RingedSpace.derivedModuleDirectImage eP.hom.toLRSHom.toShHom ≅
        (polynomialAffineTilde A) ⋙
          RingedSpace.derivedModuleDirectImage (eU.hom ≫ C.i).toLRSHom.toShHom),
      IsPolynomialTildePushforward p σ ∧ IsPolynomialAffineCoefficient C R eP q ∧
      IsPolynomialDerivedImageComparison (d := dAffine) (d' := dTilde)
        (imageAdditive := dImage) (imageAdditive' := dImage')
        (ModuleCat.restrictScalars p ⋙ tilde.functor (.of (MvPolynomial (Fin C.n) R)))
        (tilde.functor (.of A)) eP.hom (eU.hom ≫ C.i)
        (polynomialAffineOrdinaryChartComparisonForRing C p eU eP hc σ) τ ∧
      (atlas.identification C).hom =
        (RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace C.i)).map
          (polynomialAffineOpenUnit C jA eU hU K ≫
            (RingedSpace.derivedModuleDirectImage eU.hom.toLRSHom.toShHom).map e.hom) ≫
        (RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace C.i)).map
          ((RingedSpace.derivedModuleDirectImage eU.hom.toLRSHom.toShHom).map
            ((polynomialAffineTilde A).map (F.identification C.n p hp hφ).hom)) ≫
        polynomialAffineModelMapForModule (dAmbient := dAmbient) (dAffine := dAffine)
          C (atlas.exactData C) (polynomialDualityTop R C.n) p eU eP ht hlim hcolim q τ


/-- The localized coefficient is pinned by the localized ordered volume.
Source: Stacks 0BZI, 0C0H (blueprint: def-trf-polynomial-duality-affine-compatibility). -/
def IsPolynomialLocalizedAffineCoefficient
    {X S : Scheme.{u}} {f : X ⟶ S} (C : RelativeDualityPolynomialChart f)
    (R : Type u) [CommRing R] (h : MvPolynomial (Fin C.n) R)
    (eP : Spec (.of (Localization.Away h)) ≅ C.P)
    (q : (Scheme.Modules.pushforward eP.hom).obj
      (tilde (polynomialDualityLocalizedTop R C.n h)) ≅
        Scheme.Modules.exteriorSheaf C.base.relativeDifferentials C.n) : Prop :=
  q.hom.val.app (op ⊤)
    ((tilde (polynomialDualityLocalizedTop R C.n h)).val.map
      (eqToHom (show eP.hom ⁻¹ᵁ (⊤ : C.P.Opens) = ⊤ by simp)).op
        (tilde.toOpen (R := .of (Localization.Away h))
          (polynomialDualityLocalizedTop R C.n h) ⊤
            (polynomialDualityLocalizedVolume R C.n h))) =
    Scheme.Modules.exteriorSheafSection C.base.relativeDifferentials C.n ⊤
      (fun j ↦ C.base.relativeDifferentialsDerivation.d
        (eP.inv.appTop ((Scheme.ΓSpecIso (.of (Localization.Away h))).inv
          (algebraMap (MvPolynomial (Fin C.n) R)
            (Localization.Away h) (MvPolynomial.X j)))))

/-- Principal-open affine compatibility includes the inverse-coordinate presentation.
It uses the boundary of ht-1, with the forced h-inverse volume factor. Thus restriction
of a full polynomial chart to D(h) is tied to the presentation system on the smaller
source, even when the smaller source needs an additional inverse coordinate.
Source: Stacks 0E2X, 0BZI, 0BZJ, 0C0H
(blueprint: def-trf-polynomial-duality-affine-compatibility). -/
def IsPolynomialLocalizedAffineAtlasCompatible
    [∀ Z : RingedSpace.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]
    {X S : Scheme.{u}} {f : X ⟶ S} {K : schemeDerivedCategory X}
    (atlas : PolynomialDualityChartAtlas f K)
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (jA : Spec (.of A) ⟶ X) (jR : Spec (.of R) ⟶ S) [IsOpenImmersion jA]
    (M : DerivedCategory (ModuleCat.{u} A))
    (e : (polynomialOpenRestriction jA).obj K ≅ (polynomialAffineTilde A).obj M)
    (F : PolynomialDualityPresentationSystem R A (algebraMap R A) M) : Prop :=
  ∀ (C : RelativeDualityPolynomialChart f) (h : MvPolynomial (Fin C.n) R)
    (p : Localization.Away h →+* A), Function.Surjective p →
    p.comp ((algebraMap (MvPolynomial (Fin C.n) R) (Localization.Away h)).comp
      MvPolynomial.C) = algebraMap R A →
    ∀ (eU : Spec (.of A) ≅ C.U.toScheme)
    (eP : Spec (.of (Localization.Away h)) ≅ C.P)
    (hU : eU.hom ≫ C.U.ι = jA)
    (hc : eU.hom ≫ C.i = Spec.map (CommRingCat.ofHom p) ≫ eP.hom),
    eP.hom ≫ C.base = Spec.map (CommRingCat.ofHom
      ((algebraMap (MvPolynomial (Fin C.n) R) (Localization.Away h)).comp MvPolynomial.C)) ≫ jR →
    ∀ ht : (eU.hom.toLRSHom.toShHom ≫ toDirectImageAlgebraSpace C.i) ≫
      polynomialChartAlgebraMap C.i = (eU.hom ≫ C.i).toLRSHom.toShHom,
    ∃ (dAmbient : PolynomialAffineExactData (tilde.functor (.of (Localization.Away h))))
      (dAffine : PolynomialAffineExactData
        (ModuleCat.restrictScalars p ⋙ tilde.functor (.of (Localization.Away h))))
      (dTilde : PolynomialAffineExactData (tilde.functor (.of A)))
      (dImage : ((ModuleCat.restrictScalars p ⋙ tilde.functor (.of (Localization.Away h))) ⋙
        Scheme.Modules.pushforward eP.hom).Additive)
      (dImage' : (tilde.functor (.of A) ⋙
        Scheme.Modules.pushforward (eU.hom ≫ C.i)).Additive)
      (hq : Function.Surjective (p.comp (polynomialDualityLocalizationMap R C.n h)))
      (hφq : (p.comp (polynomialDualityLocalizationMap R C.n h)).comp MvPolynomial.C =
        algebraMap R A)
      (eB : (ModuleCat.derivedCoinduction (polynomialDualityLocalizationMap R C.n h)).obj
        (polynomialDualityCoefficient R (C.n + 1)) ≅
          polynomialDualityLocalizedCoefficient R C.n h),
    ∃ (σ : ModuleCat.restrictScalars p ⋙ tilde.functor (.of (Localization.Away h)) ≅
        tilde.functor (.of A) ⋙ Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom p)))
      (q : (Scheme.Modules.pushforward eP.hom).obj
        (tilde (polynomialDualityLocalizedTop R C.n h)) ≅
          Scheme.Modules.exteriorSheaf C.base.relativeDifferentials C.n)
      (hlim : PreservesFiniteLimits (Scheme.Modules.pushforward eP.hom))
      (hcolim : PreservesFiniteColimits (Scheme.Modules.pushforward eP.hom))
      (τ : polynomialExactRealization (d := dAffine) (Spec (.of (Localization.Away h)))
          (ModuleCat.restrictScalars p ⋙ tilde.functor (.of (Localization.Away h))) ⋙
          RingedSpace.derivedModuleDirectImage eP.hom.toLRSHom.toShHom ≅
        polynomialAffineTilde A ⋙
          RingedSpace.derivedModuleDirectImage (eU.hom ≫ C.i).toLRSHom.toShHom),
      IsPolynomialDualityLocalizationContraction R C.n h eB ∧
      IsPolynomialTildePushforward p σ ∧ IsPolynomialLocalizedAffineCoefficient C R h eP q ∧
      IsPolynomialDerivedImageComparison (d := dAffine) (d' := dTilde)
        (imageAdditive := dImage) (imageAdditive' := dImage')
        (ModuleCat.restrictScalars p ⋙ tilde.functor (.of (Localization.Away h)))
        (tilde.functor (.of A)) eP.hom (eU.hom ≫ C.i)
        (polynomialAffineOrdinaryChartComparisonForRing C p eU eP hc σ) τ ∧
      (atlas.identification C).hom =
        (RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace C.i)).map
          (polynomialAffineOpenUnit C jA eU hU K ≫
            (RingedSpace.derivedModuleDirectImage eU.hom.toLRSHom.toShHom).map e.hom) ≫
        (RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace C.i)).map
          ((RingedSpace.derivedModuleDirectImage eU.hom.toLRSHom.toShHom).map
            ((polynomialAffineTilde A).map
              ((F.identification (C.n + 1)
                (p.comp (polynomialDualityLocalizationMap R C.n h)) hq hφq).hom ≫
                polynomialDualityCoinductionComparison
                  (polynomialDualityLocalizationMap R C.n h) p
                  (polynomialDualityCoefficient R (C.n + 1))
                  (polynomialDualityLocalizedCoefficient R C.n h) eB))) ≫
        polynomialAffineModelMapForModule (dAmbient := dAmbient) (dAffine := dAffine)
          C (atlas.exactData C) (polynomialDualityLocalizedTop R C.n h)
          p eU eP ht hlim hcolim q τ

end AlgebraicGeometry
