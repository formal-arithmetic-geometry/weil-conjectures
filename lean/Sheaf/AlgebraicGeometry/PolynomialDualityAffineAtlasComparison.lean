/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Sheaf.AlgebraicGeometry.PolynomialDualityAffineRealization

/-! # PolynomialDualityAffineAtlasComparison

Source: Stacks duality.tex, 0E2X and 0BV2; dualizing.tex, 0BZI and 0BZJ.
(blueprint: def-trf-polynomial-duality-affine-atlas-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory TopologicalSpace
namespace AlgebraicGeometry

/-- Transport the affine tilde/direct-image comparison to an isomorphic chart.
The only transformations used are the specified affine comparison, native pushforward
composition and equality of the actual scheme maps.
Source: Stacks 01I9, 06Z0 (blueprint: def-trf-polynomial-duality-affine-atlas-comparison). -/
@[irreducible] def polynomialAffineOrdinaryChartComparisonForRing
    {X S : Scheme.{u}} {f : X ⟶ S} (C : RelativeDualityPolynomialChart f)
    {B A : Type u} [CommRing B] [CommRing A]
    (p : B →+* A)
    (eU : Spec (.of A) ≅ C.U.toScheme)
    (eP : Spec (.of (B)) ≅ C.P)
    (h : eU.hom ≫ C.i = Spec.map (CommRingCat.ofHom p) ≫ eP.hom)
    (σ : ModuleCat.restrictScalars p ⋙ tilde.functor (.of (B)) ≅
      tilde.functor (.of A) ⋙ Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom p))) :
    (ModuleCat.restrictScalars p ⋙ tilde.functor (.of (B))) ⋙
        Scheme.Modules.pushforward eP.hom ≅
      tilde.functor (.of A) ⋙ Scheme.Modules.pushforward (eU.hom ≫ C.i) :=
  Functor.isoWhiskerRight σ (Scheme.Modules.pushforward eP.hom) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Scheme.Modules.pushforwardComp _ _ ≪≫
      Scheme.Modules.pushforwardCongr h.symm)

/-- The affine coefficient is pinned by the ordered global differential volume.
A polynomial chart has a free top differential line, so this fixes the entire isomorphism,
including its sign and the rank-zero normalization.
Source: Stacks 0BZI (blueprint: def-trf-polynomial-duality-affine-atlas-comparison). -/
def IsPolynomialAffineCoefficient
    {X S : Scheme.{u}} {f : X ⟶ S} (C : RelativeDualityPolynomialChart f)
    (R : Type u) [CommRing R]
    (eP : Spec (.of (MvPolynomial (Fin C.n) R)) ≅ C.P)
    (q : (Scheme.Modules.pushforward eP.hom).obj (tilde (polynomialDualityTop R C.n)) ≅
      Scheme.Modules.exteriorSheaf C.base.relativeDifferentials C.n) : Prop :=
  q.hom.val.app (op ⊤)
    ((tilde (polynomialDualityTop R C.n)).val.map
      (eqToHom (show eP.hom ⁻¹ᵁ (⊤ : C.P.Opens) = ⊤ by simp)).op
        (tilde.toOpen (R := .of (MvPolynomial (Fin C.n) R))
          (polynomialDualityTop R C.n) ⊤ (polynomialDualityVolume R C.n))) =
    Scheme.Modules.exteriorSheafSection C.base.relativeDifferentials C.n ⊤
      (fun j ↦ C.base.relativeDifferentialsDerivation.d
        (eP.inv.appTop ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin C.n) R))).inv
          (MvPolynomial.X j))))

/-- Derive the specified ordinary coefficient isomorphism, using exact tilde, exact
isomorphism pushforward and the standard shift and single-functor comparisons.
Source: Stacks 0BZI, 06Z0 (blueprint: def-trf-polynomial-duality-affine-atlas-comparison). -/
@[irreducible] def polynomialAffineCoefficientComparisonForModule
    [∀ Z : RingedSpace.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]
    {X S : Scheme.{u}} {f : X ⟶ S} (C : RelativeDualityPolynomialChart f)
    (B : Type u) [CommRing B] (L : ModuleCat.{u} B)
    (eP : Spec (.of (B)) ≅ C.P)
    (hlim : PreservesFiniteLimits (Scheme.Modules.pushforward eP.hom))
    (hcolim : PreservesFiniteColimits (Scheme.Modules.pushforward eP.hom))
    (q : (Scheme.Modules.pushforward eP.hom).obj (tilde (L)) ≅
      Scheme.Modules.exteriorSheaf C.base.relativeDifferentials C.n) :
    (RingedSpace.derivedModuleDirectImage eP.hom.toLRSHom.toShHom).obj
      ((polynomialAffineTilde (B)).obj
        (((DerivedCategory.singleFunctor _ 0).obj L)⟦(C.n : ℤ)⟧)) ≅ C.coefficient := by
  letI := hlim
  letI := hcolim
  letI : HasDerivedCategory.{w} C.P.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings C.P.toRingedSpace)))
  letI : HasDerivedCategory.{w} (Spec (.of (B))).Modules :=
    inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (.of (B))).toRingedSpace)))
  exact (Functor.isoWhiskerLeft
      (tilde.functor (.of (B))).mapDerivedCategory
      (Scheme.Modules.pushforward eP.hom).rightDerivedFunctorIsoMapDerivedCategory ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm).app
        (((DerivedCategory.singleFunctor _ 0).obj L)⟦(C.n : ℤ)⟧) ≪≫
    (((tilde.functor (.of (B))) ⋙
      Scheme.Modules.pushforward eP.hom).mapDerivedCategory.commShiftIso (C.n : ℤ)).app _ ≪≫
    (shiftFunctor _ (C.n : ℤ)).mapIso
      ((Functor.mapDerivedCategorySingleFunctor
        (tilde.functor (.of (B)) ⋙
          Scheme.Modules.pushforward eP.hom) 0).app (L)) ≪≫
    (shiftFunctor _ (C.n : ℤ)).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso q)

/-- The affine model map is the sheaf-coinduction adjunct of the actual module
coinduction evaluation, transported by the unit-normalized affine sheafification map.
No global dualizing object or its chart identification enters this definition.
Source: Stacks 0A70, 0BUZ, 0E2U (blueprint: def-trf-polynomial-duality-affine-atlas-comparison). -/
@[irreducible] def polynomialAffineModelMapForModule
    [∀ Z : RingedSpace.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]
    {X S : Scheme.{u}} {f : X ⟶ S} (C : RelativeDualityPolynomialChart f)
    (d : PolynomialChartExactData C.i)
    {B A : Type u} [CommRing B] [CommRing A]
    (L : ModuleCat.{u} B) (p : B →+* A)
    (eU : Spec (.of A) ≅ C.U.toScheme)
    (eP : Spec (.of (B)) ≅ C.P)
    (ht : (eU.hom.toLRSHom.toShHom ≫ toDirectImageAlgebraSpace C.i) ≫
      polynomialChartAlgebraMap C.i = (eU.hom ≫ C.i).toLRSHom.toShHom)
    (hlim : PreservesFiniteLimits (Scheme.Modules.pushforward eP.hom))
    (hcolim : PreservesFiniteColimits (Scheme.Modules.pushforward eP.hom))
    (q : (Scheme.Modules.pushforward eP.hom).obj (tilde (L)) ≅
      Scheme.Modules.exteriorSheaf C.base.relativeDifferentials C.n)
    [dAmbient : PolynomialAffineExactData (tilde.functor (.of B))]
    [dAffine : PolynomialAffineExactData
      (ModuleCat.restrictScalars p ⋙ tilde.functor (.of (B)))]
    (τ : polynomialExactRealization (Spec (.of (B)))
      (ModuleCat.restrictScalars p ⋙ tilde.functor (.of (B))) ⋙
        RingedSpace.derivedModuleDirectImage eP.hom.toLRSHom.toShHom ≅
      (polynomialAffineTilde A) ⋙
        RingedSpace.derivedModuleDirectImage (eU.hom ≫ C.i).toLRSHom.toShHom) :
    (RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace C.i)).obj
      ((RingedSpace.derivedModuleDirectImage eU.hom.toLRSHom.toShHom).obj
        ((polynomialAffineTilde A).obj ((ModuleCat.derivedCoinduction p).obj
          (((DerivedCategory.singleFunctor _ 0).obj L)⟦(C.n : ℤ)⟧)))) ⟶
      C.model d.additive := by
  letI : HasDerivedCategory.{w} (Spec (.of A)).Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)))
  letI : HasDerivedCategory.{w} (Spec (.of (B))).Modules :=
    inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (.of (B))).toRingedSpace)))
  exact (polynomialChartDerivedAdjunction C.i d).homEquiv _ _
    ((Functor.isoWhiskerRight
        (polynomialImageComposition eU.hom.toLRSHom.toShHom (toDirectImageAlgebraSpace C.i))
        (RingedSpace.derivedModuleDirectImage (polynomialChartAlgebraMap C.i)) ≪≫
      polynomialImageComposition _ _ ≪≫
      eqToIso (congrArg RingedSpace.derivedModuleDirectImage ht)).hom.app _ ≫
      τ.inv.app ((ModuleCat.derivedCoinduction p).obj
          (((DerivedCategory.singleFunctor _ 0).obj L)⟦(C.n : ℤ)⟧)) ≫
      (RingedSpace.derivedModuleDirectImage eP.hom.toLRSHom.toShHom).map
        ((polynomialRestrictionTildeComposition p).hom.app _ ≫
          (polynomialAffineTilde (B)).map
            ((ModuleCat.derivedCoinductionAdjunction p).counit.app
              (((DerivedCategory.singleFunctor _ 0).obj L)⟦(C.n : ℤ)⟧))) ≫
      (polynomialAffineCoefficientComparisonForModule C B L eP hlim hcolim q).hom)

/-- The unit-normalized map from the open restriction of K to the direct image of
its expression on an isomorphic affine chart. This leaves no free affine restriction map.
Source: Stacks 0E2X, 06Z0 (blueprint: def-trf-polynomial-duality-affine-atlas-comparison). -/
@[irreducible] def polynomialAffineOpenUnit
    [∀ Z : RingedSpace.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]
    {X S : Scheme.{u}} {f : X ⟶ S} (C : RelativeDualityPolynomialChart f)
    {A : Type u} [CommRing A] (jA : Spec (.of A) ⟶ X) [IsOpenImmersion jA]
    (eU : Spec (.of A) ≅ C.U.toScheme) (hU : eU.hom ≫ C.U.ι = jA)
    (K : schemeDerivedCategory X) :
    (polynomialOpenRestriction C.U.ι).obj K ⟶
      (RingedSpace.derivedModuleDirectImage eU.hom.toLRSHom.toShHom).obj
        ((polynomialOpenRestriction jA).obj K) := by
  letI : HasDerivedCategory.{w} X.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
  letI : HasDerivedCategory.{w} C.U.toScheme.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings C.U.toScheme.toRingedSpace)))
  letI : HasDerivedCategory.{w} (Spec (.of A)).Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)))
  exact (polynomialOpenAdjunction eU.hom).unit.app _ ≫
    (RingedSpace.derivedModuleDirectImage eU.hom.toLRSHom.toShHom).map
      ((Functor.mapDerivedCategoryCompIso (Scheme.Modules.restrictFunctor C.U.ι)
        (Scheme.Modules.restrictFunctor eU.hom)).inv.app K ≫
      (Functor.mapDerivedCategoryNatIso
        ((Scheme.Modules.restrictFunctorComp eU.hom C.U.ι).symm ≪≫
          Scheme.Modules.restrictFunctorCongr hU)).hom.app K)

end AlgebraicGeometry
