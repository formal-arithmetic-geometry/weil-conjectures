/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsFlat
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStar
import WeilConjectures.SixFunctors.Etale.Derived.CoextendScalars

/-! # Restriction of coefficients and compact support

Source: latest blueprint lem-fix-operation-reduction, principal coefficient comparisons.
The proper factor is obtained by taking right adjoints of scalar extension and pullback;
the open factor is exact extension by zero.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.PrincipalCoefficient

-- The following private resolution argument reuses the proved construction in
-- WeilConjectures.SixFunctors.CoefficientReduction without importing its consumers.
-- Keep the two complex-composition comparisons explicit before specializing the sites.
private lemma leftDerivedSquare
    {C D E F : Type*}
    [Category.{u + 1} C] [Category.{u + 1} D]
    [Category.{u + 1} E] [Category.{u + 1} F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [IsGrothendieckAbelian.{u + 1} C] [IsGrothendieckAbelian.{u + 1} D]
    [IsGrothendieckAbelian.{u + 1} F]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [MonoidalCategory F] [MonoidalPreadditive F] [MonoidalClosed F] [BraidedCategory F]
    [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
    [Abelian.HasFunctorialFlatResolution F]
    [HasDerivedCategory.{u + 1} C] [HasDerivedCategory.{u + 1} D]
    [HasDerivedCategory.{u + 1} E] [HasDerivedCategory.{u + 1} F]
    (FA : C ⥤ D) (EX : D ⥤ E) (EY : C ⥤ F) (FB : F ⥤ E)
    [FA.Additive] [EX.Additive] [EY.Additive] [FB.Additive]
    [FA.PreservesKFlatQuasiIso] [EX.PreservesKFlatQuasiIso]
    [EY.PreservesKFlatQuasiIso] [FB.PreservesKFlatQuasiIso]
    [FA.PreservesFlat] [EY.PreservesFlat]
    [PreservesColimitsOfShape ℤ FA] [PreservesColimitsOfShape ℤ EY]
    (e : EY ⋙ FB ≅ FA ⋙ EX) :
    Nonempty (EY.leftDerivedFunctor ⋙ FB.leftDerivedFunctor ≅
      FA.leftDerivedFunctor ⋙ EX.leftDerivedFunctor) := by
  let eC := cochainSquareIso EY FB FA EX e
  let F := EY.leftDerivedFunctor ⋙ FB.leftDerivedFunctor
  let G := FA.leftDerivedFunctor ⋙ EX.leftDerivedFunctor
  let H := FA.mapHomologicalComplex (.up ℤ) ⋙ EX.mapHomologicalComplex (.up ℤ) ⋙
    _root_.DerivedCategory.Q
  let s : _root_.DerivedCategory.Q ⋙ G ⟶ H :=
    Functor.whiskerRight (cochainCounit FA) EX.leftDerivedFunctor ≫
      Functor.whiskerLeft (FA.mapHomologicalComplex (.up ℤ)) (cochainCounit EX)
  let t : _root_.DerivedCategory.Q ⋙ F ⟶ H :=
    Functor.whiskerRight (cochainCounit EY) FB.leftDerivedFunctor ≫
      Functor.whiskerLeft (EY.mapHomologicalComplex (.up ℤ)) (cochainCounit FB) ≫
      Functor.whiskerRight eC.hom _root_.DerivedCategory.Q
  let Λ : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ C) := Classical.arbitrary _
  have hs : ∀ K, IsIso (s.app (Λ.reduced.resolutionFunctor.obj K)) := by
    intro K
    have hF := FA.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ.reduced
      ObjectProperty.flat.essImage_ι_le K
    have := cochainCounit_isIso EX _ hF
    have := cochainCounit_isIso FA _
      (Λ.reduced.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K)
    dsimp only [s, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  have ht : ∀ K, IsIso (t.app (Λ.reduced.resolutionFunctor.obj K)) := by
    intro K
    have := cochainCounit_isIso EY _
      (Λ.reduced.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K)
    have hE := EY.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ.reduced
      ObjectProperty.flat.essImage_ι_le K
    have := cochainCounit_isIso FB _ hE
    dsimp only [t, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  exact comparisonFromResolution _root_.DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) F G H s t
    Λ.reduced.resolutionFunctor Λ.reduced.resolutionNatTrans (fun _ ↦ inferInstance) hs ht


private def restrictionDirectImageIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf.derivedRestrictScalars X.smallEtaleTopology φ ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor ≅
      (Etale.lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctor ⋙
        Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ := by
  let EX := Sheaf.extendScalars X.smallEtaleTopology φ
  let EY := Sheaf.extendScalars Y.smallEtaleTopology φ
  let UX := Sheaf.restrictScalars X.smallEtaleTopology φ
  let UY := Sheaf.restrictScalars Y.smallEtaleTopology φ
  let FA := Etale.upperStar (ModuleCat.{u + 1} A) f
  let FB := Etale.upperStar (ModuleCat.{u + 1} B) f
  let := φ.toAlgebra
  have hx : EX.PreservesKFlatQuasiIso := by
    constructor
    intro P Q hP hQ q hq
    exact CochainComplex.quasiIso_map_of_iso_tensorRight _ _
      (Sheaf.extendScalarsCompRestrictScalarsIso X.smallEtaleTopology A B) q hP hQ
  have hy : EY.PreservesKFlatQuasiIso := by
    constructor
    intro P Q hP hQ q hq
    exact CochainComplex.quasiIso_map_of_iso_tensorRight _ _
      (Sheaf.extendScalarsCompRestrictScalarsIso Y.smallEtaleTopology A B) q hP hQ
  let aX := (Sheaf.extendScalarsAdjunction X.smallEtaleTopology φ).derivedAdjunction
    |>.ofNatIsoRight UX.rightDerivedFunctorIsoMapDerivedCategory
  let aY := (Sheaf.extendScalarsAdjunction Y.smallEtaleTopology φ).derivedAdjunction
    |>.ofNatIsoRight UY.rightDerivedFunctorIsoMapDerivedCategory
  let e₀ : EY ⋙ FB ≅ FA ⋙ EX :=
    (conjugateIsoEquiv
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).comp
        (Sheaf.extendScalarsAdjunction X.smallEtaleTopology φ))
      ((Sheaf.extendScalarsAdjunction Y.smallEtaleTopology φ).comp
        (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f))).symm
      (Etale.lowerStarCompRestrictScalarsIso φ f).symm
  have := Sheaf.preservesFlat_extendScalars Y.smallEtaleTopology (f := φ)
  let e := (leftDerivedSquare FA EX EY FB e₀).some
  exact conjugateIsoEquiv
    ((Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).comp aX)
    (aY.comp (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)) e

private def restrictionOpenIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Sheaf.restrictScalars U.smallEtaleTopology φ ⋙
        Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j ≅
      Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j ⋙
        Sheaf.restrictScalars X.smallEtaleTopology φ :=
  (conjugateIsoEquiv
    ((Etale.openImmersionLowerShriekAdjunction _ j).comp
      (Sheaf.restrictCoextendScalarsAdj _ φ))
    ((Sheaf.restrictCoextendScalarsAdj _ φ).comp
      (Etale.openImmersionLowerShriekAdjunction _ j))).symm (Iso.refl _)

/-- Exact coefficient restriction commutes with compact support on unbounded complexes.
Source: latest blueprint lem-fix-operation-reduction, principal coefficient comparisons
(blueprint: lem-principal-coefficient-restriction).

Proof: scalar extension commutes with geometric inverse image, by the K-flat
scalar/pullback comparison. Take right adjoints of both composite left adjoints:
this identifies restriction followed by derived direct image with derived direct
image followed by restriction, without boundedness assumptions. For an open
immersion, transpose the objectwise equality between coextension and inverse
image; both extension by zero and restriction are exact, so their square descends
to derived categories. Paste the open square and the direct-image square for the
chosen compactification. -/
theorem compactSupportRestrictionIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    Nonempty (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ≅
      Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) f ⋙
        Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ) := by
  let c := HasCompactification.compactification f
  let e := Functor.mapDerivedCategorySquareIso (restrictionOpenIso φ c.i)
  exact ⟨(Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (restrictionDirectImageIso φ c.g) ≪≫
    (Functor.associator _ _ _).symm⟩

end AlgebraicGeometry.PrincipalCoefficient
