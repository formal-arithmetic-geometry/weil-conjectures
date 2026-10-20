/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurEtaleScalarMateProjection
import all WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities
import WeilConjectures.CategoryTheory.Sites.SheafComposePushforwardMonoidal

/-! # Compatibility of scalar pullback with the underlying tensor comparison

Source: Stacks Project, Tags 07A4, 0G7E, 06YY and 0GL6.
(blueprint: lem-asd-scalar-pullback-tensor-compatibility).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Functor
private theorem mate_symm_isMonoidal
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (G : C ⥤ E) (H : D ⥤ F)
    [L₁.Monoidal] [R₁.LaxMonoidal] [L₂.Monoidal] [R₂.LaxMonoidal]
    [G.LaxMonoidal] [H.LaxMonoidal] [adj₁.IsMonoidal] [adj₂.IsMonoidal]
    (β : TwoSquare R₁ H G R₂) [β.natTrans.IsMonoidal] :
    NatTrans.IsMonoidal ((mateEquiv adj₁ adj₂).symm β).natTrans := by
  change NatTrans.IsMonoidal
    ((Functor.leftUnitor _).inv ≫
      Functor.whiskerRight adj₁.unit (G ⋙ L₂) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (Functor.associator _ _ _).hom _ ≫
      Functor.whiskerRight (Functor.whiskerLeft L₁ β.natTrans) L₂ ≫
      Functor.whiskerRight (Functor.associator _ _ _).inv _ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (L₁ ⋙ H) adj₂.counit ≫
      (Functor.rightUnitor _).hom)
  infer_instance

private def balance {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {S : C ⥤ D} {U : D ⥤ C} [U.LaxMonoidal] (adj : S ⊣ U) (M : C) :
    M ⊗ U.obj (𝟙_ D) ⟶ U.obj (S.obj M) :=
  adj.unit.app M ▷ U.obj (𝟙_ D) ≫
    Functor.LaxMonoidal.μ U (S.obj M) (𝟙_ D) ≫ U.map (ρ_ _).hom
private theorem balance_pullback
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory F]
    (FR : C ⥤ D) (FA : E ⥤ F) [FR.Monoidal] [FA.Monoidal]
    (SY : C ⥤ E) (SX : D ⥤ F) (UY : E ⥤ C) (UX : F ⥤ D)
    [UY.LaxMonoidal] [UX.LaxMonoidal] (adjY : SY ⊣ UY) (adjX : SX ⊣ UX)
    (χ : UY ⋙ FR ≅ FA ⋙ UX) [χ.hom.IsMonoidal]
    (τ : SY ⋙ FA ≅ FR ⋙ SX)
    (hu : ∀ M, FR.map (adjY.unit.app M) ≫ χ.hom.app (SY.obj M) ≫
      UX.map (τ.hom.app M) = adjX.unit.app (FR.obj M)) (M : C) :
    FR.map (balance adjY M) ≫ χ.hom.app (SY.obj M) ≫ UX.map (τ.hom.app M) =
      Functor.OplaxMonoidal.δ FR M (UY.obj (𝟙_ E)) ≫
        FR.obj M ◁ (χ.hom.app (𝟙_ E) ≫ UX.map (Functor.OplaxMonoidal.η FA)) ≫
        balance adjX (FR.obj M) := by
  have hn := χ.hom.naturality (ρ_ (SY.obj M)).hom
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  have ht := NatTrans.IsMonoidal.tensor (τ := χ.hom) (SY.obj M) (𝟙_ E)
  simp only [Functor.LaxMonoidal.comp_μ, Functor.comp_obj] at ht
  dsimp only [balance]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  rw [Functor.Monoidal.map_whiskerRight]
  simp only [Category.assoc]
  simp only [Category.assoc] at ht
  erw [reassoc_of% ht]
  have hr : Functor.LaxMonoidal.μ FA (SY.obj M) (𝟙_ E) ≫
      FA.map (ρ_ (SY.obj M)).hom =
      FA.obj (SY.obj M) ◁ Functor.OplaxMonoidal.η FA ≫
        (ρ_ (FA.obj (SY.obj M))).hom := by
    rw [← Functor.OplaxMonoidal.right_unitality_hom FA,
      Functor.Monoidal.μ_δ_assoc]
  rw [← UX.map_comp_assoc, hr, UX.map_comp]
  simp only [Category.assoc]
  rw [← UX.map_comp (ρ_ (FA.obj (SY.obj M))).hom (τ.hom.app M)]
  rw [← rightUnitor_naturality, UX.map_comp]
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc]
  rw [← Functor.LaxMonoidal.μ_natural_left_assoc]
  simp only [Functor.id_obj, Functor.comp_obj]
  simp only [← tensorHom_id, ← id_tensorHom,
    tensorHom_comp_tensorHom_assoc,
    Category.id_comp, Category.comp_id]
  rw [hu]

namespace AlgebraicGeometry.Etale

private theorem ordinary_restriction_directImage_isMonoidal
    {R A : Type (u + 1)} [CommRing R] [CommRing A]
    (φ : R →+* A) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    NatTrans.IsMonoidal (lowerStarRestrictScalarsIso φ f).hom := by
  exact inferInstanceAs (NatTrans.IsMonoidal
    (Functor.sheafPushforwardContinuousCompSheafComposeIso
      (MorphismProperty.Over.pullback @Etale ⊤ f)
      (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)
      (ModuleCat.restrictScalars.{u + 1} φ)).hom)

private theorem ordinary_restriction_pullback_isMonoidal
    {R A : Type (u + 1)} [CommRing R] [CommRing A]
    (φ : R →+* A) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [NatTrans.IsMonoidal (lowerStarRestrictScalarsIso φ f).hom] :
    NatTrans.IsMonoidal (upperStarRestrictScalarsIsoSheaf φ f).hom := by
  have hm := underived_mate φ f
  have h := congrArg ((mateEquiv
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f)).symm)
    (show (mateEquiv
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f)
      (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIsoSheaf φ f).hom)) =
      TwoSquare.mk _ _ _ _ (lowerStarRestrictScalarsIso φ f).hom from
        congrArg (TwoSquare.mk _ _ _ _) hm)
  rw [Equiv.symm_apply_apply] at h
  rw [← show ((mateEquiv
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f)).symm
      (TwoSquare.mk _ _ _ _ (lowerStarRestrictScalarsIso φ f).hom)).natTrans =
      (upperStarRestrictScalarsIsoSheaf φ f).hom from congrArg TwoSquare.natTrans h.symm]
  exact mate_symm_isMonoidal _ _ _ _ _

private theorem scalarSheafPullback_mate
    {R A : Type (u + 1)} [CommRing R] [CommRing A]
    (φ : R →+* A) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (mateEquiv (ProEtale.etaleSheafExtendScalarsAdjunction φ Y)
      (ProEtale.etaleSheafExtendScalarsAdjunction φ X)
      (TwoSquare.mk _ _ _ _ (scalarSheafPullbackIso φ f).inv)).natTrans =
        (upperStarRestrictScalarsIsoSheaf φ f).hom := by
  apply (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f)).injective
  change (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f)
    (mateEquiv (ProEtale.etaleSheafExtendScalarsAdjunction φ Y)
      (ProEtale.etaleSheafExtendScalarsAdjunction φ X)
      (TwoSquare.mk _ _ _ _ (scalarSheafPullbackIso φ f).inv))).natTrans =
    (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f)
      (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIsoSheaf φ f).hom)).natTrans
  rw [iterated_mateEquiv_conjugateEquiv, underived_mate φ f]
  simp only [scalarSheafPullbackIso, conjugateIsoEquiv_symm_apply_inv]
  exact Equiv.apply_symm_apply _ _

private theorem scalarSheafPullback_unit
    {R A : Type (u + 1)} [CommRing R] [CommRing A]
    (φ : R →+* A) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (upperStar (ModuleCat.{u + 1} R) f).map
        ((ProEtale.etaleSheafExtendScalarsAdjunction φ Y).unit.app M) ≫
      (upperStarRestrictScalarsIsoSheaf φ f).hom.app
        ((ProEtale.etaleSheafExtendScalars φ Y).obj M) ≫
      (Sheaf.restrictScalars X.smallEtaleTopology φ).map
        ((scalarSheafPullbackIso φ f).hom.app M) =
      (ProEtale.etaleSheafExtendScalarsAdjunction φ X).unit.app
        ((upperStar (ModuleCat.{u + 1} R) f).obj M) := by
  have h := unit_mateEquiv
    (ProEtale.etaleSheafExtendScalarsAdjunction φ Y)
    (ProEtale.etaleSheafExtendScalarsAdjunction φ X)
    (TwoSquare.mk _ _ _ _ (scalarSheafPullbackIso φ f).inv) M
  have hm := congr_app (scalarSheafPullback_mate φ f)
    ((ProEtale.etaleSheafExtendScalars φ Y).obj M)
  dsimp only [TwoSquare.mk] at h
  rw [hm] at h
  rw [← Category.assoc, h, Category.assoc, ← Functor.map_comp]
  change _ ≫ (Sheaf.restrictScalars X.smallEtaleTopology φ).map
    ((scalarSheafPullbackIso φ f).inv.app M ≫
      (scalarSheafPullbackIso φ f).hom.app M) = _
  rw [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl


-- The ordinary equation needed before applying the derived representative maps.
private theorem scalarSheafPullback_tensor_compatibility
    {R A : Type (u + 1)} [CommRing R] [CommRing A]
    (φ : R →+* A) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (upperStar (ModuleCat.{u + 1} R) f).map (scalarSheafTensorMap φ Y M) ≫
        (upperStarRestrictScalarsIsoSheaf φ f).hom.app
          ((ProEtale.etaleSheafExtendScalars φ Y).obj M) ≫
        (Sheaf.restrictScalars X.smallEtaleTopology φ).map
          ((scalarSheafPullbackIso φ f).hom.app M) =
      Functor.OplaxMonoidal.δ (upperStar (ModuleCat.{u + 1} R) f) M
          (scalarCoefficientSheaf φ Y) ≫
        (upperStar (ModuleCat.{u + 1} R) f).obj M ◁
          ((upperStarRestrictScalarsIsoSheaf φ f).hom.app (𝟙_ _) ≫
            (Sheaf.restrictScalars X.smallEtaleTopology φ).map
              (Functor.OplaxMonoidal.η (upperStar (ModuleCat.{u + 1} A) f))) ≫
        scalarSheafTensorMap φ X ((upperStar (ModuleCat.{u + 1} R) f).obj M) := by
  have := ordinary_restriction_directImage_isMonoidal φ f
  have := ordinary_restriction_pullback_isMonoidal φ f
  exact balance_pullback
    (upperStar (ModuleCat.{u + 1} R) f) (upperStar (ModuleCat.{u + 1} A) f)
    (ProEtale.etaleSheafExtendScalars φ Y) (ProEtale.etaleSheafExtendScalars φ X)
    (Sheaf.restrictScalars Y.smallEtaleTopology φ)
    (Sheaf.restrictScalars X.smallEtaleTopology φ)
    (ProEtale.etaleSheafExtendScalarsAdjunction φ Y)
    (ProEtale.etaleSheafExtendScalarsAdjunction φ X)
    (upperStarRestrictScalarsIsoSheaf φ f) (scalarSheafPullbackIso φ f)
    (scalarSheafPullback_unit φ f) M

/-- Restricting the scalar/pullback comparison gives the canonical tensor comparison.

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 0G7E and 06YY;
more-etale.tex, Tag 0GL6, coefficient comparison.
(blueprint: lem-asd-scalar-pullback-tensor-compatibility).

Proof: choose a flat-term K-flat resolution P of C. Exact inverse image preserves
K-flatness and flat terms. The defining normalization of scalarPullbackIso identifies
its component on Q(P) with the degreewise ordinary scalar/pullback comparison.
The defining normalization of scalarTensorIso identifies restriction of scalar
extension with tensoring by the restricted coefficient sheaf. Substitute these
normalizations, and the counit normalization of leftDerivedUpperStarTensorComparison.
The ordinary restriction/direct-image identity is monoidal. Its inverse mate is
monoidal by the geometric monoidal unit and counit equations. The double mate of
the ordinary scalar/pullback comparison identifies its scalar unit equation with
that restriction/pullback mate. Expand scalarSheafTensorMap as scalar unit, lax
tensorator and right unitor. Naturality, the monoidal tensor equation, that scalar
unit equation and right unitality identify the two ordinary tensor routes. The
coefficient comparison is the restriction/pullback comparison at the A-unit followed
by the inverse geometric monoidal unit, exactly as in scalarCoefficientPullbackIso.
The ordinary balancing map is invertible: before sheafification its inverse
sends a tensor m to m tensor a. These formulas respect the scalar balancing
relations and restriction maps. Apply the square degreewise and totalize; no
degree is interchanged.
The tensor-model comparisons and geometric counits are invertible on P and its
inverse image. Cancel them to obtain the equation on Q(P), then use naturality
along the resolution isomorphism Q(P) to C. This argument requires neither flatness
of the coefficient map nor boundedness, finiteness or properness. -/
theorem scalarPullback_tensor_compatibility
    {R A : Type (u + 1)} [CommRing R] [CommRing A]
    (φ : R →+* A) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (C : DerivedCategoryModule R Y) :
    (scalarRestrictionPullbackIso φ f).hom.app ((scalarExtension φ Y).obj C) ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).map
          ((scalarPullbackIso φ f).hom.app C) ≫
        (scalarTensorIso φ X).hom.app (L((f)^*[ModuleCat.{u + 1} R]).obj C) =
      L((f)^*[ModuleCat.{u + 1} R]).map ((scalarTensorIso φ Y).hom.app C) ≫
        ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} R) f).app C).app
          (scalarCoefficient φ Y) ≫
        ((derivedTensor (ModuleCat.{u + 1} R) X).obj
          (L((f)^*[ModuleCat.{u + 1} R]).obj C)).map
          (scalarCoefficientPullbackIso φ f).hom := by
  sorry

end AlgebraicGeometry.Etale
