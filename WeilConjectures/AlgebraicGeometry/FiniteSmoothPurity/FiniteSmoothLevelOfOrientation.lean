/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothAdjunctionData
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorDuality
import WeilConjectures.AlgebraicGeometry.Etale.Support.EtaleSupportMapCompatibility
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothAdjunctionData
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.AlgebraicGeometry.Finite.Etale.FiniteEtaleDiagonalCoordinates
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteEtaleSpecializationCoordinates
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteRankZeroNormalIntegration
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSectionIntegratedSpecialization
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothOmegaTensorCoordinates

/-! # Finite-level purity from its normalized orientation

Source: main-20261015, sec-smooth-purity/sk-thm-smooth-purity and
sk-lem-sp-reduction/compatibilities (blueprint: lem-pur-finite-smooth-level-of-orientation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u u' w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

private theorem intrinsicOrigin
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T]
    (K : proCategory A T) (hK : IsCtf A T K) :
    ∃ K₀ : DerivedCategoryModule A T,
      DerivedCategory.boundedConstructibleFiniteTor A T K₀ ∧
      Nonempty ((comparison A T).obj K₀ ≅ K) := by
  obtain ⟨a, b, hab, hv⟩ := hK.2.1
  have hbd : _root_.DerivedCategory.TStructure.t.bounded K :=
    ⟨⟨a, (_root_.DerivedCategory.isGE_iff K a).mpr
      (fun i hi ↦ hv i (Or.inl hi))⟩,
     ⟨b, (_root_.DerivedCategory.isLE_iff K b).mpr
      (fun i hi ↦ hv i (Or.inr hi))⟩⟩
  have hc := ProEtale.exceptionalTransport_constructible_comparison A T
  obtain ⟨K₀, hK₀, ⟨e⟩⟩ := (congrFun hc K).mp ⟨hbd, hK.1⟩
  have hbc : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T K₀ := by
    obtain ⟨hc, a, b, _, hv⟩ := hK₀
    exact ⟨⟨⟨a, (_root_.DerivedCategory.isGE_iff K₀ a).mpr
      (fun i hi ↦ hv i (Or.inl hi))⟩,
      ⟨b, (_root_.DerivedCategory.isLE_iff K₀ b).mpr
        (fun i hi ↦ hv i (Or.inr hi))⟩⟩,
      fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hc i)⟩
  refine ⟨K₀, ⟨hbc, ?_⟩, ⟨e⟩⟩
  obtain ⟨c, d, hcd, ht⟩ := hK.2.2
  refine ⟨c, d, ?_⟩
  apply (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff c d K₀).mp
  exact (_root_.DerivedCategory.torAmplitudeIn _ c d).prop_of_iso e.symm ht

private theorem intrinsicOriginCounit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T]
    (K : proCategory A T) (hK : IsCtf A T K) :
    IsIso ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).counit.app K) := by
  obtain ⟨K₀, hK₀, ⟨e⟩⟩ := intrinsicOrigin A T K hK
  let adj := ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) T
  have hp : _root_.DerivedCategory.TStructure.t.plus K₀ := hK₀.1.1.1
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app (ModuleCat A) T K₀ hp
  have hu : IsIso ((comparison A T).map (adj.unit.app K₀)) := inferInstance
  have hc : IsIso (adj.counit.app ((comparison A T).obj K₀)) :=
    IsIso.of_isIso_fac_left (adj.left_triangle_components K₀)
  exact (NatTrans.isIso_app_iff_of_iso adj.counit e).mp hc

private theorem actualOriginCtf
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T]
    (K : proCategory A T) (hK : IsCtf A T K) :
    DerivedCategory.boundedConstructibleFiniteTor A T ((origin A T).obj K) := by
  obtain ⟨K₀, hK₀, ⟨e⟩⟩ := intrinsicOrigin A T K hK
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app (ModuleCat A) T K₀
    hK₀.1.1.1
  let q : K₀ ≅ (origin A T).obj K :=
    asIso ((ProEtale.derivedComparisonAdjunction (ModuleCat A) T).unit.app K₀) ≪≫
      (origin A T).mapIso e
  exact ⟨(DerivedCategory.boundedConstructible (ModuleCat A) T).prop_of_iso q hK₀.1,
    (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso q hK₀.2⟩

private def tensorTransport
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D)
    {F G : C ⥤ D} (e : F ≅ G)
    (m : (Functor.postcompose₂.obj F).obj T ≅
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj U) :
    (Functor.postcompose₂.obj G).obj T ≅
      (((Functor.whiskeringLeft₂ D).obj G).obj G).obj U :=
  (Functor.postcompose₂.mapIso e.symm).app T ≪≫ m ≪≫
    ((((Functor.whiskeringLeft₂ D).obj F).mapIso e).app U) ≪≫
    (((Functor.whiskeringLeft₂ D).mapIso e).app G).app U

private def sourceTransport
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (P : C ⥤ D) (E : C ⥤ C') (H : D ⥤ D') (Q : C' ⥤ D')
    (T : D ⥤ D ⥤ D) (U : D' ⥤ D' ⥤ D')
    (t : (Functor.postcompose₂.obj H).obj T ≅
      (((Functor.whiskeringLeft₂ D').obj H).obj H).obj U)
    (q : E ⋙ Q ≅ P ⋙ H) (L : D) :
    (P ⋙ T.flip.obj L) ⋙ H ≅ E ⋙ (Q ⋙ U.flip.obj (H.obj L)) := by
  let tL : T.flip.obj L ⋙ H ≅ H ⋙ U.flip.obj (H.obj L) :=
    ((flipFunctor _ _ _).mapIso t).app L
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft P tL ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight q.symm (U.flip.obj (H.obj L)) ≪≫
    Functor.associator _ _ _

private theorem ordinaryExceptionalCtf
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    [HasInvertibleExponent A Y]
    (K : DerivedCategoryModule A Y)
    (hK : DerivedCategory.boundedConstructibleFiniteTor A Y K) :
    DerivedCategory.boundedConstructibleFiniteTor A X
      ((rightDerivedUpperShriek A f).obj K) := by
  obtain ⟨a, b, hab⟩ :=
    (DerivedCategory.exists_constructibleTorAmplitudeIn_iff_constructibleFiniteTor K).mpr hK
  exact (DerivedCategory.exists_constructibleTorAmplitudeIn_iff_constructibleFiniteTor _).mp
    ⟨a - 2 * d, b - 2 * d,
      constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_smoothOfRelativeDimension
        A f d a b hab⟩

private theorem comparisonCtf
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T]
    (K : DerivedCategoryModule A T)
    (hK : DerivedCategory.boundedConstructibleFiniteTor A T K) :
    IsCtf A T ((comparison A T).obj K) := by
  have hc := ProEtale.exceptionalTransport_constructible_comparison A T
  have hK' : DerivedCategory.isBoundedConstructible A T K := by
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hK.1
    refine ⟨fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (hc i), min a b, b, min_le_right _ _, ?_⟩
    intro i hi
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff K a).mp ha i
        (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff K b).mp hb i hi
  obtain ⟨hb, hcon⟩ := (congrFun hc ((comparison A T).obj K)).mpr ⟨K, hK', ⟨Iso.refl _⟩⟩
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hb
  refine ⟨hcon, ⟨min a b, b, min_le_right _ _, ?_⟩, ?_⟩
  · intro i hi
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff _ a).mp ha i
        (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff _ b).mp hb i hi
  · obtain ⟨a, b, ht⟩ := hK.2
    exact ⟨a, max a b, le_max_left _ _,
      (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff _ _ K).mpr
        (ht.mono le_rfl (le_max_right _ _))⟩

private theorem isCtfOfIso
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) [IsNoetherian T]
    {K L : proCategory A T} (e : K ≅ L) (hK : IsCtf A T K) : IsCtf A T L := by
  obtain ⟨a, b, hab, hv⟩ := hK.2.1
  have hbd : _root_.DerivedCategory.TStructure.t.bounded K :=
    ⟨⟨a, (_root_.DerivedCategory.isGE_iff K a).mpr
      (fun i hi ↦ hv i (Or.inl hi))⟩,
     ⟨b, (_root_.DerivedCategory.isLE_iff K b).mpr
      (fun i hi ↦ hv i (Or.inr hi))⟩⟩
  have hc := ProEtale.exceptionalTransport_constructible_comparison A T
  obtain ⟨K₀, hK₀, ⟨q⟩⟩ := (congrFun hc K).mp ⟨hbd, hK.1⟩
  have hcon := ((congrFun hc L).mpr ⟨K₀, hK₀, ⟨q ≪≫ e⟩⟩).2
  refine ⟨hcon, ⟨a, b, hab, ?_⟩, ?_⟩
  · exact fun i hi ↦ (hv i hi).of_iso
      ((_root_.DerivedCategory.homologyFunctor _ i).mapIso e).symm
  · obtain ⟨a, b, hab, h⟩ := hK.2.2
    exact ⟨a, b, hab, (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e h⟩

private theorem proGammaIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (hY : ∀ y : Y, IsUnit (N : Y.presheaf.stalk y))
    (L : DerivedCategoryModule A X) (alpha : dualizingComplex A f ≅ L)
    (K : proCategory A Y) (hK : IsCtf A Y K) : IsIso (proGamma A f L alpha K) := by
  have hc := intrinsicOriginCounit A Y K hK
  have hi : IsIso (originInverse A Y K) := by
    dsimp only [originInverse]
    rw [dif_pos hc]
    infer_instance
  have := (smooth_tensor_duality A N hN hA hY f d).2 ((origin A Y).obj K)
  unfold proGamma sourceToOrigin gamma
  infer_instance

private theorem proObjectsCtf
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (hY : ∀ y : Y, IsUnit (N : Y.presheaf.stalk y))
    (L : DerivedCategoryModule A X) (alpha : dualizingComplex A f ≅ L)
    (K : proCategory A Y) (hK : IsCtf A Y K) :
    IsCtf A X ((proSource A f L).obj K) ∧ IsCtf A X ((exceptional A f).obj K) := by
  have hNY : IsUnit (N : Γ(Y, ⊤)) := by
    apply Y.toRingedSpace.isUnit_of_isUnit_germ
    intro y hy
    simpa only [map_natCast] using hY y
  have : HasInvertibleExponent A Y := ⟨N, hN, hA, hNY⟩
  have he : IsCtf A X ((exceptional A f).obj K) :=
    comparisonCtf A X _ (ordinaryExceptionalCtf A f d _ (actualOriginCtf A Y K hK))
  have := proGammaIso A N hN hA f d hY L alpha K hK
  exact ⟨isCtfOfIso A X (asIso (proGamma A f L alpha K)).symm he, he⟩

section
-- Avoid unfolding the derived monoidal implementation during bound transport.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
end AlgebraicGeometry.Etale.FiniteSmoothPurity
