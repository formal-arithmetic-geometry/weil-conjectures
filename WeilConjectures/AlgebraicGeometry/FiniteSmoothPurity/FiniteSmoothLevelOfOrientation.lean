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

private theorem abstractMateNaturality
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [BraidedCategory C]
    [MonoidalCategory D] [BraidedCategory D]
    (P : D ⥤ C) {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (W : C) (eps : F.obj W ⟶ 𝟙_ D)
    (pi : ∀ K, F.obj (W ⊗ P.obj K) ⟶ F.obj W ⊗ K)
    (hn : ∀ {K L} (a : K ⟶ L),
      F.map (W ◁ P.map a) ≫ pi L = pi K ≫ (F.obj W ◁ a))
    {K L : D} (a : K ⟶ L) :
    (P.map a ▷ W) ≫
      adj.homEquiv _ _ (F.map (β_ (P.obj L) W).hom ≫ pi L ≫
        (β_ (F.obj W) L).hom ≫ (L ◁ eps) ≫ (ρ_ L).hom) =
    adj.homEquiv _ _ (F.map (β_ (P.obj K) W).hom ≫ pi K ≫
        (β_ (F.obj W) K).hom ≫ (K ◁ eps) ≫ (ρ_ K).hom) ≫ G.map a := by
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
  apply congrArg (adj.homEquiv _ _)
  rw [← Category.assoc, ← Functor.map_comp,
    BraidedCategory.braiding_naturality_left, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (hn a)]
  rw [BraidedCategory.braiding_naturality_right_assoc,
    ← whisker_exchange_assoc, rightUnitor_naturality]

private theorem directNaturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    [hPF : IsIso (projectionMap (ModuleCat.{u + 1} A) f)]
    {K L : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (a : K ⟶ L) :
    ((derivedTensor (ModuleCat.{u + 1} A) X).map
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map a)).app
        (dualizingComplex A f) ≫ smoothTensorDualityMap A f hPF L =
      smoothTensorDualityMap A f hPF K ≫ (rightDerivedUpperShriek A f).map a := by
  let := smoothTensorCanonicalDerivedBraiding (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
  let := smoothTensorCanonicalDerivedBraiding (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
  apply abstractMateNaturality
  intro K L a
  have h := (asIso ((projectionMap (ModuleCat.{u + 1} A) f).app
    (dualizingComplex A f))).inv.naturality a
  simpa only [asIso, NatIso.isIso_inv_app,
    rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar,
    derivedTensorRightDerivedLowerShriek, Functor.comp_map,
    Functor.postcompose₂, Functor.whiskeringLeft₂, Functor.whiskeringRight,
    Functor.whiskeringLeft, Functor.whiskerLeft, Functor.whiskerRight,
    Functor.comp_obj, Functor.id_obj, Functor.id_map,
    rightDerivedLowerShriek, rightDerivedLowerShriekOfCompactification,
    derivedTensor_obj_map] using h

private theorem ordinaryGammaNaturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (L : DerivedCategoryModule A X)
    (alpha : dualizingComplex A f ≅ L)
    {K K' : DerivedCategoryModule A Y} (a : K ⟶ K') :
    (puritySource A f L).map a ≫ gamma A f L alpha K' =
      gamma A f L alpha K ≫ (rightDerivedUpperShriek A f).map a := by
  change ((derivedTensor (ModuleCat A) X).map
      ((ordinaryFinitePullback A f).map a)).app L ≫ _ = _
  unfold gamma
  have ht := ((derivedTensor (ModuleCat A) X).map
    ((ordinaryFinitePullback A f).map a)).naturality alpha.inv
  rw [← Category.assoc, ← ht, Category.assoc]
  have hn := directNaturality A f a
  change ((derivedTensor (ModuleCat A) X).map
    ((ordinaryFinitePullback A f).map a)).app (dualizingComplex A f) ≫
      smoothTensorDualityMap A f _ K' =
      smoothTensorDualityMap A f _ K ≫
        (rightDerivedUpperShriek A f).map a at hn
  rw [hn, Category.assoc]

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

private theorem tensorTransport_app
    (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar C X).PreservesFlat]
    (K Q : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    ((tensorTransport (derivedTensor C X) (ProEtale.derivedTensor C X)
      (ProEtale.comparisonUpperStar C X).leftDerivedFunctorIsoMapDerivedCategory
      (asIso (ProEtale.comparisonUpperStar C X).leftDerivedTensorComparison)).hom.app K).app Q =
      ((ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso C K).app Q).hom := by
  dsimp [tensorTransport,
    ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso]
  rfl

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

private theorem sourceTransport_app
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (P : C ⥤ D) (E : C ⥤ C') (H : D ⥤ D') (Q : C' ⥤ D')
    (T : D ⥤ D ⥤ D) (U : D' ⥤ D' ⥤ D')
    (t : (Functor.postcompose₂.obj H).obj T ≅
      (((Functor.whiskeringLeft₂ D').obj H).obj H).obj U)
    (q : E ⋙ Q ≅ P ⋙ H) (L : D) (K : C) :
    (sourceTransport P E H Q T U t q L).hom.app K =
      (t.hom.app (P.obj K)).app L ≫ (U.map (q.inv.app K)).app (H.obj L) := by
  simp [sourceTransport]

private def tensorSourceTransport
    (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar C X).PreservesFlat]
    {B B' : Type*} [Category B] [Category B']
    (P : B ⥤ _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (E : B ⥤ B') (Q : B' ⥤ _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C))
    (q : E ⋙ Q ≅ P ⋙ (ProEtale.comparisonUpperStar C X).mapDerivedCategory)
    (L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) :=
  sourceTransport P E (ProEtale.comparisonUpperStar C X).mapDerivedCategory Q
    (derivedTensor C X) (ProEtale.derivedTensor C X)
    (tensorTransport (derivedTensor C X) (ProEtale.derivedTensor C X)
      (ProEtale.comparisonUpperStar C X).leftDerivedFunctorIsoMapDerivedCategory
      (asIso (ProEtale.comparisonUpperStar C X).leftDerivedTensorComparison)) q L

private theorem tensorSourceTransport_app
    (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar C X).PreservesFlat]
    {B B' : Type*} [Category B] [Category B']
    (P : B ⥤ _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (E : B ⥤ B') (Q : B' ⥤ _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C))
    (q : E ⋙ Q ≅ P ⋙ (ProEtale.comparisonUpperStar C X).mapDerivedCategory)
    (L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) (K : B) :
    (tensorSourceTransport C X P E Q q L).app K =
      (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso C
        (P.obj K)).app L ≪≫
        ((ProEtale.derivedTensor C X).mapIso (q.app K).symm).app
          ((ProEtale.comparisonUpperStar C X).mapDerivedCategory.obj L) := by
  apply Iso.ext
  have h := sourceTransport_app P E (ProEtale.comparisonUpperStar C X).mapDerivedCategory Q
    (derivedTensor C X) (ProEtale.derivedTensor C X)
    (tensorTransport (derivedTensor C X) (ProEtale.derivedTensor C X)
      (ProEtale.comparisonUpperStar C X).leftDerivedFunctorIsoMapDerivedCategory
      (asIso (ProEtale.comparisonUpperStar C X).leftDerivedTensorComparison)) q L K
  have ht := tensorTransport_app C X (P.obj K) L
  exact h.trans (congrArg (fun a ↦ a ≫
    ((ProEtale.derivedTensor C X).map (q.inv.app K)).app
      ((ProEtale.comparisonUpperStar C X).mapDerivedCategory.obj L)) ht)

private def sourceNatIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : DerivedCategoryModule A X) :
    puritySource A f L ⋙ comparison A X ≅ comparison A Y ⋙ proSource A f L := by
  letI : IsNoetherianRing A := isNoetherian_of_finite A A
  letI : (ProEtale.comparisonUpperStar (ModuleCat A) X).PreservesFlat :=
    ProEtale.preservesFlat_comparisonUpperStar
  exact tensorSourceTransport (ModuleCat A) X (ordinaryFinitePullback A f)
    (comparison A Y) (proPullback A f) (sitePullbackIso A f) L

private theorem sourceNatIso_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : DerivedCategoryModule A X)
    (K : DerivedCategoryModule A Y) :
    (sourceNatIso A f L).app K = sourceAtOriginIso A f L K := by
  let : IsNoetherianRing A := isNoetherian_of_finite A A
  let : (ProEtale.comparisonUpperStar (ModuleCat A) X).PreservesFlat :=
    ProEtale.preservesFlat_comparisonUpperStar
  exact tensorSourceTransport_app (ModuleCat A) X (ordinaryFinitePullback A f)
    (comparison A Y) (proPullback A f) (sitePullbackIso A f) L K

private theorem originInverseNaturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (Y : Scheme.{u}) [IsNoetherian Y]
    {K K' : proCategory A Y} (hK : IsCtf A Y K) (hK' : IsCtf A Y K') (a : K ⟶ K') :
    a ≫ originInverse A Y K' =
      originInverse A Y K ≫ (comparison A Y).map ((origin A Y).map a) := by
  have hc := intrinsicOriginCounit A Y K hK
  have hc' := intrinsicOriginCounit A Y K' hK'
  dsimp only [originInverse]
  rw [dif_pos hc, dif_pos hc']
  apply (cancel_mono
    ((ProEtale.derivedComparisonAdjunction (ModuleCat A) Y).counit.app K')).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [show (comparison A Y).map ((origin A Y).map a) ≫
    (ProEtale.derivedComparisonAdjunction (ModuleCat A) Y).counit.app K' =
    (ProEtale.derivedComparisonAdjunction (ModuleCat A) Y).counit.app K ≫ a from
    (ProEtale.derivedComparisonAdjunction (ModuleCat A) Y).counit.naturality a]
  simp

private theorem transportedNaturality
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (P G : C ⥤ D) (E : C ⥤ C') (H : D ⥤ D') (O : C' ⥤ C) (Q : C' ⥤ D')
    (q : P ⋙ H ≅ E ⋙ Q) (g : P ⟶ G)
    {K K' : C'} (a : K ⟶ K')
    (u : K ⟶ E.obj (O.obj K)) (u' : K' ⟶ E.obj (O.obj K'))
    (hu : a ≫ u' = u ≫ E.map (O.map a)) :
    Q.map a ≫ (Q.map u' ≫ q.inv.app (O.obj K') ≫ H.map (g.app (O.obj K'))) =
      (Q.map u ≫ q.inv.app (O.obj K) ≫ H.map (g.app (O.obj K))) ≫
        H.map (G.map (O.map a)) := by
  rw [← Q.map_comp_assoc, hu, Q.map_comp_assoc]
  rw [reassoc_of% (q.inv.naturality (O.map a))]
  simp only [Category.assoc]
  rw [← H.map_comp, g.naturality, H.map_comp]

private theorem proNaturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f]
    (L : DerivedCategoryModule A X)
    (alpha : dualizingComplex A f ≅ L)
    {K K' : proCategory A Y} (hK : IsCtf A Y K) (hK' : IsCtf A Y K') (a : K ⟶ K') :
    (proSource A f L).map a ≫ proGamma A f L alpha K' =
      proGamma A f L alpha K ≫ (exceptional A f).map a := by
  let g : puritySource A f L ⟶ rightDerivedUpperShriek A f :=
    ⟨gamma A f L alpha, fun _ _ a ↦ ordinaryGammaNaturality A f L alpha a⟩
  have h := transportedNaturality (puritySource A f L)
    (rightDerivedUpperShriek A f) (comparison A Y) (comparison A X)
    (origin A Y) (proSource A f L) (sourceNatIso A f L) g a
    (originInverse A Y K) (originInverse A Y K')
    (originInverseNaturality A Y hK hK' a)
  have he (M : DerivedCategoryModule A Y) :
      (sourceNatIso A f L).inv.app M = (sourceAtOriginIso A f L M).inv :=
    congrArg Iso.inv (sourceNatIso_app A f L M)
  rw [he, he] at h
  simpa only [proGamma, sourceToOrigin, exceptional, Functor.comp_map,
    Category.assoc, g] using h

private theorem compactSiteNaturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    {M M' : DerivedCategoryModule A X}
    (hM : _root_.DerivedCategory.TStructure.t.plus M)
    (hM' : _root_.DerivedCategory.TStructure.t.plus M') (a : M ⟶ M') :
    (proCompact A f).map ((comparison A X).map a) ≫ compactSiteMap A f M' =
      compactSiteMap A f M ≫
        (comparison A Y).map ((rightDerivedLowerShriek (ModuleCat A) f).map a) := by
  dsimp only [compactSiteMap]
  rw [dif_pos hM, dif_pos hM']
  exact (ProEtale.compactSupportSiteComparison A
    (HasCompactification.compactification f)).hom.naturality
      (show (⟨M, hM⟩ : _root_.DerivedCategory.Plus _) ⟶ ⟨M', hM'⟩ from ObjectProperty.homMk a)

private theorem transportedTrace
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (F : D ⥤ C) (G : C ⥤ D) (adjF : F ⊣ G)
    (E : C ⥤ C') (H : D ⥤ D') (O : C' ⥤ C) (adj : E ⊣ O)
    (F' : D' ⥤ C') (K₀ : C) (K : C') (e : E.obj K₀ ⟶ K)
    (M : D) (g : M ⟶ G.obj K₀)
    (b : F'.obj (H.obj M) ⟶ E.obj (F.obj M))
    (b' : F'.obj (H.obj (G.obj (O.obj K))) ⟶ E.obj (F.obj (G.obj (O.obj K))))
    (hn : F'.map (H.map (g ≫ G.map (adj.unit.app K₀ ≫ O.map e))) ≫ b' =
      b ≫ E.map (F.map (g ≫ G.map (adj.unit.app K₀ ≫ O.map e)))) :
    F'.map (H.map g ≫ H.map (G.map (adj.unit.app K₀ ≫ O.map e))) ≫
      b' ≫ E.map (adjF.counit.app (O.obj K)) ≫ adj.counit.app K =
        b ≫ E.map (F.map g ≫ adjF.counit.app K₀) ≫ e := by
  have hnF : F.map (G.map (adj.unit.app K₀ ≫ O.map e)) ≫
      adjF.counit.app (O.obj K) =
      adjF.counit.app K₀ ≫ (adj.unit.app K₀ ≫ O.map e) :=
    adjF.counit.naturality _
  have hnE : E.map (O.map e) ≫ adj.counit.app K =
      adj.counit.app (E.obj K₀) ≫ e := adj.counit.naturality e
  have ht : E.map (adj.unit.app K₀) ≫ adj.counit.app (E.obj K₀) =
      𝟙 (E.obj K₀) := adj.left_triangle_components K₀
  have hε := congrArg E.map hnF
  simp only [E.map_comp] at hε
  rw [← H.map_comp, ← Category.assoc, hn]
  rw [F.map_comp, E.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hε]
  rw [E.map_comp]
  simp only [Category.assoc]
  rw [hnE, reassoc_of% ht]

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
