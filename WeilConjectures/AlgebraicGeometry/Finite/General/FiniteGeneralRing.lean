/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientPresentation
import WeilConjectures.AlgebraicGeometry.Finite.FiniteScalarDiagonalCompatibility
import WeilConjectures.AlgebraicGeometry.Finite.FiniteOrientationCoefficientCocycle
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothNormalizedExistence
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-! # Smooth purity over an arbitrary finite coefficient ring

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-thm-smooth-purity/sk-thm-smooth-purity-general-ring.md
(blueprint: det-sp-finite-general-ring).

All functors and arrows are the published canonical constructions. In particular,
the exceptional functor is the transported ordinary compact-support right adjoint,
and the direct orientation is normalized by the actual diagonal/Rees/integration equation.

## Main definitions

* `finiteGeneralRingReduction`: the canonical scalar/exceptional comparison at the unit.
* `finiteGeneralRingOrientationExtension`: scalar extension of the recorded orientation.
* `FiniteGeneralRingAt`: the three clauses and Kummer-normalized exponent independence.

## Main statements

* `finiteGeneralRingSmoothPurity`: smooth purity for every finite ell-primary ring.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity.FiniteGeneralRingProof

-- Finite-ring origin, tensor-mate and comparison arguments, specialized from the
-- existing FiniteSmoothLevelOfOrientation proof. No level structure is constructed.

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


end AlgebraicGeometry.Etale.FiniteSmoothPurity.FiniteGeneralRingProof

namespace AlgebraicGeometry.ProEtale

private def sourceInLine (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : Etale.FiniteSmoothPurity.proCategory A Y) :
    Etale.FiniteSmoothPurity.comparison A X ⋙
        (ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((Etale.FiniteSmoothPurity.proPullback A f).obj K) ⟶
      (Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((Etale.ordinaryFinitePullback A f).obj
            ((Etale.FiniteSmoothPurity.origin A Y).obj K)) ⋙
        Etale.FiniteSmoothPurity.comparison A X := by
  let : IsNoetherianRing A := isNoetherian_of_finite A A
  let : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).PreservesFlat :=
    ProEtale.preservesFlat_comparisonUpperStar
  exact Functor.whiskerLeft (Etale.FiniteSmoothPurity.comparison A X)
      ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).map
        ((Etale.FiniteSmoothPurity.proPullback A f).map
            (Etale.FiniteSmoothPurity.originInverse A Y K) ≫
          (Etale.FiniteSmoothPurity.sitePullbackIso A f).hom.app
            ((Etale.FiniteSmoothPurity.origin A Y).obj K))) ≫
    (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A)
      ((Etale.ordinaryFinitePullback A f).obj
        ((Etale.FiniteSmoothPurity.origin A Y).obj K))).inv

private theorem sourceInLine_app (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : Etale.FiniteSmoothPurity.proCategory A Y)
    (L : Etale.DerivedCategoryModule A X) :
    (sourceInLine A f K).app L = Etale.FiniteSmoothPurity.sourceToOrigin A f L K := by
  let : IsNoetherianRing A := isNoetherian_of_finite A A
  let : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).PreservesFlat :=
    ProEtale.preservesFlat_comparisonUpperStar
  simp only [sourceInLine, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.map_comp, NatTrans.comp_app, Etale.FiniteSmoothPurity.sourceToOrigin,
    Etale.FiniteSmoothPurity.proSource, Functor.comp_map,
    Etale.FiniteSmoothPurity.sourceAtOriginIso, Iso.trans_inv,
    Category.assoc]
  rfl

private theorem gammaInLine (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    {L M : Etale.DerivedCategoryModule A X} (b : M ≅ L)
    (alpha : Etale.dualizingComplex A f ≅ L)
    (K : Etale.FiniteSmoothPurity.proCategory A Y) :
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((Etale.FiniteSmoothPurity.proPullback A f).obj K)).map
          ((Etale.FiniteSmoothPurity.comparison A X).map b.hom) ≫
        Etale.FiniteSmoothPurity.proGamma A f L alpha K =
      Etale.FiniteSmoothPurity.sourceToOrigin A f M K ≫
        (Etale.FiniteSmoothPurity.comparison A X).map
          (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
              ((Etale.ordinaryFinitePullback A f).obj
                ((Etale.FiniteSmoothPurity.origin A Y).obj K))).map
                  (b.hom ≫ alpha.inv) ≫
            Etale.smoothTensorDualityMap A f
              (Etale.isIso_projectionMap_of_finite A f)
              ((Etale.FiniteSmoothPurity.origin A Y).obj K)) := by
  have hn := (sourceInLine A f K).naturality b.hom
  rw [sourceInLine_app, sourceInLine_app] at hn
  dsimp only [Functor.comp_map] at hn
  simp only [Etale.FiniteSmoothPurity.proGamma, Etale.FiniteSmoothPurity.gamma,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]

private theorem gammaOrientationEquality (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    {L L' M : Etale.DerivedCategoryModule A X} (b : M ≅ L) (b' : M ≅ L')
    (alpha : Etale.dualizingComplex A f ≅ L)
    (alpha' : Etale.dualizingComplex A f ≅ L')
    (h : alpha.hom ≫ b.inv = alpha'.hom ≫ b'.inv)
    (K : Etale.FiniteSmoothPurity.proCategory A Y) :
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((Etale.FiniteSmoothPurity.proPullback A f).obj K)).map
          ((Etale.FiniteSmoothPurity.comparison A X).map b.hom) ≫
        Etale.FiniteSmoothPurity.proGamma A f L alpha K =
      ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((Etale.FiniteSmoothPurity.proPullback A f).obj K)).map
          ((Etale.FiniteSmoothPurity.comparison A X).map b'.hom) ≫
        Etale.FiniteSmoothPurity.proGamma A f L' alpha' K := by
  have he : b.hom ≫ alpha.inv = b'.hom ≫ alpha'.inv := by
    have hi := congrArg Iso.inv (Iso.ext h : alpha ≪≫ b.symm = alpha' ≪≫ b'.symm)
    exact hi
  rw [gammaInLine, gammaInLine, he]

/-- Smooth purity for every finite commutative ring killed by a positive ell-power.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-thm-smooth-purity/sk-thm-smooth-purity-general-ring.md
(blueprint: det-sp-finite-general-ring).

Proof:
1. Obtain the finite prime quotient and its generator-normalized scalar root line.
   Construct the ordinary orientation by the direct finite diagonal/Rees argument.
   The scalar chart comparison identifies it with coefficient extension of the
   prime orientation. Define theta using the inverse dualizing-unit map; cancellation
   proves both required comparison equations.
2. Intrinsic Dctf objects have ordinary etale origins. Smooth tensor duality makes
   the inverse-projection-formula/counit transpose invertible. Transport through the
   actual comparison counit and tensorator proves the tensor formula, target
   constructibility, finite Tor amplitude and naturality.
3. At the common maximum exponent, use the canonical Kummer power comparisons.
   The coefficient-composition square carries normalization from one exponent to
   the common exponent and then to the other. Cancelling the line isomorphisms
   identifies the inverse orientations. Naturality of the source comparison in
   the line object gives equality of the entire purity maps.
-/
theorem finiteGeneralRingSmoothPurity
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] (d : ℕ) [SmoothOfRelativeDimension d f]
    (n : ℕ) (hn : 1 ≤ n)
    (A : Type u) [CommRing A] [Finite A] (hA : ((ell ^ n : ℕ) : A) = 0) :
    ∃ (hX : IsNoetherian X) (hY : IsNoetherian Y) (hqc : QuasiCompact f),
      ∃ hc : HasCompactification f,
        FiniteGeneralRingAt (finiteGeneralRingPrimeSetting D ell hEll n hn) A
          hA d f (Y ↘ Spec (.of D.k)) hX hY hqc hc := by
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  let : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of D.k))
  let hX : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of D.k))
  let hY : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of D.k))
  let hqc : QuasiCompact f := inferInstance
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  have : LocallyOfFiniteType f := inferInstance
  -- The Noetherian target is quasi-compact and quasi-separated, as Nagata requires.
  let hc : HasCompactification f := inferInstance
  let P := finiteGeneralRingPrimeSetting D ell hEll n hn
  let hAU := congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA
  obtain ⟨e, ⟨t⟩⟩ := finitePrimeCoefficientPresentation D ell hEll n hn A hA X
    (P.diagonalExponent_isUnit (f ≫ (Y ↘ Spec (.of D.k))))
  obtain ⟨geometry, alpha, hnorm⟩ :=
    Etale.FiniteSmoothPurity.generalRingNormalizedOrientation (ULift.{u + 1, u} A)
      P.diagonalExponent (pow_pos (Fact.out : ell.Prime).pos n) hAU f d
      (P.diagonalExponent_isUnit (f ≫ (Y ↘ Spec (.of D.k))))
  obtain ⟨hu, hr, heq⟩ := finiteScalarDiagonalCompatibility P A hA
    (finiteGeneralRingCoefficientMap P A hA e) f d (Y ↘ Spec (.of D.k))
    t geometry alpha hnorm
  let := hu
  let theta := (asIso (finiteGeneralRingDualizingUnitMap (ULift.{u + 1, u} A) f)).symm ≪≫
    (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1, u} A) X).mapIso alpha
  refine ⟨hX, hY, hqc, hc, e, t, theta, alpha, geometry, hr, heq, hu, ?_, hnorm, ?_, ?_⟩
  · dsimp only [theta, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    exact IsIso.hom_inv_id_assoc _ _
  · have hN := pow_pos (Fact.out : ell.Prime).pos n
    have hNY : IsUnit ((ell ^ n : ℕ) : Γ(Y, ⊤)) :=
      P.diagonalExponent_isUnit (Y ↘ Spec (.of D.k))
    have hstalk : ∀ y : Y, IsUnit ((ell ^ n : ℕ) : Y.presheaf.stalk y) := by
      intro y
      simpa only [map_natCast] using hNY.map (Y.presheaf.germ ⊤ y trivial).hom
    let : HasInvertibleExponent (ULift.{u + 1, u} A) Y := ⟨ell ^ n, hN, hAU, hNY⟩
    constructor
    · intro K hK
      refine ⟨?_, ?_⟩
      · exact Etale.FiniteSmoothPurity.FiniteGeneralRingProof.comparisonCtf _ X _
          (Etale.FiniteSmoothPurity.FiniteGeneralRingProof.ordinaryExceptionalCtf _ f d _
            (Etale.FiniteSmoothPurity.FiniteGeneralRingProof.actualOriginCtf _ Y K hK))
      · have hc := Etale.FiniteSmoothPurity.FiniteGeneralRingProof.intrinsicOriginCounit _ Y K hK
        have hi : IsIso (Etale.FiniteSmoothPurity.originInverse _ Y K) := by
          dsimp only [Etale.FiniteSmoothPurity.originInverse]
          rw [dif_pos hc]
          infer_instance
        have := (Etale.smooth_tensor_duality _ (ell ^ n) hN hAU hstalk f d).2
          ((Etale.FiniteSmoothPurity.origin _ Y).obj K)
        unfold Etale.FiniteSmoothPurity.proGamma Etale.FiniteSmoothPurity.sourceToOrigin
          Etale.FiniteSmoothPurity.gamma
        infer_instance
    · intro K K' hK hK' a
      exact Etale.FiniteSmoothPurity.FiniteGeneralRingProof.proNaturality _ f _ alpha hK hK' a
  · intro n' hn' hA'
    have hdiv : ell ^ n ∣ ell ^ max n n' := pow_dvd_pow ell (le_max_left n n')
    have hdiv' : ell ^ n' ∣ ell ^ max n n' := pow_dvd_pow ell (le_max_right n n')
    have hM : ((ell ^ max n n' : ℕ) : ULift.{u + 1, u} A) = 0 :=
      (CharP.cast_eq_zero_iff _ (ringChar _) _).mpr
        (dvd_trans ((CharP.cast_eq_zero_iff _ (ringChar _) _).mp hAU) hdiv)
    have hp (k : ℕ) : 0 < ell ^ k := pow_pos (Fact.out : ell.Prime).pos k
    have hmax : 1 ≤ max n n' := hn.trans (le_max_left n n')
    have units (k : ℕ) (hk : 1 ≤ k) : IsUnit ((ell ^ k : ℕ) : Γ(X, ⊤)) :=
      ({ P with level := k, level_pos := hk } :
        WeilConjectures.PurityFiniteSetting).diagonalExponent_isUnit
          (f ≫ (Y ↘ Spec (.of D.k)))
    obtain ⟨_, _, _, laws⟩ := Scheme.etaleFiniteTwistPullback
      (ULift.{u + 1, u} A) (ell ^ n) (hp n) hAU
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hexp⟩ := laws
    obtain ⟨q, powers, hq, hgenerators, _⟩ :=
      hexp (ell ^ max n n') (hp _) hdiv X (units _ hmax)
    obtain ⟨_, _, _, laws'⟩ := Scheme.etaleFiniteTwistPullback
      (ULift.{u + 1, u} A) (ell ^ n') (hp n') hA'
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hexp'⟩ := laws'
    obtain ⟨q', powers', hq', hgenerators', _⟩ :=
      hexp' (ell ^ max n n') (hp _) hdiv' X (units _ hmax)
    let b : Scheme.finiteEtaleTateLine X (ell ^ max n n') (ULift.{u + 1, u} A) hM ≅
        Scheme.finiteEtaleTateLine X (ell ^ n) (ULift.{u + 1, u} A) hAU := powers 1
    let b' : Scheme.finiteEtaleTateLine X (ell ^ max n n') (ULift.{u + 1, u} A) hM ≅
        Scheme.finiteEtaleTateLine X (ell ^ n') (ULift.{u + 1, u} A) hA' := powers' 1
    have hb : FiniteGeneralRingKummerComparison _ _ _ hM hAU X q b :=
      ⟨hq, hgenerators⟩
    have hb' : FiniteGeneralRingKummerComparison _ _ _ hM hA' X q' b' :=
      ⟨hq', hgenerators'⟩
    let c := finiteGeneralRingLevelPower _ _ _ hM hAU X b d
    let c' := finiteGeneralRingLevelPower _ _ _ hM hA' X b' d
    -- Compare both orientations through the common coefficient exponent.
    let alphaM := alpha ≪≫ c.symm
    let alpha' := alphaM ≪≫ c'
    have hnBase : Etale.FiniteSmoothPurity.OrientationNormalized _ (ell ^ n) (hp n)
        hAU f d geometry (units n hn) alpha := hnorm
    have hnM : Etale.FiniteSmoothPurity.OrientationNormalized _ _ (hp _) hM
        f d geometry (units _ hmax) alphaM := by
      apply (finiteOrientationCoefficientCocycle _ _ _ (hp _) (hp n) hdiv hM hAU
        f d geometry (units _ hmax) (units n hn) q b hb alphaM).mpr
      simpa only [alphaM, c, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl] using hnBase
    have hn' := (finiteOrientationCoefficientCocycle _ _ _ (hp _) (hp n') hdiv'
      hM hA' f d geometry (units _ hmax) (units n' hn') q' b' hb' alphaM).mp hnM
    have he : alpha.hom ≫ c.inv = alpha'.hom ≫ c'.inv := by
      simp only [alpha', alphaM, Iso.trans_hom, Iso.symm_hom, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    refine ⟨hM, q, q', b, b', alpha', hb, hb', hn', he, ?_⟩
    intro K _hK
    exact gammaOrientationEquality (ULift.{u + 1, u} A) f c c' alpha alpha' he K

end AlgebraicGeometry.ProEtale
