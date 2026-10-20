/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.Paper.FiniteSmoothAdjunctionData
import Sheaf.AlgebraicGeometry.SmoothTensorDuality
import Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility
import Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
import Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalObjectComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

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
    (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]
    {FC : A → A → Type w} {CC : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    [(rightDerivedLowerShriek A f).IsLeftAdjoint]
    [hPF : IsIso (projectionMap A f)]
    {K L : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A)} (a : K ⟶ L) :
    ((derivedTensor A X).map ((upperStar A f).leftDerivedFunctor.map a)).app
        (dualizingComplex A f) ≫ smoothTensorDualityMap A f hPF L =
      smoothTensorDualityMap A f hPF K ≫ (rightDerivedUpperShriek A f).map a := by
  let := smoothTensorCanonicalDerivedBraiding (Sheaf X.smallEtaleTopology A)
  let := smoothTensorCanonicalDerivedBraiding (Sheaf S.smallEtaleTopology A)
  apply abstractMateNaturality
  intro K L a
  have h := (asIso ((projectionMap A f).app (dualizingComplex A f))).inv.naturality a
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
    (alpha : dualizingComplex (ModuleCat A) f ≅ L)
    {K K' : DerivedCategoryModule A Y} (a : K ⟶ K') :
    (puritySource A f L).map a ≫ gamma A f L alpha K' =
      gamma A f L alpha K ≫ (rightDerivedUpperShriek (ModuleCat A) f).map a := by
  change ((derivedTensor (ModuleCat A) X).map
      ((ordinaryFinitePullback A f).map a)).app L ≫ _ = _
  unfold gamma
  have ht := ((derivedTensor (ModuleCat A) X).map
    ((ordinaryFinitePullback A f).map a)).naturality alpha.inv
  rw [← Category.assoc, ← ht, Category.assoc]
  have hn := directNaturality (ModuleCat A) f a
  change ((derivedTensor (ModuleCat A) X).map
    ((ordinaryFinitePullback A f).map a)).app (dualizingComplex (ModuleCat A) f) ≫
      smoothTensorDualityMap (ModuleCat A) f _ K' =
      smoothTensorDualityMap (ModuleCat A) f _ K ≫
        (rightDerivedUpperShriek (ModuleCat A) f).map a at hn
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
    (alpha : dualizingComplex (ModuleCat A) f ≅ L)
    {K K' : proCategory A Y} (hK : IsCtf A Y K) (hK' : IsCtf A Y K') (a : K ⟶ K') :
    (proSource A f L).map a ≫ proGamma A f L alpha K' =
      proGamma A f L alpha K ≫ (exceptional A f).map a := by
  let g : puritySource A f L ⟶ rightDerivedUpperShriek (ModuleCat A) f :=
    ⟨gamma A f L alpha, fun _ _ a ↦ ordinaryGammaNaturality A f L alpha a⟩
  have h := transportedNaturality (puritySource A f L)
    (rightDerivedUpperShriek (ModuleCat A) f) (comparison A Y) (comparison A X)
    (origin A Y) (proSource A f L) (sourceNatIso A f L) g a
    (originInverse A Y K) (originInverse A Y K')
    (originInverseNaturality A Y hK hK' a)
  have he (M : DerivedCategoryModule A Y) :
      (sourceNatIso A f L).inv.app M = (sourceAtOriginIso A f L M).inv :=
    congrArg Iso.inv (sourceNatIso_app A f L M)
  rw [he, he] at h
  simpa only [proGamma, sourceToOrigin, exceptional, Functor.comp_map,
    Category.assoc, g] using h

private theorem transportedAtOrigin
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (P G : C ⥤ D) (E : C ⥤ C') (H : D ⥤ D') (O : C' ⥤ C) (Q : C' ⥤ D')
    (q : P ⋙ H ≅ E ⋙ Q) (g : P ⟶ G) (adj : E ⊣ O)
    (K₀ : C) (K : C') [IsIso (adj.counit.app K)] (e : E.obj K₀ ⟶ K) :
    q.hom.app K₀ ≫ Q.map e ≫
        (Q.map (inv (adj.counit.app K)) ≫ q.inv.app (O.obj K) ≫ H.map (g.app (O.obj K))) =
      H.map (g.app K₀) ≫ H.map (G.map (adj.unit.app K₀ ≫ O.map e)) := by
  have he : e ≫ inv (adj.counit.app K) = E.map (adj.unit.app K₀ ≫ O.map e) := by
    apply (cancel_mono (adj.counit.app K)).mp
    have hn : E.map (O.map e) ≫ adj.counit.app K =
        adj.counit.app (E.obj K₀) ≫ e := adj.counit.naturality e
    have ht : E.map (adj.unit.app K₀) ≫ adj.counit.app (E.obj K₀) =
        𝟙 (E.obj K₀) := adj.left_triangle_components K₀
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, E.map_comp,
      Category.assoc, hn, ← Category.assoc,
      ht, Category.id_comp]
  rw [← Q.map_comp_assoc, he]
  rw [← reassoc_of% (q.hom.naturality (adj.unit.app K₀ ≫ O.map e))]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← H.map_comp, g.naturality, H.map_comp]

private theorem anyOrigin
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f]
    (L : DerivedCategoryModule A X)
    (alpha : dualizingComplex (ModuleCat A) f ≅ L)
    (K₀ : DerivedCategoryModule A Y)
    (K : proCategory A Y) (hK : IsCtf A Y K)
    (e : (comparison A Y).obj K₀ ≅ K) :
    (sourceAtOriginIso A f L K₀).hom ≫ (proSource A f L).map e.hom ≫
        proGamma A f L alpha K =
      (comparison A X).map (gamma A f L alpha K₀) ≫
        (comparison A X).map ((rightDerivedUpperShriek (ModuleCat A) f).map
          ((ProEtale.derivedComparisonAdjunction (ModuleCat A) Y).unit.app K₀ ≫
            (origin A Y).map e.hom)) := by
  have hc := intrinsicOriginCounit A Y K hK
  let g : puritySource A f L ⟶ rightDerivedUpperShriek (ModuleCat A) f :=
    ⟨gamma A f L alpha, fun _ _ a ↦ ordinaryGammaNaturality A f L alpha a⟩
  have h := transportedAtOrigin (puritySource A f L)
    (rightDerivedUpperShriek (ModuleCat A) f) (comparison A Y) (comparison A X)
    (origin A Y) (proSource A f L) (sourceNatIso A f L) g
    (ProEtale.derivedComparisonAdjunction (ModuleCat A) Y) K₀ K e.hom
  have heh (M : DerivedCategoryModule A Y) :
      (sourceNatIso A f L).hom.app M = (sourceAtOriginIso A f L M).hom :=
    congrArg Iso.hom (sourceNatIso_app A f L M)
  have hei (M : DerivedCategoryModule A Y) :
      (sourceNatIso A f L).inv.app M = (sourceAtOriginIso A f L M).inv :=
    congrArg Iso.inv (sourceNatIso_app A f L M)
  rw [heh, hei] at h
  simpa only [proGamma, sourceToOrigin, originInverse, dif_pos hc,
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

private theorem traceTransport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f]
    (L : DerivedCategoryModule A X)
    (alpha : dualizingComplex (ModuleCat A) f ≅ L)
    (K₀ : DerivedCategoryModule A Y)
    (K : proCategory A Y) (hK : IsCtf A Y K)
    (e : (comparison A Y).obj K₀ ≅ K)
    (hM : _root_.DerivedCategory.TStructure.t.plus ((puritySource A f L).obj K₀))
    (hM' : _root_.DerivedCategory.TStructure.t.plus
      ((rightDerivedUpperShriek (ModuleCat A) f).obj ((origin A Y).obj K))) :
    (proCompact A f).map
        ((sourceAtOriginIso A f L K₀).hom ≫ (proSource A f L).map e.hom) ≫
        proTrace A f L alpha K =
      compactSiteMap A f ((puritySource A f L).obj K₀) ≫
        (comparison A Y).map (trace A f L alpha K₀) ≫ e.hom := by
  have ha : ((sourceAtOriginIso A f L K₀).hom ≫ (proSource A f L).map e.hom) ≫
      proGamma A f L alpha K =
      (comparison A X).map (gamma A f L alpha K₀) ≫
        (comparison A X).map ((rightDerivedUpperShriek (ModuleCat A) f).map
          ((ProEtale.derivedComparisonAdjunction (ModuleCat A) Y).unit.app K₀ ≫
            (origin A Y).map e.hom)) := by
    simpa only [Category.assoc] using anyOrigin A f L alpha K₀ K hK e
  dsimp only [proTrace, proCounit, trace]
  rw [← (proCompact A f).map_comp_assoc, ha]
  exact transportedTrace (rightDerivedLowerShriek (ModuleCat A) f)
    (rightDerivedUpperShriek (ModuleCat A) f)
    (rightDerivedUpperShriekAdjunction (ModuleCat A) f)
    (comparison A Y) (comparison A X) (origin A Y)
    (ProEtale.derivedComparisonAdjunction (ModuleCat A) Y)
    (proCompact A f) K₀ K e.hom ((puritySource A f L).obj K₀)
    (gamma A f L alpha K₀) _ _
    (compactSiteNaturality A f hM hM' _)

private theorem counitCoordinates
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' P : D ⥤ C}
    (adj : F ⊣ G) (adj' : F' ⊣ G') (s : F ≅ F') (u : P ≅ G')
    (K : D) (M : C) (g : M ⟶ G.obj K) (z : M ⟶ P.obj K)
    (hg : g ≫ ((adj.rightAdjointUniq (adj'.ofNatIsoLeft s.symm)) ≪≫ u.symm).hom.app K = z) :
    F.map g ≫ adj.counit.app K =
      F.map z ≫ s.hom.app (P.obj K) ≫ F'.map (u.hom.app K) ≫ adj'.counit.app K := by
  have hc := adj.rightAdjointUniq_hom_app_counit (adj'.ofNatIsoLeft s.symm) K
  have hgr : g ≫ (adj.rightAdjointUniq (adj'.ofNatIsoLeft s.symm)).hom.app K =
      z ≫ u.hom.app K := by
    apply (cancel_mono (u.inv.app K)).mp
    simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
      Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom] using hg
  rw [← hc, ← F.map_comp_assoc, hgr, F.map_comp]
  simp only [Adjunction.ofNatIsoLeft_counit, Iso.symm_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc]
  rw [reassoc_of% (s.hom.naturality (u.hom.app K))]

private theorem zeroTrace
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [Etale f] [IsSeparated f] [QuasiCompact f]
    (d : ℕ) (hd : d = 0)
    (alpha : dualizingComplex (ModuleCat A) f ≅ line A N hA X d)
    (C : FiniteSmoothCompactSupportComparisons A) (K : DerivedCategoryModule A Y)
    (h : gamma A f (line A N hA X d) alpha K ≫
        (finiteSmoothAdjointCoordinates A C f).hom.app K = zeroSourceMap A N hA f d hd K) :
    trace A f (line A N hA X d) alpha K =
      (rightDerivedLowerShriek (ModuleCat A) f).map (zeroSourceMap A N hA f d hd K) ≫
        (finiteSmoothSumComparison A C f).hom.app _ ≫
        (etaleLowerShriek (ModuleCat A) f inferInstance).mapDerivedCategory.map
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat A) f).hom.app K) ≫
        ((etaleLowerShriekUpperStarAdjunction (ModuleCat A) f
          inferInstance).mapDerivedCategoryAdjunction).counit.app K := by
  exact counitCoordinates (rightDerivedUpperShriekAdjunction (ModuleCat A) f)
    (etaleLowerShriekUpperStarAdjunction (ModuleCat A) f
      inferInstance).mapDerivedCategoryAdjunction
    (finiteSmoothSumComparison A C f)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat A) f) K
    ((puritySource A f (line A N hA X d)).obj K)
    (gamma A f (line A N hA X d) alpha K) (zeroSourceMap A N hA f d hd K) h


private theorem ordinaryExceptionalCtf
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    [HasInvertibleExponent A Y]
    (K : DerivedCategoryModule A Y)
    (hK : DerivedCategory.boundedConstructibleFiniteTor A Y K) :
    DerivedCategory.boundedConstructibleFiniteTor A X
      ((rightDerivedUpperShriek (ModuleCat A) f).obj K) := by
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

private def comparisonUnitIso
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    (comparison A T).obj (𝟙_ _) ≅ 𝟙_ _ :=
  ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A T

private theorem ordinaryUnitCtf
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) :
    DerivedCategory.boundedConstructibleFiniteTor A T (𝟙_ _) := by
  let U := 𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat A))
  have hbc := DerivedCategory.boundedConstructible_singleFunctor_obj U 0
  have ht := torAmplitudeIn_singleFunctor_zero_of_flat (ModuleCat A) U
    (ObjectProperty.prop_unit (ObjectProperty.flat (A := Sheaf T.smallEtaleTopology
      (ModuleCat A))))
  let e := singleFunctorObjUnitIso (ModuleCat A) T
  exact ⟨(DerivedCategory.boundedConstructible (ModuleCat A) T).prop_of_iso e hbc,
    (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso e ⟨0, 0, ht⟩⟩

private theorem unitCtf
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T] : IsCtf A T (𝟙_ _) := by
  exact isCtfOfIso A T (comparisonUnitIso A T)
    (comparisonCtf A T _ (ordinaryUnitCtf A T))

private theorem proGammaIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (hY : ∀ y : Y, IsUnit (N : Y.presheaf.stalk y))
    (L : DerivedCategoryModule A X) (alpha : dualizingComplex (ModuleCat A) f ≅ L)
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
    (L : DerivedCategoryModule A X) (alpha : dualizingComplex (ModuleCat A) f ≅ L)
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

private theorem genericUnitTor
    (C : Type*) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] :
    _root_.DerivedCategory.torAmplitudeIn C 0 0
      (𝟙_ (_root_.DerivedCategory C)) := by
  exact (_root_.DerivedCategory.torAmplitudeIn C 0 0).prop_of_iso
    (_root_.DerivedCategory.singleFunctorObjUnitIso C)
    (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
      (ObjectProperty.prop_unit (ObjectProperty.flat (A := C))))

private theorem ordinaryUnitTor
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    DerivedCategory.torAmplitudeIn (ModuleCat A) T 0 0
      (𝟙_ (DerivedCategoryModule A T)) := by
  exact genericUnitTor (Sheaf T.smallEtaleTopology (ModuleCat A))

private def originUnitIso
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) :
    (𝟙_ (DerivedCategoryModule A T)) ≅
      (origin A T).obj (𝟙_ (proCategory A T)) := by
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app (ModuleCat A) T
    (𝟙_ (DerivedCategoryModule A T)) (ordinaryUnitCtf A T).1.1.1
  exact asIso ((ProEtale.derivedComparisonAdjunction (ModuleCat A) T).unit.app
    (𝟙_ (DerivedCategoryModule A T))) ≪≫ (origin A T).mapIso (comparisonUnitIso A T)

private theorem originUnitTor
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) :
    DerivedCategory.constructibleTorAmplitudeIn (ModuleCat A) T 0 0
      ((origin A T).obj (𝟙_ (proCategory A T))) := by
  have ht := ordinaryUnitTor A T
  have hcon := _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn ht
  have hu : DerivedCategory.constructibleTorAmplitudeIn (ModuleCat A) T 0 0
      (𝟙_ (DerivedCategoryModule A T)) := ⟨⟨(ordinaryUnitCtf A T).1, hcon⟩, ht⟩
  let e := originUnitIso A T
  have := hcon.1
  have := hcon.2
  exact ⟨⟨(DerivedCategory.boundedConstructible (ModuleCat A) T).prop_of_iso e hu.1.1,
    _root_.DerivedCategory.TStructure.t.isGE_of_iso e 0,
    _root_.DerivedCategory.TStructure.t.isLE_of_iso e 0⟩,
    (_root_.DerivedCategory.torAmplitudeIn _ 0 0).prop_of_iso e hu.2⟩

private theorem exceptionalUnitTor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (d : ℕ) [SmoothOfRelativeDimension d f] [HasInvertibleExponent A Y] :
    ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat A) X
      (-(2 * (d : ℤ))) (-(2 * (d : ℤ)))
      ((exceptional A f).obj (𝟙_ (proCategory A Y))) := by
  have h := constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_smoothOfRelativeDimension
    A f d 0 0 (originUnitTor A Y)
  have ht := (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff
    (0 - 2 * (d : ℤ)) (0 - 2 * (d : ℤ))
    ((rightDerivedUpperShriek (ModuleCat A) f).obj
      ((origin A Y).obj (𝟙_ (proCategory A Y))))).mpr h.2
  simpa only [zero_sub, exceptional, comparison, Functor.comp_obj] using ht

private theorem exceptionalUnitDegree
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (d : ℕ) [SmoothOfRelativeDimension d f] [HasInvertibleExponent A Y]
    (i : ℤ) (hi : i ≠ -(2 * (d : ℤ))) :
    IsZero ((_root_.DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat A)) i).obj
        ((exceptional A f).obj (𝟙_ (proCategory A Y)))) := by
  have hcon := _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn
    (exceptionalUnitTor A f d)
  rcases lt_or_gt_of_ne hi with hi | hi
  · exact (_root_.DerivedCategory.isGE_iff _ _).mp hcon.1 i hi
  · exact (_root_.DerivedCategory.isLE_iff _ _).mp hcon.2 i hi

private theorem proUnitDegree
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (hY : ∀ y : Y, IsUnit (N : Y.presheaf.stalk y))
    (L : DerivedCategoryModule A X) (alpha : dualizingComplex (ModuleCat A) f ≅ L)
    (i : ℤ) (hi : i ≠ -(2 * (d : ℤ))) :
    IsZero ((_root_.DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat A)) i).obj
        ((proSource A f L).obj (𝟙_ (proCategory A Y)))) := by
  have hNY : IsUnit (N : Γ(Y, ⊤)) := by
    apply Y.toRingedSpace.isUnit_of_isUnit_germ
    intro y hy
    simpa only [map_natCast] using hY y
  have : HasInvertibleExponent A Y := ⟨N, hN, hA, hNY⟩
  have hz := exceptionalUnitDegree A f d i hi
  have := proGammaIso A N hN hA f d hY L alpha (𝟙_ (proCategory A Y)) (unitCtf A Y)
  exact hz.of_iso ((_root_.DerivedCategory.homologyFunctor
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat A)) i).mapIso
      (asIso (proGamma A f L alpha (𝟙_ (proCategory A Y)))))

end

private theorem ordinaryGammaIsIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (hY : ∀ y : Y, IsUnit (N : Y.presheaf.stalk y))
    (L : DerivedCategoryModule A X) (alpha : dualizingComplex (ModuleCat A) f ≅ L)
    (K : DerivedCategoryModule A Y) : IsIso (gamma A f L alpha K) := by
  have := (smooth_tensor_duality A N hN hA hY f d).2 K
  unfold gamma
  infer_instance

-- Keep derived tensor and bound instances abstract during the final assembly.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Complete the finite-level assertions from a fixed normalized geometric orientation.
Source: sk-thm-smooth-purity, three-factor map and etale/pro-etale transport
(blueprint: lem-pur-finite-smooth-level-of-orientation).
Proof: the canonical tensor mate is invertible by smooth tensor duality. Tensoring
with alpha inverse preserves invertibility and naturality. The finite-ring origin
comparison identifies Rnu_* of each intrinsic constructible finite-Tor object with
its bounded constructible finite-Tor ordinary origin, and its counit is invertible.
Pullback of bounded flat models and tensor with the root line preserve constructibility
and shift Tor bounds by -2d. Transport gamma and its adjunct through the canonical
pullback, tensor and open/proper comparisons. Naturality and the triangular identities
prove independence of origins and the trace equation. In dimension zero, compare the
normalized three factors with the graph-normalized sum adjunction using finite smooth
gamma normalization. At the unit the ordered root tensor has cohomology only in -2d;
transport and purity give the same for its exceptional image. Assemble SmoothLevel
using the supplied geometry, unit and alpha, with no change to its defining maps. -/
theorem finiteSmoothLevelOfOrientation
    (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType f] (d : ℕ) [SmoothOfRelativeDimension d f]
    (hY : ∀ y : Y, IsUnit (ell : Y.presheaf.stalk y))
    (n : ℕ) (hn : 1 ≤ n)
    (G : FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (hX : IsUnit ((ell ^ n : ℕ) : Γ(X, ⊤)))
    (alpha : dualizingComplex (ModuleCat.{u + 1} (coefficient ell n)) f ≅
      line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) X d)
    (hAlpha : OrientationNormalized (coefficient ell n) (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) (CharP.cast_eq_zero _ _) f d G hX alpha) :
    Nonempty (Level ell n f d) := by
  have hZero := finiteSmoothIntrinsicLevelProperties ell f d hY n hn G hX alpha hAlpha
  have hOrigin := actualOriginCtf (coefficient ell n) Y
  have hCounit := intrinsicOriginCounit (coefficient ell n) Y
  have hUnit := unitCtf (coefficient ell n) Y
  have hYn : ∀ y : Y, IsUnit ((ell ^ n : ℕ) : Y.presheaf.stalk y) := by
    intro y
    simpa only [Nat.cast_pow] using (hY y).pow n
  have hCtf := proObjectsCtf (coefficient ell n) (ell ^ n)
    (pow_pos (Fact.out : ell.Prime).pos n) (CharP.cast_eq_zero _ _) f d hYn
    (line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) X d) alpha
  have hOrdinary : ∀ K : DerivedCategoryModule (coefficient ell n) Y,
      IsIso (gamma (coefficient ell n) f
        (line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) X d) alpha K) := by
    intro K
    apply ordinaryGammaIsIso (coefficient ell n) (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) (CharP.cast_eq_zero _ _) f d
    intro y
    simpa only [Nat.cast_pow] using (hY y).pow n
  have hPro : ∀ K : proCategory (coefficient ell n) Y,
      IsCtf (coefficient ell n) Y K →
      IsIso (proGamma (coefficient ell n) f
        (line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) X d) alpha K) := by
    intro K hK
    have hc := hCounit K hK
    have hi : IsIso (originInverse (coefficient ell n) Y K) := by
      dsimp only [originInverse]
      rw [dif_pos hc]
      infer_instance
    have := hOrdinary ((origin (coefficient ell n) Y).obj K)
    unfold proGamma sourceToOrigin
    infer_instance
  refine ⟨{
    geometry := G
    invertible := hX
    alpha := alpha
    orientation := hAlpha
    ordinary_isIso := fun K _ ↦ hOrdinary K
    ordinary_natural := fun K L a ↦ ordinaryGammaNaturality (coefficient ell n) f
      (line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) X d) alpha a
    origin_ctf := hOrigin
    origin_counit := hCounit
    pro_purity := fun K hK ↦ ⟨(hCtf K hK).1, (hCtf K hK).2, hPro K hK⟩
    pro_natural := fun _ _ hK hL a ↦ proNaturality (coefficient ell n) f
      (line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) X d) alpha hK hL a
    any_origin := fun K₀ _ K hK e ↦ anyOrigin (coefficient ell n) f
      (line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) X d) alpha K₀ K hK e
    trace_transport := ?_
    etale_sum := fun _ ↦ by
      obtain ⟨a, C, p, ha, _⟩ := etaleSupportMapCompatibility (coefficient ell n)
      refine ⟨C, a, ?_⟩
      intro V T _ _ _ _ e _ _ _ _ c
      exact (ha e c).2
    dimension_zero := fun hd _ C hC K ↦ ⟨hZero hd C hC K,
      zeroTrace (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) f d hd alpha C K
        (hZero hd C hC K)⟩
    unit_ctf := ⟨hUnit, (hCtf _ hUnit).1, (hCtf _ hUnit).2⟩
    unit_degree := ?_
  }⟩
  · intro K₀ hK₀ K hK e
    have hNY : IsUnit ((ell ^ n : ℕ) : Γ(Y, ⊤)) := by
      apply Y.toRingedSpace.isUnit_of_isUnit_germ
      intro y hy
      simpa only [map_natCast] using hYn y
    have : HasInvertibleExponent (coefficient ell n) Y :=
      ⟨ell ^ n, pow_pos (Fact.out : ell.Prime).pos n, CharP.cast_eq_zero _ _, hNY⟩
    have hM := (ordinaryExceptionalCtf (coefficient ell n) f d K₀ hK₀).1.1.1
    have hM' := (ordinaryExceptionalCtf (coefficient ell n) f d
      ((origin (coefficient ell n) Y).obj K) (hOrigin K hK)).1.1.1
    have := hOrdinary K₀
    exact traceTransport (coefficient ell n) f
      (line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) X d) alpha K₀ K hK e
      (_root_.DerivedCategory.TStructure.t.plus.prop_of_iso
        (asIso (gamma (coefficient ell n) f
          (line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) X d) alpha K₀)).symm hM)
      hM'
  · intro i hi
    have hs := proUnitDegree (coefficient ell n) (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) (CharP.cast_eq_zero _ _) f d hYn
      (line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) X d) alpha i hi
    have := hPro _ hUnit
    exact ⟨hs, hs.of_iso
      ((_root_.DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (coefficient ell n))) i).mapIso
          (asIso (proGamma (coefficient ell n) f
            (line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) X d) alpha
              (𝟙_ _)))).symm⟩

end AlgebraicGeometry.Etale.FiniteSmoothPurity
