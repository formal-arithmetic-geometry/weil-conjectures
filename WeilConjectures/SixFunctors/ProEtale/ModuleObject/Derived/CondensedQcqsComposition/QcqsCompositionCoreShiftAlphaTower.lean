/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedQcqsComposition.CondensedQcqsCompositionDefs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedQcqsComposition.QcqsTowerNormalizationLaw
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedDirectCompositorNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdjunctionShift
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition

open CondensedOpenProper CompactSupportComposition

-- Use the existing adjunction shifts of the native compactification functors.
private abbrev nativeModulePushforwardShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (moduleObjectDerivedPushforward Λ f).CommShift ℤ :=
  commShift_rightDerivedLowerStar Λ f

attribute [local instance] nativeModulePushforwardShift

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

-- The following model-comparison calculations are the private calculations of
-- CondensedTowerCompositorNormalization, applied before any finite-Tor restriction.
attribute [-instance] modulePushforwardDerivedCommShift in
private theorem mateComponent
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) {G : C ⥤ E} {H : D ⥤ F}
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (M : D) :
    (mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ α)).natTrans.app M =
      a₂.unit.app (G.obj (R₁.obj M)) ≫
        R₂.map (α.app (R₁.obj M)) ≫ R₂.map (H.map (a₁.counit.app M)) := by
  simp [mateEquiv_apply, TwoSquare.mk, TwoSquare.natTrans]

attribute [-instance] modulePushforwardDerivedCommShift in
private theorem transposeComponent
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) (F : E ⥤ C) (G : E ⥤ D)
    (α : F ⟶ G ⋙ R) (M : E) :
    ((Functor.leftUnitor (F ⋙ L)).inv ≫ Functor.whiskerRight α L ≫
      (Functor.associator G R L).hom ≫ Functor.whiskerLeft G a.counit ≫
      (Functor.rightUnitor G).hom).app M =
        (a.homEquiv (F.obj M) (G.obj M)).symm (α.app M) := by
  simp [Adjunction.homEquiv_counit]

attribute [-instance] modulePushforwardDerivedCommShift in
private theorem restrictionComponent
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (J : C ⥤ D) (R : D ⥤ E) (P : E ⥤ F) (Q : C ⥤ F) (U : D ⥤ C)
    (α : R ⋙ P ⟶ U ⋙ Q) (β : J ⋙ U ⟶ 𝟭 C) (M : C) :
    ((Functor.associator _ _ _).hom ≫ Functor.whiskerLeft J α ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight β Q ≫
      (Functor.leftUnitor _).hom).app M = α.app (J.obj M) ≫ Q.map (β.app M) := by
  simp

attribute [-instance] modulePushforwardDerivedCommShift in
attribute [-instance] modulePushforwardDerivedCommShift in
private theorem openComp_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (j : X ⟶ Y) (i : Y ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion i] :
    CompactSupportComposition.openComp Λ j i = jComp Λ j i := by
  apply Iso.ext
  ext K
  simp [CompactSupportComposition.openComp, jComp, pComp, Adjunction.leftAdjointUniq,
    conjugateEquiv_symm_apply_app, Adjunction.ofNatIsoRight_unit,
    Functor.map_comp, Category.assoc]

attribute [-instance] modulePushforwardDerivedCommShift in
private theorem openFactor_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}}
    (j : X ⟶ Y) (i : Y ⟶ Z) (h : X ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion h] (e : j ≫ i = h) :
    CompactSupportComposition.openFactor Λ j i h e =
      jComp Λ j i ≪≫ jCongr Λ e := by
  subst h
  unfold CompactSupportComposition.openFactor
  rw [openComp_eq]
  simp only [jCongr, eqToIso_refl, Iso.trans_refl]

attribute [-instance] modulePushforwardDerivedCommShift in
private theorem restrictionComparison_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (p : X ⟶ Y) (i : Y ⟶ Z)
    [IsOpenImmersion i] (c : Compactification.BoundaryCompactification (p ≫ i))
    (M : D Λ c.obj.obj.Z) :
    compositionInterchangeRestriction Λ p i c M =
      (derivedDirectImageOpenRestriction Λ ⟨c.obj.obj.comm.symm⟩).app M := by
  unfold compositionInterchangeRestriction
  rw [exactAdjunction_eq, exactAdjunction_eq]
  conv_rhs => rw [derivedDirectImageOpenRestriction, mateComponent]
  conv_lhs => rw [Adjunction.homEquiv_unit, Functor.map_comp]
  rfl

section Normalization

attribute [local irreducible] derivedOpenImmersionLowerShriekUpperStarAdjunction
  derivedUpperStarLowerStarAdjunction leftDerivedUpperStarIsoMapDerivedCategory
  Functor.rightDerivedFunctorNatIso

set_option maxHeartbeats 2000000 in
-- Comparing ambient derived models requires elaborating the full adjunctions.
attribute [-instance] modulePushforwardDerivedCommShift in
private theorem normalized_eq_gamma
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (B : Pasting Λ)
    {X Y Z : Scheme.{u}} (p : X ⟶ Y) (i : Y ⟶ Z) [IsOpenImmersion i]
    (c : Compactification.BoundaryCompactification (p ≫ i))
    [QuasiCompact i] (sq : IsPullback c.obj.obj.i p c.obj.obj.g i)
    (M : D Λ X)
    (m : (J Λ i).obj ((R Λ p).obj M) ⟶
      (R Λ c.obj.obj.g).obj ((J Λ c.obj.obj.i).obj M))
    (hm : compositionInterchangeIsNormalized Λ p i c M m) :
    m = (gamma Λ B.units sq.toCommSq).app M := by
  have : QuasiCompact c.obj.obj.i := c.obj.property
  let a := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i
  let ρ := restriction Λ B.units sq.toCommSq
  have hρ : IsIso ρ := B.restriction_isIso sq.toCommSq (Or.inl sq)
  have hγ : (gamma Λ B.units sq.toCommSq).app M =
      (a.homEquiv _ _).symm ((comparisonInverse ρ).app M) := by
    exact transposeComponent a (R Λ p) (J Λ c.obj.obj.i ⋙ R Λ c.obj.obj.g)
      (comparisonInverse ρ) M
  rw [hγ]
  apply (a.homEquiv _ _).injective
  simp only [Functor.comp_obj, Equiv.apply_symm_apply]
  apply (cancel_mono (ρ.app M)).mp
  have hinv : comparisonInverse ρ = inv ρ := by
    simp only [comparisonInverse, dif_pos hρ]
  rw [hinv]
  conv_rhs => rw [← NatTrans.comp_app, IsIso.inv_hom_id, NatTrans.id_app]
  rw [show ρ.app M =
      (derivedDirectImageOpenRestriction Λ sq.toCommSq).app
          ((J Λ c.obj.obj.i).obj M) ≫
        (R Λ p).map ((B.units.unitIso c.obj.obj.i).inv.app M) from
      restrictionComponent _ _ _ _ _ _ _ M]
  change a.homEquiv _ _ m ≫
      ((derivedDirectImageOpenRestriction Λ sq.toCommSq).app
          ((J Λ c.obj.obj.i).obj M) ≫
        (R Λ p).map ((B.units.unitIso c.obj.obj.i).inv.app M)) = _
  rw [← Category.assoc]
  have hm' := hm
  unfold compositionInterchangeIsNormalized at hm'
  rw [restrictionComparison_eq] at hm'
  dsimp only [a, R, J, moduleObjectDerivedPushforward]
  rw [hm']
  rw [← Functor.map_comp]
  have hu := congrArg (fun t ↦ t.app M) (B.units.normalized c.obj.obj.i)
  rw [← hu, Iso.hom_inv_id_app]
  exact CategoryTheory.Functor.map_id _ M

end Normalization

attribute [local semireducible] Functor.mapDerivedCategory

attribute [-instance] modulePushforwardDerivedCommShift in
attribute [-instance] modulePushforwardDerivedCommShift in
private theorem exactAdjunction_shift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction.CommShift ℤ := by
  rw [← exactAdjunction_eq]
  exact Adjunction.commShift_ofNatIsoLeft _ _

attribute [-instance] modulePushforwardDerivedCommShift in
private theorem derivedDirectImageOpenRestriction_shiftTriangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] {X Y X' Y' : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {b : Y' ⟶ Y} (sq : CommSq a f' f b) :
    NatTrans.CommShift (derivedDirectImageOpenRestriction Λ sq) ℤ := by
  have hlocal1 :
      (upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction.CommShift ℤ :=
    exactAdjunction_shift Λ f
  have hlocal2 :
      (upperStarLowerStarAdjunction Λ f').mapDerivedCategoryRightDerivedAdjunction.CommShift ℤ :=
    exactAdjunction_shift Λ f'
  have : NatTrans.CommShift (derivedOpenCoherencePullbackSquare Λ sq).hom ℤ := by
    dsimp only [derivedOpenCoherencePullbackSquare, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  have : NatTrans.CommShift (derivedDirectImageOpenRestriction Λ sq) ℤ :=
    NatTrans.CommShift.mateEquiv (A := ℤ)
      (upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction
      (upperStarLowerStarAdjunction Λ f').mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ (derivedOpenCoherencePullbackSquare Λ sq).hom)
  infer_instance

-- Integer-shift compatibility of the normalized proper/open adjunct.
attribute [-instance] modulePushforwardDerivedCommShift in
private theorem gamma_shiftTriangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] {U W Y Z : Scheme.{u}} {j : U ⟶ W} {p : U ⟶ Y}
    {r : W ⟶ Z} {i : Y ⟶ Z} [IsOpenImmersion j] [IsOpenImmersion i]
    [QuasiCompact j] [QuasiCompact i] [IsProper p] [IsProper r]
    (units : OpenUnits Λ) (sq : CommSq j p r i) :
    NatTrans.CommShift (gamma Λ units sq) ℤ := by
  have hlocal5 := derivedDirectImageOpenRestriction_shiftTriangle Λ sq
  have : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).CommShift ℤ :=
    (openImmersionLowerShriekUpperStarAdjunction Λ j).commShift_mapDerivedCategoryAdjunction
  have : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).CommShift ℤ :=
    (openImmersionLowerShriekUpperStarAdjunction Λ i).commShift_mapDerivedCategoryAdjunction
  have : NatTrans.CommShift (units.unitIso j).hom ℤ := by
    rw [units.normalized]
    infer_instance
  have : NatTrans.CommShift (restriction Λ units sq) ℤ := by
    dsimp only [restriction]
    infer_instance
  have : NatTrans.CommShift (comparisonInverse (restriction Λ units sq)) ℤ := by
    classical
    unfold comparisonInverse
    split_ifs with h
    · exact NatTrans.CommShift.of_iso_inv (asIso (restriction Λ units sq)) ℤ
    · constructor
      intro n
      ext K
      simp
  have : NatTrans.CommShift (gamma Λ units sq) ℤ :=
    adjunct_commShift (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i)
      (comparisonInverse (restriction Λ units sq))
  infer_instance

attribute [-instance] modulePushforwardDerivedCommShift in
private theorem pComp_shiftTriangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.CommShift (pComp Λ f g).hom ℤ := by
  have : NatTrans.CommShift (pComp Λ f g).hom ℤ := by
    dsimp only [pComp, Iso.trans_hom]
    infer_instance
  infer_instance

attribute [-instance] modulePushforwardDerivedCommShift in
private theorem rComp_shiftTriangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.CommShift (rComp Λ f g).hom ℤ := by
  have hlocal9 := pComp_shiftTriangle Λ f g
  have hlocal10 := exactAdjunction_shift Λ f
  have hlocal11 := exactAdjunction_shift Λ g
  have hlocal12 := exactAdjunction_shift Λ (f ≫ g)
  have : NatTrans.CommShift (rComp Λ f g).hom ℤ := by
    dsimp only [rComp, Iso.symm_hom]
    infer_instance
  infer_instance

-- Integer-shift compatibility of the open compositor.
attribute [-instance] modulePushforwardDerivedCommShift in
private theorem jComp_shiftTriangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (j : X ⟶ Y) (i : Y ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion i] :
    NatTrans.CommShift (jComp Λ j i).hom ℤ := by
  have hlocal13 := pComp_shiftTriangle Λ j i
  have : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).CommShift ℤ :=
    (openImmersionLowerShriekUpperStarAdjunction Λ j).commShift_mapDerivedCategoryAdjunction
  have : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).CommShift ℤ :=
    (openImmersionLowerShriekUpperStarAdjunction Λ i).commShift_mapDerivedCategoryAdjunction
  have : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (j ≫ i)).CommShift ℤ :=
    (openImmersionLowerShriekUpperStarAdjunction Λ (j ≫ i)).commShift_mapDerivedCategoryAdjunction
  have : NatTrans.CommShift (jComp Λ j i).hom ℤ := by
    dsimp only [jComp, Iso.symm_hom]
    infer_instance
  infer_instance

attribute [-instance] modulePushforwardDerivedCommShift in
private theorem jCongr_shift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {j i : X ⟶ Y}
    [IsOpenImmersion j] [IsOpenImmersion i] (h : j = i) :
    NatTrans.CommShift (jCongr Λ h).hom ℤ := by
  subst i
  change NatTrans.CommShift (𝟙 _) ℤ
  infer_instance

attribute [-instance] modulePushforwardDerivedCommShift in
private theorem directCongr_shift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    NatTrans.CommShift (Functor.rightDerivedFunctorNatIso
      (eqToIso (congrArg (lowerStar Λ) h))).hom ℤ := by
  subst g
  simp only [eqToIso_refl, Functor.rightDerivedFunctorNatIso,
    Iso.refl_hom, Functor.rightDerivedFunctorNatTrans, NatTrans.mapHomotopyCategory_id,
    Functor.whiskerRight_id', Functor.rightDerivedNatTrans_id]
  infer_instance

private def towerWord
    {C₀ C₁ C₂ C₃ C₄ C₅ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category C₃] [Category C₄] [Category C₅]
    (J₁ : C₀ ⥤ C₁) (R₁ : C₁ ⥤ C₂) (J₂ : C₂ ⥤ C₃) (R₂ : C₃ ⥤ C₄)
    (Jq : C₁ ⥤ C₅) (Rp : C₅ ⥤ C₃) (Je : C₀ ⥤ C₅)
    (Rc Rf : C₅ ⥤ C₄) (γ : R₁ ⋙ J₂ ⟶ Jq ⋙ Rp) (o : J₁ ⋙ Jq ⟶ Je)
    (r : Rp ⋙ R₂ ⟶ Rc) (e : Rc ⟶ Rf) : (J₁ ⋙ R₁) ⋙ (J₂ ⋙ R₂) ⟶ Je ⋙ Rf :=
  (Functor.associator J₁ R₁ (J₂ ⋙ R₂)).hom ≫
      Functor.whiskerLeft J₁ (Functor.associator R₁ J₂ R₂).inv ≫
      Functor.whiskerLeft J₁ (Functor.whiskerRight γ R₂) ≫
      Functor.whiskerLeft J₁ (Functor.associator Jq Rp R₂).hom ≫
      (Functor.associator J₁ Jq (Rp ⋙ R₂)).inv ≫
      Functor.whiskerRight o (Rp ⋙ R₂) ≫
      Functor.whiskerLeft Je r ≫ Functor.whiskerLeft Je e

-- Evaluate the formal composition word before specializing to derived functors.
private theorem towerComponent
    {C₀ C₁ C₂ C₃ C₄ C₅ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category C₃] [Category C₄] [Category C₅]
    (J₁ : C₀ ⥤ C₁) (R₁ : C₁ ⥤ C₂) (J₂ : C₂ ⥤ C₃) (R₂ : C₃ ⥤ C₄)
    (Jq : C₁ ⥤ C₅) (Rp : C₅ ⥤ C₃) (Je : C₀ ⥤ C₅)
    (Rc Rf : C₅ ⥤ C₄) (γ : R₁ ⋙ J₂ ⟶ Jq ⋙ Rp) (o : J₁ ⋙ Jq ⟶ Je)
    (r : Rp ⋙ R₂ ⟶ Rc) (e : Rc ⟶ Rf) (K : C₀) :
    ((Functor.associator J₁ R₁ (J₂ ⋙ R₂)).hom ≫
      Functor.whiskerLeft J₁ (Functor.associator R₁ J₂ R₂).inv ≫
      Functor.whiskerLeft J₁ (Functor.whiskerRight γ R₂) ≫
      Functor.whiskerLeft J₁ (Functor.associator Jq Rp R₂).hom ≫
      (Functor.associator J₁ Jq (Rp ⋙ R₂)).inv ≫
      Functor.whiskerRight o (Rp ⋙ R₂) ≫
      Functor.whiskerLeft Je r ≫ Functor.whiskerLeft Je e).app K =
        R₂.map (γ.app (J₁.obj K) ≫ Rp.map (o.app K)) ≫
          r.app (Je.obj K) ≫ e.app (Je.obj K) := by
  simp [Functor.map_comp, Category.assoc]

-- Keep the component formula explicit at native derived-functor applications.
private def compactTowerWord
    {C₀ C₁ C₂ C₃ C₄ C₅ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category C₃] [Category C₄] [Category C₅]
    (J₁ : C₀ ⥤ C₁) (R₁ : C₁ ⥤ C₂) (J₂ : C₂ ⥤ C₃) (R₂ : C₃ ⥤ C₄)
    (Jq : C₁ ⥤ C₅) (Rp : C₅ ⥤ C₃) (Je : C₀ ⥤ C₅)
    (Rc Rf : C₅ ⥤ C₄) (γ : R₁ ⋙ J₂ ⟶ Jq ⋙ Rp) (o : J₁ ⋙ Jq ⟶ Je)
    (r : Rp ⋙ R₂ ⟶ Rc) (e : Rc ⟶ Rf) : (J₁ ⋙ R₁) ⋙ (J₂ ⋙ R₂) ⟶ Je ⋙ Rf where
  app K := R₂.map (γ.app (J₁.obj K) ≫ Rp.map (o.app K)) ≫
    r.app (Je.obj K) ≫ e.app (Je.obj K)
  naturality {K L} f := by
    simpa only [towerWord, towerComponent] using
      (towerWord J₁ R₁ J₂ R₂ Jq Rp Je Rc Rf γ o r e).naturality f

private theorem compactTowerWord_eq
    {C₀ C₁ C₂ C₃ C₄ C₅ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category C₃] [Category C₄] [Category C₅]
    (J₁ : C₀ ⥤ C₁) (R₁ : C₁ ⥤ C₂) (J₂ : C₂ ⥤ C₃) (R₂ : C₃ ⥤ C₄)
    (Jq : C₁ ⥤ C₅) (Rp : C₅ ⥤ C₃) (Je : C₀ ⥤ C₅)
    (Rc Rf : C₅ ⥤ C₄) (γ : R₁ ⋙ J₂ ⟶ Jq ⋙ Rp) (o : J₁ ⋙ Jq ⟶ Je)
    (r : Rp ⋙ R₂ ⟶ Rc) (e : Rc ⟶ Rf) :
    compactTowerWord J₁ R₁ J₂ R₂ Jq Rp Je Rc Rf γ o r e =
      towerWord J₁ R₁ J₂ R₂ Jq Rp Je Rc Rf γ o r e := by
  ext K
  exact (towerComponent J₁ R₁ J₂ R₂ Jq Rp Je Rc Rf γ o r e K).symm

-- Shift calculations in abstract categories, before native specialization.
private theorem towerWordCommShift
    {C₀ C₁ C₂ C₃ C₄ C₅ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category C₃] [Category C₄] [Category C₅]
    [HasShift C₀ ℤ] [HasShift C₁ ℤ] [HasShift C₂ ℤ]
    [HasShift C₃ ℤ] [HasShift C₄ ℤ] [HasShift C₅ ℤ]
    (J₁ : C₀ ⥤ C₁) (R₁ : C₁ ⥤ C₂) (J₂ : C₂ ⥤ C₃) (R₂ : C₃ ⥤ C₄)
    (Jq : C₁ ⥤ C₅) (Rp : C₅ ⥤ C₃) (Je : C₀ ⥤ C₅) (Rc Rf : C₅ ⥤ C₄)
    [J₁.CommShift ℤ] [R₁.CommShift ℤ] [J₂.CommShift ℤ] [R₂.CommShift ℤ]
    [Jq.CommShift ℤ] [Rp.CommShift ℤ] [Je.CommShift ℤ] [Rc.CommShift ℤ] [Rf.CommShift ℤ]
    (γ : R₁ ⋙ J₂ ⟶ Jq ⋙ Rp) (o : J₁ ⋙ Jq ⟶ Je)
    (r : Rp ⋙ R₂ ⟶ Rc) (e : Rc ⟶ Rf)
    [NatTrans.CommShift γ ℤ] [NatTrans.CommShift o ℤ]
    [NatTrans.CommShift r ℤ] [NatTrans.CommShift e ℤ] :
    NatTrans.CommShift
      ((Functor.associator J₁ R₁ (J₂ ⋙ R₂)).hom ≫
        Functor.whiskerLeft J₁ (Functor.associator R₁ J₂ R₂).inv ≫
        Functor.whiskerLeft J₁ (Functor.whiskerRight γ R₂) ≫
        Functor.whiskerLeft J₁ (Functor.associator Jq Rp R₂).hom ≫
        (Functor.associator J₁ Jq (Rp ⋙ R₂)).inv ≫
        Functor.whiskerRight o (Rp ⋙ R₂) ≫
        Functor.whiskerLeft Je r ≫ Functor.whiskerLeft Je e) ℤ := by
  infer_instance

private theorem compactTowerWordCommShift
    {C₀ C₁ C₂ C₃ C₄ C₅ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category C₃] [Category C₄] [Category C₅]
    [HasShift C₀ ℤ] [HasShift C₁ ℤ] [HasShift C₂ ℤ]
    [HasShift C₃ ℤ] [HasShift C₄ ℤ] [HasShift C₅ ℤ]
    (J₁ : C₀ ⥤ C₁) (R₁ : C₁ ⥤ C₂) (J₂ : C₂ ⥤ C₃) (R₂ : C₃ ⥤ C₄)
    (Jq : C₁ ⥤ C₅) (Rp : C₅ ⥤ C₃) (Je : C₀ ⥤ C₅) (Rc Rf : C₅ ⥤ C₄)
    [J₁.CommShift ℤ] [R₁.CommShift ℤ] [J₂.CommShift ℤ] [R₂.CommShift ℤ]
    [Jq.CommShift ℤ] [Rp.CommShift ℤ] [Je.CommShift ℤ] [Rc.CommShift ℤ] [Rf.CommShift ℤ]
    (γ : R₁ ⋙ J₂ ⟶ Jq ⋙ Rp) (o : J₁ ⋙ Jq ⟶ Je)
    (r : Rp ⋙ R₂ ⟶ Rc) (e : Rc ⟶ Rf)
    [NatTrans.CommShift γ ℤ] [NatTrans.CommShift o ℤ]
    [NatTrans.CommShift r ℤ] [NatTrans.CommShift e ℤ] :
    NatTrans.CommShift (compactTowerWord J₁ R₁ J₂ R₂ Jq Rp Je Rc Rf γ o r e) ℤ := by
  rw [compactTowerWord_eq]
  exact towerWordCommShift J₁ R₁ J₂ R₂ Jq Rp Je Rc Rf γ o r e

private theorem reflectedWordCommShift
    {C D E Cb Db Eb : Type*}
    [Category C] [Category D] [Category E] [Category Cb] [Category Db] [Category Eb]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    [HasShift Cb ℤ] [HasShift Db ℤ] [HasShift Eb ℤ]
    (I : Cb ⥤ C) (J : Db ⥤ D) (L : Eb ⥤ E) [L.Faithful]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    (Fb : Cb ⥤ Db) (Gb : Db ⥤ Eb) (Hb : Cb ⥤ Eb)
    [I.CommShift ℤ] [J.CommShift ℤ] [L.CommShift ℤ]
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
    [Fb.CommShift ℤ] [Gb.CommShift ℤ] [Hb.CommShift ℤ]
    (a : Fb ⋙ J ≅ I ⋙ F) (b : Gb ⋙ L ≅ J ⋙ G) (c : Hb ⋙ L ≅ I ⋙ H)
    [NatTrans.CommShift a.hom ℤ] [NatTrans.CommShift b.hom ℤ]
    [NatTrans.CommShift c.hom ℤ]
    (τ : F ⋙ G ⟶ H) [NatTrans.CommShift τ ℤ] (α : Fb ⋙ Gb ⟶ Hb)
    (h : Functor.whiskerRight α L =
      (Functor.associator Fb Gb L).hom ≫ Functor.whiskerLeft Fb b.hom ≫
      (Functor.associator Fb J G).inv ≫ Functor.whiskerRight a.hom G ≫
      (Functor.associator I F G).hom ≫ Functor.whiskerLeft I τ ≫ c.inv) :
    NatTrans.CommShift α ℤ := by
  have : NatTrans.CommShift c.inv ℤ := NatTrans.CommShift.of_iso_inv c ℤ
  have : NatTrans.CommShift (Functor.whiskerRight α L) ℤ := by
    apply (congrArg
      (fun η : (Fb ⋙ Gb) ⋙ L ⟶ Hb ⋙ L ↦ NatTrans.CommShift η ℤ) h).mpr
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight _ L

-- Compute the inclusion/lift word in abstract categories.
private theorem restrictedWordComponent
    {C D E : Type*} [Category C] [Category D] [Category E]
    (P : ObjectProperty C) (Q : ObjectProperty D) (R : ObjectProperty E)
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    (hF : ∀ K : P.FullSubcategory, Q (F.obj K.obj))
    (hG : ∀ K : Q.FullSubcategory, R (G.obj K.obj))
    (hH : ∀ K : P.FullSubcategory, R (H.obj K.obj))
    (α : Q.lift (P.ι ⋙ F) hF ⋙ R.lift (Q.ι ⋙ G) hG ⟶ R.lift (P.ι ⋙ H) hH)
    (τ : F ⋙ G ⟶ H) (hα : ∀ K, (α.app K).hom = τ.app K.obj) :
    Functor.whiskerRight α R.ι =
      (Functor.associator (Q.lift (P.ι ⋙ F) hF) (R.lift (Q.ι ⋙ G) hG) R.ι).hom ≫
      Functor.whiskerLeft (Q.lift (P.ι ⋙ F) hF) (R.liftCompιIso _ hG).hom ≫
      (Functor.associator (Q.lift (P.ι ⋙ F) hF) Q.ι G).inv ≫
      Functor.whiskerRight (Q.liftCompιIso _ hF).hom G ≫
      (Functor.associator P.ι F G).hom ≫ Functor.whiskerLeft P.ι τ ≫
      (R.liftCompιIso _ hH).inv := by
  ext K
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    ObjectProperty.lift, ObjectProperty.liftCompιIso, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Functor.comp_obj, Functor.comp_map, ObjectProperty.ι_obj, ObjectProperty.ι_map,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] using hα K

-- Restrict a shift-compatible ambient word using the canonical lifted shift structures.
private theorem restrictedCommShift
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (P : ObjectProperty C) (Q : ObjectProperty D) (S : ObjectProperty E)
    [P.IsStableUnderShift ℤ] [Q.IsStableUnderShift ℤ] [S.IsStableUnderShift ℤ]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
    (hF : ∀ K : P.FullSubcategory, Q (F.obj K.obj))
    (hG : ∀ K : Q.FullSubcategory, S (G.obj K.obj))
    (hH : ∀ K : P.FullSubcategory, S (H.obj K.obj))
    (τ : F ⋙ G ⟶ H) [NatTrans.CommShift τ ℤ]
    (α : Q.lift (P.ι ⋙ F) hF ⋙ S.lift (Q.ι ⋙ G) hG ⟶ S.lift (P.ι ⋙ H) hH)
    (hα : ∀ K, (α.app K).hom = τ.app K.obj) : NatTrans.CommShift α ℤ := by
  let a := Q.liftCompιIso (P.ι ⋙ F) hF
  let b := S.liftCompιIso (Q.ι ⋙ G) hG
  let c := S.liftCompιIso (P.ι ⋙ H) hH
  have ha : NatTrans.CommShift a.hom ℤ := Functor.CommShift.ofComp_compatibility a ℤ
  have hb : NatTrans.CommShift b.hom ℤ := Functor.CommShift.ofComp_compatibility b ℤ
  have hc : NatTrans.CommShift c.hom ℤ := Functor.CommShift.ofComp_compatibility c ℤ
  have hn := restrictedWordComponent P Q S F G H hF hG hH α τ hα
  exact reflectedWordCommShift P.ι Q.ι S.ι F G H
    (Q.lift (P.ι ⋙ F) hF) (S.lift (Q.ι ⋙ G) hG) (S.lift (P.ι ⋙ H) hH)
    a b c τ α hn

-- Apply normalization and shift transport before specializing to native objects.
private theorem normalizedRestrictionCommShift
    {C₀ C₁ C₂ C₃ C₄ C₅ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category C₃] [Category C₄] [Category C₅]
    [HasShift C₀ ℤ] [HasShift C₁ ℤ] [HasShift C₂ ℤ]
    [HasShift C₃ ℤ] [HasShift C₄ ℤ] [HasShift C₅ ℤ]
    (P : ObjectProperty C₀) (Q : ObjectProperty C₂) (S : ObjectProperty C₄)
    [P.IsStableUnderShift ℤ] [Q.IsStableUnderShift ℤ] [S.IsStableUnderShift ℤ]
    (J₁ : C₀ ⥤ C₁) (R₁ : C₁ ⥤ C₂) (J₂ : C₂ ⥤ C₃) (R₂ : C₃ ⥤ C₄)
    (Jq : C₁ ⥤ C₅) (Rp : C₅ ⥤ C₃) (Je : C₀ ⥤ C₅) (Rc Rf : C₅ ⥤ C₄)
    [J₁.CommShift ℤ] [R₁.CommShift ℤ] [J₂.CommShift ℤ] [R₂.CommShift ℤ]
    [Jq.CommShift ℤ] [Rp.CommShift ℤ] [Je.CommShift ℤ] [Rc.CommShift ℤ] [Rf.CommShift ℤ]
    (γ : R₁ ⋙ J₂ ⟶ Jq ⋙ Rp) (o : J₁ ⋙ Jq ⟶ Je)
    (r : Rp ⋙ R₂ ⟶ Rc) (e : Rc ⟶ Rf)
    [NatTrans.CommShift γ ℤ] [NatTrans.CommShift o ℤ]
    [NatTrans.CommShift r ℤ] [NatTrans.CommShift e ℤ]
    (hF : ∀ K : P.FullSubcategory, Q ((J₁ ⋙ R₁).obj K.obj))
    (hG : ∀ K : Q.FullSubcategory, S ((J₂ ⋙ R₂).obj K.obj))
    (hH : ∀ K : P.FullSubcategory, S ((Je ⋙ Rf).obj K.obj))
    (α : Q.lift (P.ι ⋙ (J₁ ⋙ R₁)) hF ⋙ S.lift (Q.ι ⋙ (J₂ ⋙ R₂)) hG ⟶
      S.lift (P.ι ⋙ (Je ⋙ Rf)) hH)
    (N : ∀ M : C₁, (J₂.obj (R₁.obj M) ⟶ Rp.obj (Jq.obj M)) → Prop)
    (hΓ : ∀ M m, N M m → m = γ.app M)
    (hNorm : ∀ K : P.FullSubcategory,
      TowerNormalizationLaw J₁ R₁ J₂ R₂ Jq Rp Je Rc Rf o r e N
        K.obj (α.app K).hom) : NatTrans.CommShift α ℤ := by
  unfold TowerNormalizationLaw at hNorm
  let τ := compactTowerWord J₁ R₁ J₂ R₂ Jq Rp Je Rc Rf γ o r e
  have hτ : NatTrans.CommShift τ ℤ :=
    compactTowerWordCommShift J₁ R₁ J₂ R₂ Jq Rp Je Rc Rf γ o r e
  apply restrictedCommShift P Q S (J₁ ⋙ R₁) (J₂ ⋙ R₂) (Je ⋙ Rf) hF hG hH τ α
  intro K
  obtain ⟨m, hm, hα⟩ := hNorm K
  rw [hΓ _ m hm] at hα
  exact hα

attribute [-instance] modulePushforwardDerivedCommShift in
private theorem openFactorCommShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (j : X ⟶ Y) (i : Y ⟶ Z) (h : X ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion h] (e : j ≫ i = h) :
    NatTrans.CommShift (openFactor Λ j i h e).hom ℤ := by
  rw [openFactor_eq]
  have hj := jComp_shiftTriangle Λ j i
  have he := jCongr_shift Λ e
  infer_instance

attribute [-instance] modulePushforwardDerivedCommShift in
private theorem directCompositorCommShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.CommShift (rightDerivedLowerStarComp Λ f g).hom ℤ := by
  rw [normalizedDirectCompositor_eq]
  exact rComp_shiftTriangle Λ f g

attribute [-instance] modulePushforwardDerivedCommShift in
-- Assemble the native models while the coefficient object remains an abstract parameter.
private theorem nativeRestrictionCommShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] {X Z Y : Scheme.{u}} {h : X ⟶ Z} {g : Z ⟶ Y}
    (T : Compactification.Triangle h g) [QuasiCompact (T.cf.g ≫ T.cg.i)]
    [QuasiCompact T.cf.i] [QuasiCompact T.cg.i] (B : Pasting Λ)
    (P : ObjectProperty (CondensedOpenProper.D Λ X))
    (Q : ObjectProperty (CondensedOpenProper.D Λ Z))
    (S : ObjectProperty (CondensedOpenProper.D Λ Y))
    [P.IsStableUnderShift ℤ] [Q.IsStableUnderShift ℤ] [S.IsStableUnderShift ℤ]
    (hF : ∀ K : P.FullSubcategory,
      Q ((rightDerivedLowerShriekOfCompactification Λ T.cf).obj K.obj))
    (hG : ∀ K : Q.FullSubcategory,
      S ((rightDerivedLowerShriekOfCompactification Λ T.cg).obj K.obj))
    (hH : ∀ K : P.FullSubcategory,
      S ((rightDerivedLowerShriekOfCompactification Λ T.cfg).obj K.obj))
    (α : Q.lift (P.ι ⋙ rightDerivedLowerShriekOfCompactification Λ T.cf) hF ⋙
      S.lift (Q.ι ⋙ rightDerivedLowerShriekOfCompactification Λ T.cg) hG ⟶
      S.lift (P.ι ⋙ rightDerivedLowerShriekOfCompactification Λ T.cfg) hH)
    (hNorm : ∀ K : P.FullSubcategory,
      TowerNormalizationLaw
        ((openImmersionLowerShriek Λ T.cf.i).mapDerivedCategory)
        ((lowerStar Λ T.cf.g).rightDerivedFunctor)
        ((openImmersionLowerShriek Λ T.cg.i).mapDerivedCategory)
        ((lowerStar Λ T.cg.g).rightDerivedFunctor)
        ((openImmersionLowerShriek Λ T.q).mapDerivedCategory)
        ((lowerStar Λ T.p).rightDerivedFunctor)
        ((openImmersionLowerShriek Λ T.cfg.i).mapDerivedCategory)
        ((lowerStar Λ (T.p ≫ T.cg.g)).rightDerivedFunctor)
        ((lowerStar Λ T.cfg.g).rightDerivedFunctor)
        (openFactor Λ T.cf.i T.q T.cfg.i T.i_q).hom
        (rightDerivedLowerStarComp Λ T.p T.cg.g).hom
        (Functor.rightDerivedFunctorNatIso
          (eqToIso (congrArg (fun t ↦ lowerStar Λ t) T.p_g))).hom
        (fun M m ↦ compositionInterchangeIsNormalized Λ T.cf.g T.cg.i
          (detSfBoundaryCompactification (middle T)) M m)
        K.obj (α.app K).hom) :
    NatTrans.CommShift α ℤ := by
  have hq : QuasiCompact T.q := by
    have : QuasiCompact (T.q ≫ T.p) := by
      rw [← T.isPullback.w]
      infer_instance
    exact QuasiCompact.of_comp T.q T.p
  let J₁ := (openImmersionLowerShriek Λ T.cf.i).mapDerivedCategory
  let R₁ := (lowerStar Λ T.cf.g).rightDerivedFunctor
  let J₂ := (openImmersionLowerShriek Λ T.cg.i).mapDerivedCategory
  let R₂ := (lowerStar Λ T.cg.g).rightDerivedFunctor
  let Jq := (openImmersionLowerShriek Λ T.q).mapDerivedCategory
  let Rp := (lowerStar Λ T.p).rightDerivedFunctor
  let Je :=
    (openImmersionLowerShriek Λ T.cfg.i).mapDerivedCategory
  let γ := gamma Λ B.units T.isPullback.flip.toCommSq
  let o := openFactor Λ T.cf.i T.q T.cfg.i T.i_q
  let r := rightDerivedLowerStarComp Λ T.p T.cg.g
  let e := Functor.rightDerivedFunctorNatIso
    (eqToIso (congrArg (fun t ↦ lowerStar Λ t) T.p_g))
  have hγ : NatTrans.CommShift γ ℤ :=
    gamma_shiftTriangle Λ B.units _
  have ho : NatTrans.CommShift o.hom ℤ :=
    openFactorCommShift Λ T.cf.i T.q T.cfg.i T.i_q
  have hr : NatTrans.CommShift r.hom ℤ :=
    directCompositorCommShift Λ T.p T.cg.g
  have he : NatTrans.CommShift e.hom ℤ := by
    exact directCongr_shift Λ T.p_g
  exact normalizedRestrictionCommShift P Q S
    J₁ R₁ J₂ R₂ Jq Rp Je
    ((lowerStar Λ (T.p ≫ T.cg.g)).rightDerivedFunctor)
    ((lowerStar Λ T.cfg.g).rightDerivedFunctor) γ o.hom r.hom e.hom
    hF hG hH
    α
    (fun M m ↦ compositionInterchangeIsNormalized Λ
      T.cf.g T.cg.i
      (detSfBoundaryCompactification (middle T)) M m)
    (fun M m hm ↦ normalized_eq_gamma Λ B T.cf.g T.cg.i
      (detSfBoundaryCompactification (middle T)) T.isPullback.flip M m hm) hNorm

attribute [-instance] modulePushforwardDerivedCommShift in
-- Specialize the coefficient-parametrized calculation to the supplied system.
private theorem qcqsCompositionCoreShiftAlphaTower_proof (ℓ : ℕ) [Fact ℓ.Prime]
    {X Z Y : Scheme.{u}} {h : X ⟶ Z} {g : Z ⟶ Y}
    [(bc ℓ X).IsTriangulated] [(bc ℓ Z).IsTriangulated] [(bc ℓ Y).IsTriangulated]
    (A : Comparisons ℓ h g) :
    ∀ (T : Compactification.Triangle h g)
      [QuasiCompact (T.cf.g ≫ T.cg.i)] [QuasiCompact T.cf.i]
      [QuasiCompact T.cg.i],
      NatTrans.CommShift (A.alpha T.cf T.cg T.cfg).hom ℤ := by
  intro T _ _ _
  have hΛ : IsAdmissibleCoefficient (Profinite.padicAlgClRingObj.{u} ℓ) :=
    ⟨ℓ, inferInstance, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))))⟩
  obtain ⟨B⟩ := condensedOpenProperPasting (Profinite.padicAlgClRingObj.{u} ℓ) hΛ
  exact nativeRestrictionCommShift (Profinite.padicAlgClRingObj.{u} ℓ) T B
    (bc ℓ X) (bc ℓ Z) (bc ℓ Y)
    (A.sh.preserves T.cf)
    (A.sg.preserves T.cg)
    (A.sgh.preserves T.cfg)
    (A.alpha T.cf T.cg T.cfg).hom
    (A.tower_normalized T)

-- Preserve the original hypotheses while applying the stronger private result.
set_option linter.unusedVariables false in
attribute [-instance] modulePushforwardDerivedCommShift in
attribute [-instance] nativeModulePushforwardShift in
/-- Shift compatibility of the normalized compositor on one compatible compactification
  tower. Expand `A.alpha` using `A.tower_normalized`: the normalized middle
  interchange is the proper/open `gamma` word, followed by the open compositor,
  proper compositor, and equality transport. The qcqs proper/open calculus supplies
  `CommShift` for every factor, and `NatTrans.CommShift.comp` and whiskering close
  the equation. The compactification triangle supplies the quasi-compactness
  instances needed by each factor. The finite-field and separated finite-type
  hypotheses are retained so compatible towers are available. Source: Stacks Tags
  0F7J and 05SU.
  (blueprint: new-m5-qcqs-composition-core-shift-alpha-tower). -/
theorem qcqsCompositionCoreShiftAlphaTower (ℓ : ℕ) [Fact ℓ.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hℓ : ℓ ≠ D.p)
    {X₀ Z₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [QuasiSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [QuasiSeparated Z₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [QuasiSeparated Y₀.hom]
    (h₀ : X₀ ⟶ Z₀) (g₀ : Z₀ ⟶ Y₀)
    [IsSeparated h₀.left] [LocallyOfFiniteType h₀.left] [QuasiCompact h₀.left]
    [IsSeparated g₀.left] [LocallyOfFiniteType g₀.left] [QuasiCompact g₀.left]
    [(bc ℓ (((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap D.k₀ D.k)))).obj X₀).left)).IsTriangulated]
    [(bc ℓ (((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap D.k₀ D.k)))).obj Z₀).left)).IsTriangulated]
    [(bc ℓ (((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap D.k₀ D.k)))).obj Y₀).left)).IsTriangulated]
    (A : Comparisons ℓ (modelMap D h₀) (modelMap D g₀)) :
    ∀ (T : Compactification.Triangle (modelMap D h₀) (modelMap D g₀))
      [QuasiCompact (T.cf.g ≫ T.cg.i)] [QuasiCompact T.cf.i]
      [QuasiCompact T.cg.i],
      NatTrans.CommShift (A.alpha T.cf T.cg T.cfg).hom ℤ := by
  exact qcqsCompositionCoreShiftAlphaTower_proof ℓ A
end AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
