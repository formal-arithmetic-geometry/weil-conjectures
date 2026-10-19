/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteLift
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import all Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Closed inverse image preserves limits

Source: blueprint, pro-etale coefficients, `sk-prop-sf-open-closed-triangle`,
`det-sf-open-closed-pullback-limits` (blueprint: det-sf-open-closed-pullback-limits).

A sheaf of rings is a monoid object in abelian sheaves, and its module sheaves are
`CategoryTheory.Mod`. This includes noncommutative rings. The canonical inverse image
is the existing `Functor.mapMod` applied to the monoidal sheaf inverse image.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.Scheme.AffineProEt

/-- The henselian lift viewed over the original scheme through an affine open chart.
Source: blueprint `det-sf-open-closed-pullback-limits`, clause (1), using the lift of
`def-exc-closed-site-lift` (blueprint: det-sf-open-closed-pullback-limits). -/
def closedSiteLiftOver {X : Scheme.{u}} (A : Type u) [CommRing A] (I : Ideal A)
    (a : Spec (.of A) ⟶ X) [IsOpenImmersion a]
    (V : (Spec (.of (A ⧸ I))).AffineProEt) : X.ProEt :=
  ProEt.mk (((toProEt (Spec (.of A))).obj ((closedSiteLift A I).obj V)).hom ≫ a)

end AlgebraicGeometry.Scheme.AffineProEt

namespace AlgebraicGeometry.Scheme


private theorem projectiveEvaluation_openChart {S Z : Scheme.{u}}
    (z : S ⟶ Z) [IsOpenImmersion z] (V : S.AffineProEt)
    (hV : (ProEt.topology Z).IsWeaklyContractible.{u + 1}
      ((AffineProEt.toProEt S ⋙
        MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale z)).obj V)) :
    ∀ (P Q : Sheaf (AffineProEt.topology S) (Type (u + 1))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op V)) := by
  let G := AffineProEt.toProEt S ⋙
    MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale z)
  have : (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale z)).Full :=
    inferInstance
  have : (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale z)).Faithful :=
    inferInstance
  have : G.Full := by dsimp only [G]; infer_instance
  have : G.Faithful := by dsimp only [G]; infer_instance
  intro P Q φ hφ y
  have hlocal : Sheaf.IsLocallySurjective φ := (Sheaf.isLocallySurjective_iff_epi φ).mpr hφ
  obtain ⟨W, q, hq, x, hx⟩ := (AffineProEt.isLocallySurjective_iff φ).mp hlocal V y
  have hcover : Sieve.generate (Presieve.singleton (G.map q)) ∈
      ProEt.topology Z (G.obj V) := by
    have h := AffineProEt.generate_singleton_mem_topology q hq
    have h' := ((AffineProEt.toProEt S).functorPushforward_mem_iff
      (AffineProEt.topology S) (ProEt.topology S)).mpr h
    have h'' := (ProEt.coverPreserving_overMap
      (inferInstance : WeaklyEtale z)).cover_preserve h'
    simpa only [G, Functor.comp_obj, Functor.comp_map, ← Sieve.functorPushforward_comp,
      ← Sieve.generate_map_eq_functorPushforward,
      Presieve.map_singleton] using h''
  let J := ProEt.topology Z
  let H := J.uliftYoneda.{u + 1}
  have hepi : Epi (H.map (G.map q)) := by
    constructor
    intro T a b hab
    apply J.uliftYonedaEquiv.injective
    have hsep := ((isSheaf_iff_isSheaf_of_type J T.obj).mp T.property).isSheafFor
      (Presieve.singleton (G.map q)) hcover |>.isSeparatedFor
    apply hsep.ext
    rintro Y f ⟨⟩
    rw [J.uliftYonedaEquiv_naturality, J.uliftYonedaEquiv_naturality]
    exact congrArg J.uliftYonedaEquiv hab
  obtain ⟨t, ht⟩ := hV (H.map (G.map q))
    ((Sheaf.isLocallySurjective_iff_epi _).mpr hepi) (ULift.up (𝟙 _))
  let σ : V ⟶ W := G.preimage t.down
  have hσ : σ ≫ q = 𝟙 _ := by
    apply G.map_injective
    dsimp only [σ]
    rw [G.map_comp, G.map_preimage, G.map_id]
    exact congrArg ULift.down ht
  refine ⟨P.obj.map σ.op x, ?_⟩
  rw [φ.hom.naturality_apply, hx, ← Q.obj.map_comp_apply, ← op_comp, hσ]
  exact Q.obj.map_id_apply _ y

private theorem weaklyContractible_of_iso {Z : Scheme.{u}} {V W : Z.ProEt}
    (e : V ≅ W) (hW : (ProEt.topology Z).IsWeaklyContractible.{u + 1} W) :
    (ProEt.topology Z).IsWeaklyContractible.{u + 1} V := by
  intro P Q φ hφ y
  obtain ⟨x, hx⟩ := hW φ hφ (Q.obj.map e.inv.op y)
  refine ⟨P.obj.map e.hom.op x, ?_⟩
  rw [φ.hom.naturality_apply, hx, ← Q.obj.map_comp_apply, ← op_comp]
  simp

namespace AffineProEt

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_precomposition_toSheafify {S T : Scheme.{u}}
    (v : S.AffineProEt ⥤ T.AffineProEt) {r : T.AffineProEt ⥤ S.AffineProEt}
    (adj : v ⊣ r) [(topology S).Subcanonical]
    (hcov : ∀ (V : S.AffineProEt) (R : Presieve V), R ∈ precoverage V →
      R.map v ∈ precoverage (v.obj V))
    (H : Sheaf (topology T) AddCommGrpCat.{u + 1}) (V : S.AffineProEt)
    (hV : ∀ (P Q : Sheaf (topology S) (Type (u + 1))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op V))) :
    IsIso ((toSheafify (topology S) (v.op ⋙ H.obj)).app (op V)) := by
  let H₀ := (sheafCompose (topology T) (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj H
  have hbij : Function.Bijective
      ((toSheafify (topology S) (v.op ⋙ H₀.obj)).app (op V)) := by
    exact ⟨precomposition_unit_injective v hcov H₀ V,
      precomposition_unit_surjective v adj H₀ V hV⟩
  let e := sheafifyComposeIso (topology S)
    (CategoryTheory.forget AddCommGrpCat.{u + 1}) (v.op ⋙ H.obj)
  have hfac := congrArg (fun φ ↦ φ.app (op V))
    (sheafComposeIso_hom_fac (topology S)
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) (v.op ⋙ H.obj))
  have : IsIso ((toSheafify (topology S) (v.op ⋙ H₀.obj)).app (op V)) :=
    (isIso_iff_bijective _).mpr hbij
  apply (ConcreteCategory.isIso_iff_bijective _).2
  change Function.Bijective (ConcreteCategory.hom
    ((Functor.whiskerRight (toSheafify (topology S) (v.op ⋙ H.obj))
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).app (op V)))
  have he := congrArg ConcreteCategory.hom hfac
  have hc : Function.Bijective (ConcreteCategory.hom
      (e.hom.app (op V))) := (isIso_iff_bijective _).mp inferInstance
  rw [← he]
  exact hc.comp hbij

set_option backward.isDefEq.respectTransparency false in
private theorem affineUnit_from_projectiveFiber
    (A : Type u) [CommRing A] (I : Ideal A)
    (B : (Spec (.of A)).AffineProEt)
    (adj : closedSiteLift A I ⊣ closedSiteBaseChange A I)
    (hε : IsIso (adj.counit.app B))
    (hR : ∀ (P Q : Sheaf (topology (Spec (.of (A ⧸ I)))) (Type (u + 1)))
      (φ : P ⟶ Q), Epi φ → Function.Surjective
        (φ.hom.app (op ((closedSiteBaseChange A I).obj B))))
    (F : Sheaf (ProEt.topology (Spec (.of A))) AddCommGrpCat.{u + 1}) :
    IsIso (((proEtaleSheafAdjunction
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
        AddCommGrpCat.{u + 1}).unit.app F).hom.app (op ((toProEt (Spec (.of A))).obj B))) := by
  let X := Spec (.of A)
  let Z := Spec (.of (A ⧸ I))
  let i : Z ⟶ X := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let v := closedSiteLift A I
  let r := closedSiteBaseChange A I
  obtain ⟨_, _, _, _, hco, _, hcov, _⟩ := affine_closed_site_functor_properties A I
  have : v.IsCocontinuous (topology Z) (topology X) := hco
  have : r.IsContinuous (topology X) (topology Z) :=
    adj.isContinuous_of_isCocontinuous _ _
  have : (topology Z).Subcanonical :=
    GrothendieckTopology.subcanonical_of_full_of_faithful (toProEt Z)
      (topology Z) (ProEt.topology Z)
  let D := AddCommGrpCat.{u + 1}
  let RX := (toProEt X).sheafPushforwardContinuous D (topology X) (ProEt.topology X)
  let RZ := (toProEt Z).sheafPushforwardContinuous D (topology Z) (ProEt.topology Z)
  let L := sheafToPresheaf (topology X) D ⋙
    (Functor.whiskeringLeft _ _ D).obj v.op ⋙ presheafToSheaf (topology Z) D
  let R := r.sheafPushforwardContinuous D (topology X) (topology Z)
  let a : L ⊣ R :=
    ((adj.op.whiskerLeft D).comp (sheafificationAdjunction (topology Z) D)).restrictFullyFaithful
      (Functor.FullyFaithful.ofFullyFaithful (sheafToPresheaf (topology X) D))
      (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)
  have t : r ⋙ toProEt Z ≅ toProEt X ⋙ proEtaleBaseChange i := Iso.refl _
  have : (toProEt X ⋙ proEtaleBaseChange i).IsContinuous
      (topology X) (ProEt.topology Z) :=
    Functor.isContinuous_comp _ _ (topology X) (ProEt.topology X) (ProEt.topology Z)
  have : (r ⋙ toProEt Z).IsContinuous (topology X) (ProEt.topology Z) :=
    Functor.isContinuous_comp _ _ (topology X) (topology Z) (ProEt.topology Z)
  let beta : proEtaleSheafDirectImage i D ⋙ RX ≅ RZ ⋙ R :=
    Functor.sheafPushforwardContinuousComp (toProEt X) (proEtaleBaseChange i)
      D (topology X) (ProEt.topology X) (ProEt.topology Z) ≪≫
    Functor.sheafPushforwardContinuousIso t.symm D (topology X) (ProEt.topology Z) ≪≫
    (Functor.sheafPushforwardContinuousComp r (toProEt Z) D
      (topology X) (topology Z) (ProEt.topology Z)).symm
  let alpha := ((mateEquiv (proEtaleSheafAdjunction i D) a).symm beta.hom).natTrans
  have : IsIso alpha := isIso_inverseMate_of_equivalences (proEtaleSheafAdjunction i D) a beta
  have hp := hR
  have hη : IsIso ((a.unit.app (RX.obj F)).hom.app (op B)) := by
    have heq : (a.unit.app (RX.obj F)).hom.app (op B) =
        (RX.obj F).obj.map (adj.counit.app B).op ≫
          (toSheafify (topology Z) (v.op ⋙ (RX.obj F).obj)).app (op (r.obj B)) := by
      dsimp [a]
      rw [← sheafToPresheaf_map, Adjunction.map_restrictFullyFaithful_unit_app]
      simp only [Adjunction.comp_unit_app, sheafificationAdjunction_unit_app,
        Functor.comp_map, Iso.refl_hom, NatTrans.id_app]
      rfl
    rw [heq]
    have : IsIso (adj.counit.app B) := hε
    have := isIso_precomposition_toSheafify v adj hcov (RX.obj F) (r.obj B) hp
    infer_instance
  have hu := unit_mateEquiv_symm (proEtaleSheafAdjunction i D) a beta.hom F
  have hu' := congrArg (fun f ↦ f.hom.app (op B)) hu
  change ((proEtaleSheafAdjunction i D).unit.app F).hom.app (op ((toProEt X).obj B)) ≫
    (beta.hom.app _).hom.app (op B) =
      (a.unit.app (RX.obj F)).hom.app (op B) ≫
        (R.map (alpha.app F)).hom.app (op B) at hu'
  have : IsIso (((proEtaleSheafAdjunction i D).unit.app F).hom.app
      (op ((toProEt X).obj B)) ≫ (beta.hom.app _).hom.app (op B)) := by
    rw [hu']
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((beta.hom.app _).hom.app (op B))

end AffineProEt

section Localization
universe u'
open AlgebraicGeometry MorphismProperty AlgebraicGeometry.ProEtale CategoryTheory.Category
variable (A : Type u') [Category.{u + 1} A]

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}

variable [WeaklyEtale j] [WeaklyEtale j']

private instance localPullbackMapContinuous :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g' ⋙
    MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ j')).IsContinuous
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology Z') :=
  have := Scheme.ProEt.isContinuous_overPullback g'
  have := Scheme.ProEt.isContinuous_overMap (inferInstance : @WeaklyEtale _ _ j')
  Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology U') _

private instance localMapPullbackContinuous :
    (MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ j) ⋙
    MorphismProperty.Over.pullback @WeaklyEtale ⊤ g'').IsContinuous
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology Z') :=
  have := Scheme.ProEt.isContinuous_overPullback g''
  have := Scheme.ProEt.isContinuous_overMap (inferInstance : @WeaklyEtale _ _ j)
  Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology Z) _

/-- The base change map `g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` on pro-étale sheaves, with the pullbacks
along the weakly étale morphisms `j` and `j'` computed as restrictions along the localization
functors: the map induced by `CategoryTheory.MorphismProperty.Over.pullbackMapComparison`. -/
private noncomputable def localRestrictionBaseChangeMap (sq : CommSq g' j' j g'') :
    (g'')_*[A] ⋙ ProEtale.localizationRestriction A j inferInstance ⟶
      ProEtale.localizationRestriction A j' inferInstance ⋙ (g')_*[A] :=
  Functor.sheafPushforwardContinuousNatTrans
    (MorphismProperty.Over.pullbackMapComparison (inferInstance : @WeaklyEtale _ _ j)
      (inferInstance : @WeaklyEtale _ _ j') sq) A
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology Z')

/-- If the square is cartesian, the base change map on restrictions is an isomorphism, being
induced by an isomorphism of site functors. -/
private lemma isIso_localRestrictionBaseChangeMap_of_isPullback
    (hsq : IsPullback g' j' j g'') :
    IsIso (localRestrictionBaseChangeMap A hsq.toCommSq) :=
  have := MorphismProperty.Over.isIso_pullbackMapComparison_of_isPullback
    (inferInstance : @WeaklyEtale _ _ j) (inferInstance : @WeaklyEtale _ _ j') hsq
  inferInstanceAs (IsIso (Functor.sheafPushforwardContinuousNatTrans
    (MorphismProperty.Over.pullbackMapComparison (inferInstance : @WeaklyEtale _ _ j)
      (inferInstance : @WeaklyEtale _ _ j') hsq.toCommSq) A
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology Z')))

private noncomputable def siteMate (sq : CommSq g' j' j g'') :=
  (mateEquiv
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j (inferInstance : WeaklyEtale j) trivial)
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j'
      (inferInstance : WeaklyEtale j') trivial)
    (TwoSquare.mk _ _ _ _ (MorphismProperty.Over.pullbackMapComparison
      (inferInstance : WeaklyEtale j) (inferInstance : WeaklyEtale j') sq))).natTrans
private theorem siteMate_eq (sq : CommSq g' j' j g'') :
    siteMate sq = (MorphismProperty.Over.pullbackComp g' j).inv ≫
      (MorphismProperty.Over.pullbackCongr (P := @WeaklyEtale) (Q := ⊤) sq.w).hom ≫
      (MorphismProperty.Over.pullbackComp j' g'').hom := by
  ext b
  dsimp [siteMate, mateEquiv]
  set_option backward.defeqAttrib.useBackward true in
  apply pullback.hom_ext
  · apply pullback.hom_ext <;>
      simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
        MorphismProperty.Over.mk]
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk]


private lemma isIso_mate_localRestrictionBaseChangeMap (sq : CommSq g' j' j g'') :
    IsIso ((mateEquiv
      (ProEtale.localizationRestrictionLowerStarAdjunction A j' inferInstance)
      (ProEtale.localizationRestrictionLowerStarAdjunction A j inferInstance)
      (TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq))).natTrans) := by
  have hs : IsIso (siteMate sq) := by rw [siteMate_eq]; infer_instance
  have h (F : Sheaf (ProEt.topology U') A) (b : Z.ProEt) :
      ((mateEquiv
        (ProEtale.localizationRestrictionLowerStarAdjunction A j' inferInstance)
        (ProEtale.localizationRestrictionLowerStarAdjunction A j inferInstance)
        (TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq))).natTrans.app F).hom.app
          (op b) = F.obj.map ((siteMate sq).app b).op := by
    simp only [Functor.comp_obj, mateEquiv, ProEtale.localizationRestrictionLowerStarAdjunction,
      Adjunction.sheafPushforwardContinuous, Functor.id_obj,
      localRestrictionBaseChangeMap, Functor.sheafPushforwardContinuousNatTrans,
      ObjectProperty.ι_obj, Equiv.coe_fn_mk, NatTrans.comp_app, Functor.rightUnitor_inv_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Functor.comp_map, Functor.leftUnitor_hom_app, comp_id, id_comp,
      ObjectProperty.FullSubcategory.comp_hom, Adjunction.whiskerLeft_unit_app_app,
      Functor.op_obj, Adjunction.op_unit, NatTrans.op_app,
      Adjunction.whiskerLeft_counit_app_app, Adjunction.op_counit,
      ProEtale.lowerStar_map_hom_app]
    change F.obj.map _ ≫ F.obj.map _ ≫ F.obj.map _ = _
    simp only [← Functor.map_comp]
    dsimp [siteMate, mateEquiv]
    simp only [id_comp, comp_id, ← Functor.map_comp, ← op_comp]
    simp only [Functor.map_comp, op_comp, Category.assoc]
  have hF (F : Sheaf (ProEt.topology U') A) : IsIso ((mateEquiv
      (ProEtale.localizationRestrictionLowerStarAdjunction A j' inferInstance)
      (ProEtale.localizationRestrictionLowerStarAdjunction A j inferInstance)
      (TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq))).natTrans.app F) := by
    have hB : ∀ b : Z.ProEtᵒᵖ, IsIso (((mateEquiv
        (ProEtale.localizationRestrictionLowerStarAdjunction A j' inferInstance)
        (ProEtale.localizationRestrictionLowerStarAdjunction A j inferInstance)
        (TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq))).natTrans.app F).hom.app b) :=
      fun b ↦ by rw [h F b.unop]; infer_instance
    apply (isIso_iff_of_reflects_iso _ (sheafToPresheaf _ A)).mp
    change IsIso (((mateEquiv
      (ProEtale.localizationRestrictionLowerStarAdjunction A j' inferInstance)
      (ProEtale.localizationRestrictionLowerStarAdjunction A j inferInstance)
      (TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq))).natTrans.app F).hom)
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

variable [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_inverseMate_localRestrictionBaseChange (sq : CommSq g' j' j g'') :
    IsIso (((mateEquiv (proEtaleSheafAdjunction g'' A)
      (proEtaleSheafAdjunction g' A)).symm
        (TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq))).natTrans) := by
  let ai := proEtaleSheafAdjunction g'' A
  let ak := proEtaleSheafAdjunction g' A
  let aj := localizationRestrictionLowerStarAdjunction A j inferInstance
  let ab := localizationRestrictionLowerStarAdjunction A j' inferInstance
  let beta := TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq)
  let alpha := (mateEquiv ai ak).symm beta
  have hm : mateEquiv ai ak alpha = beta := (mateEquiv ai ak).apply_symm_apply beta
  have h := iterated_mateEquiv_conjugateEquiv ai ak aj ab alpha
  rw [hm] at h
  have hc : IsIso (conjugateEquiv (ai.comp ab) (aj.comp ak) alpha.natTrans) := by
    rw [← h]
    exact isIso_mate_localRestrictionBaseChangeMap A sq
  have := hc
  let e := (conjugateIsoEquiv (ai.comp ab) (aj.comp ak)).symm
    (asIso (conjugateEquiv (ai.comp ab) (aj.comp ak) alpha.natTrans))
  have he : e.hom = alpha.natTrans :=
    (conjugateEquiv (ai.comp ab) (aj.comp ak)).symm_apply_apply alpha.natTrans
  change IsIso alpha.natTrans
  rw [← he]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_unit_sections_of_localization
    (hsq : IsPullback g' j' j g'') (W : U.ProEt)
    (F : Sheaf (ProEt.topology Z) A)
    (hη : IsIso (((proEtaleSheafAdjunction g' A).unit.app
      ((localizationRestriction A j inferInstance).obj F)).hom.app (op W))) :
    IsIso (((proEtaleSheafAdjunction g'' A).unit.app F).hom.app
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj W))) := by
  let ai := proEtaleSheafAdjunction g'' A
  let ak := proEtaleSheafAdjunction g' A
  let G := localizationRestriction A j inferInstance
  let R := proEtaleSheafDirectImage g' A
  let beta := TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A hsq.toCommSq)
  let alpha := (mateEquiv ai ak).symm beta
  have : IsIso alpha.natTrans := isIso_inverseMate_localRestrictionBaseChange A hsq.toCommSq
  have : IsIso beta.natTrans := isIso_localRestrictionBaseChangeMap_of_isPullback A hsq
  have hu := unit_mateEquiv_symm ai ak beta F
  have hu' := congrArg (fun f ↦ f.hom.app (op W)) hu
  change ((ai.unit.app F).hom.app
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj W))) ≫
      (beta.app _).hom.app (op W) =
    (ak.unit.app (G.obj F)).hom.app (op W) ≫
      (R.map (alpha.app F)).hom.app (op W) at hu'
  have : IsIso ((ak.unit.app (G.obj F)).hom.app (op W)) := hη
  have : IsIso (((ai.unit.app F).hom.app
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj W))) ≫
      (beta.app _).hom.app (op W)) := by
    rw [hu']
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((beta.app _).hom.app (op W))

end Localization

/-- The canonical closed inverse-image unit is invertible on a henselian lift
whose closed fibre is weakly contractible. The assertion concerns all abelian
sheaves, independently of a ring or module structure.

Source: Stacks Project, Tag 09BL, lemma-closed-immersion-affines-apply (1),(2),
and Tag 09AA, lemma-closed-immersion, affine localization in its proof.
(blueprint: det-sf-open-closed-pullback-limits)

Proof:
Restrict first to the affine chart. Restriction from the full pro-etale site to
its affine ind-etale basis is an equivalence. The closed-site lift is fully
faithful and left adjoint to closed base change. Mate the commuting direct-image
square across the two restriction equivalences. The unit equation for mates
identifies the ordinary inverse-image unit with the composite of the map induced
by the lift adjunction counit and the sheafification unit for the presheaf F
composed with the lift. The counit at a lifted object is invertible by full
faithfulness and the triangle identity. The affine closed evaluation theorem
makes the latter sheafification map bijective at a weakly contractible object.
Its weak contractibility hypothesis can be transported across the affine-basis
restriction equivalence, since that equivalence preserves epimorphisms.

For a general affine open chart, the cartesian square gives the canonical
pullback-map comparison of the site functors. This comparison is invertible.
The topology on objects over the open chart is the slice topology, so weak
contractibility of the given global closed fibre implies weak contractibility
of its corresponding local object. The localization direct-image comparison
is invertible, and its double mate gives the inverse-image comparison. The
unit equation for these mates identifies the restricted global unit with the
local unit up to those invertible comparisons. Thus the affine calculation
proves the assertion on the original scheme.

Finally forget an abelian sheaf to sets. The forgetful functor preserves the
filtered left Kan extensions and sheafification used in inverse image. The
canonical forgetful comparison respects the adjunction units. Its component
therefore identifies the underlying map in the assertion with the set unit,
up to an isomorphism. Forgetting abelian groups reflects isomorphisms. This
also covers the empty chart and empty closed fibre, where sheaves have their
terminal value. -/
private theorem closed_inverseImage_unit_isIso_on_lift
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (A : Type u) [CommRing A] (I : Ideal A)
    (a : Spec (.of A) ⟶ X) [IsOpenImmersion a]
    (z : Spec (.of (A ⧸ I)) ⟶ Z)
    (hchart : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) z a i)
    (V : (Spec (.of (A ⧸ I))).AffineProEt)
    (hV : (ProEt.topology Z).IsWeaklyContractible.{u + 1}
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).obj
        (ProEt.mk (((AffineProEt.toProEt (Spec (.of A))).obj
          ((AffineProEt.closedSiteLift A I).obj V)).hom ≫ a))))
    (F : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) :
    IsIso (((proEtaleSheafAdjunction i AddCommGrpCat.{u + 1}).unit.app F).hom.app
      (op (ProEt.mk (((AffineProEt.toProEt (Spec (.of A))).obj
        ((AffineProEt.closedSiteLift A I).obj V)).hom ≫ a)))) := by
  have : IsOpenImmersion z := MorphismProperty.of_isPullback hchart inferInstance
  let i₀ := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let B := (AffineProEt.closedSiteLift A I).obj V
  let W := (AffineProEt.toProEt (Spec (.of A))).obj B
  let G := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale z)
  let c := MorphismProperty.Over.pullbackMapComparison
    (inferInstance : WeaklyEtale a) (inferInstance : WeaklyEtale z) hchart.toCommSq
  have : IsIso c := MorphismProperty.Over.isIso_pullbackMapComparison_of_isPullback
    (inferInstance : WeaklyEtale a) (inferInstance : WeaklyEtale z) hchart
  have hlocal : (ProEt.topology Z).IsWeaklyContractible.{u + 1}
      (G.obj ((proEtaleBaseChange i₀).obj W)) :=
    weaklyContractible_of_iso (asIso (c.app W)) hV
  have hR := projectiveEvaluation_openChart z
    ((AffineProEt.closedSiteBaseChange A I).obj B) hlocal
  obtain ⟨_, _, hfull, hfaith, _, ⟨adj⟩, _, _⟩ :=
    AffineProEt.affine_closed_site_functor_properties A I
  have : (AffineProEt.closedSiteLift A I).Full := hfull
  have : (AffineProEt.closedSiteLift A I).Faithful := hfaith
  have hε : IsIso (adj.counit.app B) := by
    have h := adj.left_triangle_components V
    have : IsIso ((AffineProEt.closedSiteLift A I).map (adj.unit.app V)) := inferInstance
    have : IsIso ((AffineProEt.closedSiteLift A I).map (adj.unit.app V) ≫
        adj.counit.app B) := by
      rw [h]
      exact ⟨𝟙 _, by simp, by simp⟩
    exact IsIso.of_isIso_comp_left
      ((AffineProEt.closedSiteLift A I).map (adj.unit.app V)) (adj.counit.app B)
  have hη := AffineProEt.affineUnit_from_projectiveFiber A I B adj hε hR
    ((AlgebraicGeometry.ProEtale.localizationRestriction AddCommGrpCat.{u + 1}
      a inferInstance).obj F)
  exact isIso_unit_sections_of_localization AddCommGrpCat.{u + 1} hchart W F hη


/-- Closed inverse image is evaluation on henselian lifts at weakly contractible
closed-site basis objects, and is exact and preserves small limits and colimits.
The affine chart is specified by the cartesian square `(A/I, Z, A, X)`. The object
`i⁻¹(v(V))` is canonically `V`, by the closed-fibre property of the henselian lift.
Thus the displayed component of the inverse-image adjunction unit is precisely the
canonical map `F(v(V)) → (i^*F)(V)`, after that canonical identification. No arbitrary
isomorphism or comparison arrow is selected. The two finite-preservation assertions
express exactness in the abelian categories of module objects.

Source: blueprint `det-sf-open-closed-pullback-limits`, clauses (1) and (2);
Bhatt--Scholze, Proposition 4.2.8 (blueprint: det-sf-open-closed-pullback-limits).

Proof:
1. Transfer projective evaluation to the closed affine chart. Any local epimorphism
   lifts after one affine surjective cover. Its image in the global closed site is
   covering. Subcanonical Yoneda and weak contractibility split that cover; full
   faithfulness of the open-chart inclusion returns its section to the affine basis.
2. On the affine basis, inverse image is sheafified precomposition with the lift.
   Its adjunction unit is restriction along the lift counit followed by the
   sheafification unit. Full faithfulness makes that counit invertible on a lifted
   object. Closed affine evaluation makes the second map bijective. Sheafification
   commutes with forgetting abelian groups, which reflects isomorphisms.
3. The cartesian chart gives an invertible comparison of base-change site functors.
   The rotated mate is a composite of pullback-composition isomorphisms. The iterated
   mate identity therefore makes the inverse-image comparison invertible. Its unit
   equation transfers the affine calculation to the specified global unit component.
4. Use the abelian-sheaf clause of
   `proEtale_immersion_inverseImage_preservesLimits` for the closed immersion.
   Limits of module objects are created by `Mod.forget`; its conservativity reflects
   limit cones. The underlying functor of `mapMod` is inverse image of underlying
   abelian sheaves, so reflection gives all small module limits.
5. The existing monoidal `Adjunction.mapModAdjunction` lifts inverse/direct image
   to module objects over an arbitrary ring object. Its left adjoint preserves all
   small colimits. Specializing the two preservation results to finite diagrams
   gives the two finite-preservation assertions. Empty diagrams and empty charts
   are included throughout.
-/
theorem closed_inverseImage_preserves_limits
    {X Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (_hU : IsCompact ((Set.range i)ᶜ))
    (B : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) [MonObj B] :
    (∀ (A : Type u) [CommRing A] (I : Ideal A)
      (a : Spec (.of A) ⟶ X) [IsOpenImmersion a]
      (z : Spec (.of (A ⧸ I)) ⟶ Z)
      (_hchart : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) z a i)
      (V : (Spec (.of (A ⧸ I))).AffineProEt),
      (ProEt.topology Z).IsWeaklyContractible.{u + 1}
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).obj
            (AffineProEt.closedSiteLiftOver A I a V)) →
      ∀ F : Mod (Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) B,
        IsIso (((proEtaleSheafAdjunction i AddCommGrpCat.{u + 1}).unit.app
          F.X).hom.app (op (AffineProEt.closedSiteLiftOver A I a V)))) ∧
    PreservesFiniteLimits ((ProEtale.upperStar AddCommGrpCat.{u + 1} i).mapMod B) ∧
    PreservesFiniteColimits ((ProEtale.upperStar AddCommGrpCat.{u + 1} i).mapMod B) ∧
    PreservesLimitsOfSize.{u + 1, u + 1}
      ((ProEtale.upperStar AddCommGrpCat.{u + 1} i).mapMod B) ∧
    PreservesColimitsOfSize.{u + 1, u + 1}
      ((ProEtale.upperStar AddCommGrpCat.{u + 1} i).mapMod B) := by
  have hAb : PreservesLimitsOfSize.{u + 1, u + 1}
      (ProEtale.upperStar AddCommGrpCat.{u + 1} i) :=
    (proEtale_immersion_inverseImage_preservesLimits i).2.1
  have hMod : PreservesLimitsOfSize.{u + 1, u + 1}
      ((ProEtale.upperStar AddCommGrpCat.{u + 1} i).mapMod B) := by
    let L := ProEtale.upperStar AddCommGrpCat.{u + 1} i
    have : PreservesLimitsOfSize.{u + 1, u + 1}
        (L.mapMod B ⋙ Mod.forget (L.obj B)) :=
      inferInstanceAs (PreservesLimitsOfSize.{u + 1, u + 1} (Mod.forget B ⋙ L))
    have : HasLimitsOfSize.{u + 1, u + 1}
        (Mod (Sheaf (ProEt.topology Z) AddCommGrpCat.{u + 1}) (L.obj B)) :=
      ⟨fun J _ ↦ inferInstance⟩
    have : ReflectsLimitsOfSize.{u + 1, u + 1}
        (Mod.forget (L.obj B) :
          Mod (Sheaf (ProEt.topology Z) AddCommGrpCat.{u + 1}) (L.obj B) ⥤ _) :=
      reflectsLimits_of_reflectsIsomorphisms
    exact preservesLimits_of_reflects_of_preserves (L.mapMod B) (Mod.forget (L.obj B))
  have hColim : PreservesColimitsOfSize.{u + 1, u + 1}
      ((ProEtale.upperStar AddCommGrpCat.{u + 1} i).mapMod B) :=
    (Adjunction.leftAdjoint_preservesColimits
      ((ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).mapModAdjunction B))
  refine ⟨?_, inferInstance, inferInstance, hMod, hColim⟩
  intro A _ I a _ z hchart V hV F
  exact closed_inverseImage_unit_isIso_on_lift i A I a z hchart V hV F.X

end AlgebraicGeometry.Scheme
