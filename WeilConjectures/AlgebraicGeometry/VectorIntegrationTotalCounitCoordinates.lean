/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationDirectSumCounitMaps
import all WeilConjectures.AlgebraicGeometry.VectorIntegrationOverlapCoordinates
import all WeilConjectures.AlgebraicGeometry.VectorTraceGeometry

/-! # Coordinates of the flattened simultaneous bundle chart

This comparison is entirely a statement about morphisms of schemes.
(blueprint: lem-pur-vector-integration-total-counit-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

open Opposite VectorBundleZeroSection
attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom

private theorem block_base_coordinate (T : Scheme.{u}) (s r : ℕ) (i : Fin s) :
    (VectorIntegrationDirectSumCounit.towerBlockIso T s r).hom.appTop
        (affineTraceCoordinate T (s + r) (i.castAdd r)) =
      (affineTraceProjection (affineTraceTower T s) r).appTop (affineTraceCoordinate T s i) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change (AffineSpace.map PUnit.{u + 1}
      (VectorIntegrationDirectSumCounit.towerBlockIso T s r).hom).appTop
        (affineTraceCoordinate T (s + (r + 1)) (i.castAdd (r + 1))) = _
    rw [← Fin.castSucc_castAdd]
    simp only [affineTraceCoordinate, Fin.lastCases_castSucc]
    change (AffineSpace.map PUnit.{u + 1}
      (VectorIntegrationDirectSumCounit.towerBlockIso T s r).hom).appTop
        ((AffineSpace PUnit.{u + 1} (affineTraceTower T (s + r)) ↘ _).appTop
          (affineTraceCoordinate T (s + r) (i.castAdd r))) =
      (AffineSpace PUnit.{u + 1} (affineTraceTower (affineTraceTower T s) r) ↘ _).appTop
        ((affineTraceProjection (affineTraceTower T s) r).appTop
          (affineTraceCoordinate T s i))
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, AffineSpace.map_over,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ih]

private theorem block_fibre_coordinate (T : Scheme.{u}) (s r : ℕ) (i : Fin r) :
    (VectorIntegrationDirectSumCounit.towerBlockIso T s r).hom.appTop
        (affineTraceCoordinate T (s + r) (i.natAdd s)) =
      affineTraceCoordinate (affineTraceTower T s) r i := by
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [Fin.natAdd_last]
      change (AffineSpace.map PUnit.{u + 1}
        (VectorIntegrationDirectSumCounit.towerBlockIso T s r).hom).appTop
          (affineTraceCoordinate T ((s + r) + 1) (Fin.last (s + r))) =
        affineTraceCoordinate (affineTraceTower T s) (r + 1) (Fin.last r)
      simp only [affineTraceCoordinate, Fin.lastCases_last]
      exact AffineSpace.map_appTop_coord _ _
    · rw [Fin.natAdd_castSucc]
      simp only [affineTraceCoordinate, Fin.lastCases_castSucc]
      change (AffineSpace.map PUnit.{u + 1}
        (VectorIntegrationDirectSumCounit.towerBlockIso T s r).hom).appTop
          ((AffineSpace PUnit.{u + 1} (affineTraceTower T (s + r)) ↘ _).appTop
            (affineTraceCoordinate T (s + r) (j.natAdd s))) =
        (AffineSpace PUnit.{u + 1} (affineTraceTower (affineTraceTower T s) r) ↘ _).appTop
          (affineTraceCoordinate (affineTraceTower T s) r j)
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, AffineSpace.map_over,
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ih]

section Frames
variable (S : Scheme.{u}) (r s : ℕ) (F G : S.Modules)
  (V U : S.Opens) (eF : Trivialization S r F V) (eG : Trivialization S s G U)
  (W : S.Opens) (hWV : W ≤ V) (hWU : W ≤ U)

private theorem sum_frame_inl (i : Fin r) :
    SheafOfModules.ιFree (ULift.up (i.castAdd s)) ≫
        (VectorIntegrationDirectSumCounit.sumFrame S r s F G V U eF eG W hWV hWU).inv =
      SheafOfModules.ιFree (ULift.up i) ≫
        (VectorIntegrationDirectSumCounit.restrictedFrame hWV eF).inv ≫
        (Scheme.Modules.restrictFunctor W.ι).map (biprod.inl : F ⟶ F ⊞ G) := by
  classical
  let : PreservesBinaryBiproducts (Scheme.Modules.restrictFunctor W.ι) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have hi : (Scheme.Modules.restrictFunctor W.ι).map (biprod.inl : F ⟶ F ⊞ G) ≫
      ((Scheme.Modules.restrictFunctor W.ι).mapBiprod F G).hom = biprod.inl := by
    apply (cancel_mono ((Scheme.Modules.restrictFunctor W.ι).mapBiprod F G).inv).mp
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, Functor.mapBiprod_inv]
    simp only [biprod.inl_desc]
  apply (cancel_mono
    (VectorIntegrationDirectSumCounit.sumFrame S r s F G V U eF eG W hWV hWU).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp only [VectorIntegrationDirectSumCounit.sumFrame, Iso.trans_hom, Functor.mapIso_hom]
  rw [reassoc_of% hi]
  simp only [biprod.mapIso_hom, biprod.inl_map_assoc, Iso.inv_hom_id_assoc,
    biprod_isoCoprod_hom, biprod.inl_desc_assoc]
  erw [SheafOfModules.inl_freeSumIso_hom_assoc]
  simp only [SheafOfModules.freeFunctor_map]
  erw [SheafOfModules.ιFree_freeMap_assoc, SheafOfModules.ιFree_freeMap]
  rfl

private theorem sum_frame_inr (i : Fin s) :
    SheafOfModules.ιFree (ULift.up (i.natAdd r)) ≫
        (VectorIntegrationDirectSumCounit.sumFrame S r s F G V U eF eG W hWV hWU).inv =
      SheafOfModules.ιFree (ULift.up i) ≫
        (VectorIntegrationDirectSumCounit.restrictedFrame hWU eG).inv ≫
        (Scheme.Modules.restrictFunctor W.ι).map (biprod.inr : G ⟶ F ⊞ G) := by
  classical
  let : PreservesBinaryBiproducts (Scheme.Modules.restrictFunctor W.ι) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have hi : (Scheme.Modules.restrictFunctor W.ι).map (biprod.inr : G ⟶ F ⊞ G) ≫
      ((Scheme.Modules.restrictFunctor W.ι).mapBiprod F G).hom = biprod.inr := by
    apply (cancel_mono ((Scheme.Modules.restrictFunctor W.ι).mapBiprod F G).inv).mp
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, Functor.mapBiprod_inv]
    simp only [biprod.inr_desc]
  apply (cancel_mono
    (VectorIntegrationDirectSumCounit.sumFrame S r s F G V U eF eG W hWV hWU).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp only [VectorIntegrationDirectSumCounit.sumFrame, Iso.trans_hom, Functor.mapIso_hom]
  rw [reassoc_of% hi]
  simp only [biprod.mapIso_hom, biprod.inr_map_assoc, Iso.inv_hom_id_assoc,
    biprod_isoCoprod_hom, biprod.inr_desc_assoc]
  erw [SheafOfModules.inr_freeSumIso_hom_assoc]
  simp only [SheafOfModules.freeFunctor_map]
  erw [SheafOfModules.ιFree_freeMap_assoc, SheafOfModules.ιFree_freeMap]
  rfl

end Frames

private theorem frame_section_map {S : Scheme.{u}} {r t : ℕ} {F H : S.Modules}
    (W : S.Opens) (eF : Trivialization S r F W) (eH : Trivialization S t H W)
    (m : F ⟶ H) (i : Fin r) (j : Fin t)
    (h : SheafOfModules.ιFree (ULift.up j) ≫ eH.inv =
      SheafOfModules.ιFree (ULift.up i) ≫ eF.inv ≫
        (Scheme.Modules.restrictFunctor W.ι).map m) :
    frameSection S t H W eH j = m.val.app (op W) (frameSection S r F W eF i) := by
  have he := congrArg (fun (k : SheafOfModules.unit W.toScheme.ringCatSheaf ⟶
      H.restrict W.ι) ↦ Scheme.Modules.Hom.app (X := W.toScheme) k ⊤
        (1 : Γ(W.toScheme, ⊤))) h
  unfold frameSection
  change H.presheaf.map (eqToHom W.ι_image_top.symm).op
    (Scheme.Modules.Hom.app (X := W.toScheme)
      (SheafOfModules.ιFree (ULift.up j) ≫ eH.inv) ⊤ (1 : Γ(W.toScheme, ⊤))) = _
  rw [he]
  exact (PresheafOfModules.naturality_apply m.val
    (eqToHom W.ι_image_top.symm).op _).symm

private theorem coordinate_pullback {S X : Scheme.{u}} [IsNoetherian S]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (W : S.Opens) (e : Trivialization S d F W)
    (k : X ⟶ ((π S d F) ⁻¹ᵁ W).toScheme) (i : Fin d) :
    k.appTop (coordinate S d F W e i) =
      (k ≫ ((π S d F) ⁻¹ᵁ W).ι).appLE ((π S d F) ⁻¹ᵁ W) ⊤ (by simp)
        (VectorTraceGeometry.generator S d F W (frameSection S d F W e i)) := by
  have hi : ((π S d F) ⁻¹ᵁ W).ι.appLE ((π S d F) ⁻¹ᵁ W) ⊤ (by simp) =
      ((π S d F) ⁻¹ᵁ W).topIso.inv := by
    rw [Scheme.Opens.ι_appLE]
    rfl
  rw [← Scheme.Hom.appLE_comp_appLE k ((π S d F) ⁻¹ᵁ W).ι
    ((π S d F) ⁻¹ᵁ W) ⊤ ⊤ (by simp) (by simp), hi]
  erw [Scheme.Hom.appLE_eq_app]
  rfl

private theorem generator_coordinate {S X : Scheme.{u}} [IsNoetherian S]
    (r t : ℕ) (F H : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [H.IsFiniteLocallyFreeOfRank t]
    (m : F ⟶ H) (W : S.Opens)
    (eF : Trivialization S r F W) (eH : Trivialization S t H W)
    (i : Fin r) (j : Fin t)
    (he : frameSection S t H W eH j = m.val.app (op W) (frameSection S r F W eF i))
    (kF : X ⟶ ((π S r F) ⁻¹ᵁ W).toScheme)
    (kH : X ⟶ ((π S t H) ⁻¹ᵁ W).toScheme)
    (hk : kF ≫ ((π S r F) ⁻¹ᵁ W).ι = kH ≫ ((π S t H) ⁻¹ᵁ W).ι ≫
      WeilConjectures.PurityFiniteSetting.purityBundleMap S t r H F m) :
    kH.appTop (coordinate S t H W eH j) = kF.appTop (coordinate S r F W eF i) := by
  rw [coordinate_pullback, coordinate_pullback, he]
  have hg := VectorTraceGeometry.purityBundleMap_generators S t r H F m W
    (frameSection S r F W eF i)
  rw [← hg, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  exact congrArg (fun (z : Γ(scheme S r F, (π S r F) ⁻¹ᵁ W) ⟶ Γ(X, ⊤)) ↦
    z (VectorTraceGeometry.generator S r F W
    (frameSection S r F W eF i)))
    (Scheme.Hom.appLE_congr_hom hk.symm _ _ _ _)

private theorem inverse_frame_coordinate {S X : Scheme.{u}} [IsNoetherian S]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (W : S.Opens) (e : Trivialization S d F W)
    [IsIso (trivializationMap S d F W e)]
    (k : X ⟶ affineTraceTower W.toScheme d) (i : Fin d) :
    (k ≫ (affineTraceAffineSpaceIso W.toScheme d).hom ≫
      inv (trivializationMap S d F W e)).appTop (coordinate S d F W e i) =
      k.appTop (affineTraceCoordinate W.toScheme d i) := by
  let := (trivializationMap_spec S d F W e).1
  have hc : (trivializationMap S d F W e).appTop
      (AffineSpace.coord W.toScheme (ULift.up i)) = coordinate S d F W e i :=
    AffineSpace.homOfVector_appTop_coord _ _ _
  rw [← hc, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  rw [tower_iso_coord]

private theorem restriction_unit_compare {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctorIsoPullback f).hom.app (Scheme.Modules.unit Y) ≫
        (Scheme.Modules.pullbackObjUnitIso f).hom =
      (Scheme.Modules.restrictUnitIso f).hom := by
  apply ((Scheme.Modules.restrictAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Scheme.Modules.restrictFunctorIsoPullback,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, ← Adjunction.homEquiv_unit]
  change (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
    (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) = _
  erw [SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change f.app U x = (f.appIso (f ⁻¹ᵁ U)).hom
    (Y.presheaf.map (homOfLE (f.image_preimage_le U)).op x)
  rw [← CommRingCat.comp_apply, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_eq_app]

private theorem restriction_free_compare {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (I : Type u)
    [PreservesColimitsOfShape (Discrete I) (Scheme.Modules.restrictFunctor f)] :
    Scheme.Modules.restrictFreeIso f I =
      (SheafOfModules.mapFreeIso (Scheme.Modules.restrictFunctor f) I
        (Scheme.Modules.restrictUnitIso f).symm).symm := by
  apply Iso.ext
  apply (cancel_epi (SheafOfModules.mapFreeIso (Scheme.Modules.restrictFunctor f) I
    (Scheme.Modules.restrictUnitIso f).symm).hom).mp
  rw [Iso.symm_hom, Iso.hom_inv_id]
  apply Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan I)
  intro i
  erw [SheafOfModules.ιFree_mapFreeIso_hom_assoc]
  dsimp only [Scheme.Modules.restrictFreeIso, Iso.trans_hom]
  change (Scheme.Modules.restrictUnitIso f).inv ≫
      (Scheme.Modules.restrictFunctor f).map (SheafOfModules.ιFree i) ≫
        (Scheme.Modules.restrictFunctorIsoPullback f).hom.app _ ≫
          (Scheme.Modules.pullbackFreeIso f I).hom = _
  rw [(Scheme.Modules.restrictFunctorIsoPullback f).hom.naturality_assoc,
    Scheme.Modules.pullback_map_ιFree_pullbackFreeIso_hom,
    reassoc_of% restriction_unit_compare f]
  erw [Iso.inv_hom_id_assoc, SheafOfModules.freeCofan_inj, Category.comp_id]

private theorem restricted_chart (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    {W V : S.Opens} (h : W ≤ V) (e : Trivialization S d F V) :
    vectorIntegrationRestrictedChart S d F W V h e =
      vectorIntegrationChart S d F W
        (VectorIntegrationDirectSumCounit.restrictedFrame h e) := by
  let := restrict_coproduct (S.homOfLE h) d
  rw [VectorIntegrationDirectSumCounit.restrictedFrame, restriction_free_compare]
  exact restrict_chart S d F h e

private theorem permutation_coordinates (T : Scheme.{u}) (d : ℕ)
    (σ : Equiv.Perm (Fin d)) :
    ∃ g : Matrix.GeneralLinearGroup (Fin d) Γ(T, ⊤), ∀ i,
      (affineTraceLinearMap T d g).appTop (affineTraceCoordinate T d i) =
        affineTraceCoordinate T d (σ i) := by
  classical
  let g : Matrix.GeneralLinearGroup (Fin d) Γ(T, ⊤) :=
    { val := fun i j ↦ if σ i = j then 1 else 0
      inv := fun i j ↦ if σ.symm i = j then 1 else 0
      val_inv := by
        ext i j
        simp only [Matrix.mul_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_eq_single (σ i)]
        · simp
        · intro k _ hk
          simp [Ne.symm hk]
        · simp
      inv_val := by
        ext i j
        simp only [Matrix.mul_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_eq_single (σ.symm i)]
        · simp
        · intro k _ hk
          simp [Ne.symm hk]
        · simp }
  refine ⟨g, fun i ↦ ?_⟩
  simp [affineTraceLinearMap_coordinate, g, eq_comm]

private theorem transport_coordinate (T : Scheme.{u}) {d e : ℕ} (h : d = e) (i : Fin e) :
    (eqToHom (congrArg (affineTraceTower T) h)).appTop (affineTraceCoordinate T e i) =
      affineTraceCoordinate T d (Fin.cast h.symm i) := by
  cases h
  rfl

private theorem transport_projection (T : Scheme.{u}) {d e : ℕ} (h : d = e) :
    eqToHom (congrArg (affineTraceTower T) h) ≫ affineTraceProjection T e =
      affineTraceProjection T d := by
  cases h
  exact Category.id_comp _

/-- The flattened double chart and the sum frame differ by an invertible linear map.
Source: vector-bundle purity, paragraph 2, simultaneous trivializations.
(blueprint: lem-pur-vector-integration-total-counit-coordinates).

Proof: restrict both supplied frames to W. On the biproduct injections the frame
`sumFrame` is the direct sum of these restrictions, by the defining equations of
`mapBiprod`, `biprod.mapIso`, and `freeSumIso`. The two projections of `sumIso`
are its defining product projections. Use `chart_first` and `chart_second` to
compute the generators of the double chart in these two frames. Flattening the
iterated tower puts the s base coordinates before the r fibre coordinates, whereas
the sum frame puts F before G. The resulting finite permutation gives an invertible
matrix g over Γ(W,⊤), with inverse the reverse permutation. The coordinate maps
therefore agree on the structural projection and every degree-one generator.
The relative symmetric-algebra universal property proves the displayed equality.
The same proof includes empty coordinate blocks and the empty base. -/
theorem vectorIntegration_totalCounit_coordinates
    (S : Scheme.{u}) [IsNoetherian S] (r s : ℕ)
    (F G : S.Modules) [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s]
    (V U : S.Opens) (eF : VectorBundleZeroSection.Trivialization S r F V)
    (eG : VectorBundleZeroSection.Trivialization S s G U)
    (W : S.Opens) (hWV : W ≤ V) (hWU : W ≤ U) :
    ∃ g : Matrix.GeneralLinearGroup (Fin (s + r)) Γ(W.toScheme, ⊤),
      (VectorIntegrationDirectSumCounit.towerBlockIso W.toScheme s r).inv ≫
          VectorIntegrationDirectSumCounit.chart S r s F G V U eF eG W hWV hWU ≫
          (VectorTraceGeometry.sumIso S r s F G).hom =
        affineTraceLinearMap W.toScheme (s + r) g ≫
          eqToHom (congrArg (affineTraceTower W.toScheme) (Nat.add_comm s r)) ≫
          vectorIntegrationChart S (r + s) (VectorTraceGeometry.sum S F G) W
            (VectorIntegrationDirectSumCounit.sumFrame S r s F G V U eF eG W hWV hWU) := by
  classical
  let H := VectorTraceGeometry.sum S F G
  let e := VectorIntegrationDirectSumCounit.sumFrame S r s F G V U eF eG W hWV hWU
  let a := VectorIntegrationDirectSumCounit.restrictedFrame hWV eF
  let b := VectorIntegrationDirectSumCounit.restrictedFrame hWU eG
  let : IsIso (trivializationMap S r F W a) := (trivializationMap_spec S r F W a).1
  let : IsIso (trivializationMap S s G W b) := (trivializationMap_spec S s G W b).1
  let : IsIso (trivializationMap S (r + s) H W e) :=
    (trivializationMap_spec S (r + s) H W e).1
  let X := affineTraceTower (affineTraceTower W.toScheme s) r
  let q : X ⟶ W.toScheme :=
    affineTraceProjection (affineTraceTower W.toScheme s) r ≫ affineTraceProjection W.toScheme s
  let ℓ := VectorIntegrationDirectSumCounit.chart S r s F G V U eF eG W hWV hWU ≫
    (VectorTraceGeometry.sumIso S r s F G).hom
  have hsum := (VectorTraceGeometry.existsUnique_sumIso S r s F G).exists.choose_spec
  change (VectorTraceGeometry.sumIso S r s F G).hom ≫ VectorTraceGeometry.first S r s F G =
      VectorTraceGeometry.baseChange (π S s G) r F ∧
    (VectorTraceGeometry.sumIso S r s F G).hom ≫ VectorTraceGeometry.second S r s F G =
      π (scheme S s G) r ((Scheme.Modules.tensorPullback (π S s G)).obj F) at hsum
  have hF : ℓ ≫ VectorTraceGeometry.first S r s F G =
      affineTraceMap (affineTraceProjection W.toScheme s) r ≫
        vectorIntegrationChart S r F W a := by
    dsimp only [ℓ]
    rw [Category.assoc, hsum.1, VectorIntegrationDirectSumCounit.chart_first,
      restricted_chart]
  have hG : ℓ ≫ VectorTraceGeometry.second S r s F G =
      affineTraceProjection (affineTraceTower W.toScheme s) r ≫
        vectorIntegrationChart S s G W b := by
    dsimp only [ℓ]
    rw [Category.assoc, hsum.2, VectorIntegrationDirectSumCounit.chart_second,
      restricted_chart]
  have hp : ℓ ≫ π S (r + s) H = q ≫ W.ι := by
    dsimp only [ℓ, q, H]
    rw [Category.assoc, (VectorTraceGeometry.sumIso_isPullback S r s F G).w,
      Category.comp_id, ← Category.assoc, VectorIntegrationDirectSumCounit.chart_second,
      Category.assoc, (vectorIntegrationRestrictedChart_isPullback S s G W U hWU eG).w,
      Category.assoc]
  let sq := (isPullback_morphismRestrict (π S (r + s) H) W).flip
  let k := sq.lift ℓ q hp
  have hk : k ≫ ((π S (r + s) H) ⁻¹ᵁ W).ι = ℓ := sq.lift_fst _ _ _
  have hkp : k ≫ ((π S (r + s) H) ∣_ W) = q := sq.lift_snd _ _ _
  let kF : X ⟶ ((π S r F) ⁻¹ᵁ W).toScheme :=
    affineTraceMap (affineTraceProjection W.toScheme s) r ≫
      (affineTraceAffineSpaceIso W.toScheme r).hom ≫ inv (trivializationMap S r F W a)
  let kG : X ⟶ ((π S s G) ⁻¹ᵁ W).toScheme :=
    affineTraceProjection (affineTraceTower W.toScheme s) r ≫
      (affineTraceAffineSpaceIso W.toScheme s).hom ≫ inv (trivializationMap S s G W b)
  have hkF : kF ≫ ((π S r F) ⁻¹ᵁ W).ι =
      k ≫ ((π S (r + s) H) ⁻¹ᵁ W).ι ≫ VectorTraceGeometry.first S r s F G := by
    rw [← Category.assoc k, hk, hF]
    rfl
  have hkG : kG ≫ ((π S s G) ⁻¹ᵁ W).ι =
      k ≫ ((π S (r + s) H) ⁻¹ᵁ W).ι ≫ VectorTraceGeometry.second S r s F G := by
    rw [← Category.assoc k, hk, hG]
    rfl
  have hcF (i : Fin r) : k.appTop (coordinate S (r + s) H W e (i.castAdd s)) =
      affineTraceCoordinate (affineTraceTower W.toScheme s) r i := by
    have hf := frame_section_map W a e (biprod.inl : F ⟶ H) i (i.castAdd s)
      (sum_frame_inl S r s F G V U eF eG W hWV hWU i)
    rw [generator_coordinate r (r + s) F H biprod.inl W a e i (i.castAdd s) hf kF k hkF]
    exact (inverse_frame_coordinate r F W a
      (affineTraceMap (affineTraceProjection W.toScheme s) r) i).trans
        (tower_map_coord (affineTraceProjection W.toScheme s) r i)
  have hcG (i : Fin s) : k.appTop (coordinate S (r + s) H W e (i.natAdd r)) =
      (affineTraceProjection (affineTraceTower W.toScheme s) r).appTop
        (affineTraceCoordinate W.toScheme s i) := by
    have hf := frame_section_map W b e (biprod.inr : G ⟶ H) i (i.natAdd r)
      (sum_frame_inr S r s F G V U eF eG W hWV hWU i)
    rw [generator_coordinate s (r + s) G H biprod.inr W b e i (i.natAdd r) hf kG k hkG]
    exact inverse_frame_coordinate s G W b
      (affineTraceProjection (affineTraceTower W.toScheme s) r) i
  let σ : Equiv.Perm (Fin (s + r)) := (finCongr (Nat.add_comm s r)).trans
    (finSumFinEquiv.symm.trans ((Equiv.sumComm (Fin r) (Fin s)).trans finSumFinEquiv))
  obtain ⟨g, hg⟩ := permutation_coordinates W.toScheme (s + r) σ
  have hσF (i : Fin r) : σ (Fin.cast (Nat.add_comm s r).symm (i.castAdd s)) = i.natAdd s := by
    simp [σ]
  have hσG (i : Fin s) : σ (Fin.cast (Nat.add_comm s r).symm (i.natAdd r)) = i.castAdd r := by
    simp [σ]
  have he : k ≫ trivializationMap S (r + s) H W e =
      (VectorIntegrationDirectSumCounit.towerBlockIso W.toScheme s r).hom ≫
        affineTraceLinearMap W.toScheme (s + r) g ≫
          eqToHom (congrArg (affineTraceTower W.toScheme) (Nat.add_comm s r)) ≫
            (affineTraceAffineSpaceIso W.toScheme (r + s)).hom := by
    apply AffineSpace.hom_ext
    · simp only [Category.assoc, (trivializationMap_spec S (r + s) H W e).2.1,
        affineTraceAffineSpaceIso, asIso_hom, affineTraceToAffineSpace,
        AffineSpace.homOfVector_over]
      erw [transport_projection W.toScheme (Nat.add_comm s r), affineTraceLinearMap_over,
        VectorIntegrationDirectSumCounit.towerBlockIso_over]
      exact hkp
    · rintro ⟨j⟩
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, trivializationMap,
        AffineSpace.homOfVector_appTop_coord, tower_iso_coord]
      erw [transport_coordinate W.toScheme (Nat.add_comm s r)]
      rw [hg]
      refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
      · rw [hcF, hσF, block_fibre_coordinate]
      · rw [hcG, hσG, block_base_coordinate]
  have hℓ : ℓ = (VectorIntegrationDirectSumCounit.towerBlockIso W.toScheme s r).hom ≫
      affineTraceLinearMap W.toScheme (s + r) g ≫
        eqToHom (congrArg (affineTraceTower W.toScheme) (Nat.add_comm s r)) ≫
          vectorIntegrationChart S (r + s) H W e := by
    rw [← hk]
    unfold vectorIntegrationChart
    simp only [← Category.assoc]
    apply congrArg (fun z ↦ z ≫ ((π S (r + s) H) ⁻¹ᵁ W).ι)
    apply (cancel_mono (trivializationMap S (r + s) H W e)).mp
    simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using he
  refine ⟨g, ?_⟩
  change (VectorIntegrationDirectSumCounit.towerBlockIso W.toScheme s r).inv ≫ ℓ = _
  rw [hℓ]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rfl

end AlgebraicGeometry.Etale
