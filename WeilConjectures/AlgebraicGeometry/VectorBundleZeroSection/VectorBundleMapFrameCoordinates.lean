/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTraceGeometry.VectorTraceGeometry
import WeilConjectures.CategoryTheory.CommAlgebraSheafModule

/-! # Degree-one coordinates of a linear bundle map

Source: the symmetric-algebra generator calculation in the proof of vector-bundle purity.
(blueprint: lem-pur-vector-bundle-map-frame-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.VectorBundleZeroSection

/-- Pull a frame to an arbitrary scheme, using the canonical module pullback comparisons.
Source: blueprint vector-bundle purity, paragraph 2.
(blueprint: lem-pur-vector-bundle-map-frame-coordinates). -/
def pulledFrame (S : Scheme.{u}) (r : ℕ) (F : S.Modules)
    (V : S.Opens) (e : Trivialization S r F V)
    {W : Scheme.{u}} (g : W ⟶ V.toScheme) :
    (Scheme.Modules.pullback (g ≫ V.ι)).obj F ≅
      SheafOfModules.free (R := W.ringCatSheaf) (ULift.{u} (Fin r)) :=
  (Scheme.Modules.pullbackComp g V.ι).symm.app F ≪≫
    (Scheme.Modules.pullback g).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).symm.app F ≪≫ e) ≪≫
    Scheme.Modules.pullbackFreeIso g (ULift.{u} (Fin r))

/-- The map of free modules obtained by expressing a pulled-back linear map in two frames.
No invertibility of the linear map is required.
Source: blueprint vector-bundle purity, paragraph 2.
(blueprint: lem-pur-vector-bundle-map-frame-coordinates). -/
def framedPullbackMap {S T : Scheme.{u}} (f : T ⟶ S) (r s : ℕ)
    (F : S.Modules) (G : T.Modules) (m : (Scheme.Modules.pullback f).obj F ⟶ G)
    (V : S.Opens) (eS : Trivialization S r F V)
    (U : T.Opens) (eT : Trivialization T s G U)
    {W : Scheme.{u}} (a : W ⟶ U.toScheme) (g : W ⟶ V.toScheme)
    (h : (a ≫ U.ι) ≫ f = g ≫ V.ι) :
    SheafOfModules.free (R := W.ringCatSheaf) (ULift.{u} (Fin r)) ⟶
      SheafOfModules.free (R := W.ringCatSheaf) (ULift.{u} (Fin s)) :=
  (pulledFrame S r F V eS g).inv ≫
    (Scheme.Modules.pullbackCongr h.symm).hom.app F ≫
    (Scheme.Modules.pullbackComp (a ≫ U.ι) f).inv.app F ≫
    (Scheme.Modules.pullback (a ≫ U.ι)).map m ≫
    (pulledFrame T s G U eT a).hom

attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom

open Scheme.Modules
open SheafOfModules hiding freeπ sum_freeπ_ιFree

private theorem mate_homEquiv {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (t : L₂ ⟶ L₁) {M : C} {N : D} (b : L₁.obj M ⟶ N) :
    a₂.homEquiv _ _ (t.app M ≫ b) =
      a₁.homEquiv _ _ b ≫ (conjugateEquiv a₁ a₂ t).app N := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv a₁ a₂ t, Category.assoc, ← NatTrans.naturality]
  rw [← Category.assoc, ← Adjunction.homEquiv_unit]

private theorem adjoint_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (N : X.Modules)
    (b : (Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f).obj M ⟶ N) :
    (pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _
      ((pullbackComp f g).inv.app M ≫ b) =
    (pullbackPushforwardAdjunction g).homEquiv _ _
      ((pullbackPushforwardAdjunction f).homEquiv _ _ b) ≫
        (pushforwardComp f g).hom.app N := by
  rw [mate_homEquiv, conjugateEquiv_pullbackComp_inv, Adjunction.comp_homEquiv]
  rfl

private theorem pullback_eval_one {X Y : Scheme.{u}} (f : X ⟶ Y) (N : X.Modules)
    (b : (Scheme.Modules.pullback f).obj (Scheme.Modules.unit Y) ⟶ N) :
    Hom.app (X := X) b ⊤ (Hom.app (X := X) (pullbackObjUnitIso f).inv ⊤ (1 : Γ(X, ⊤))) =
      Hom.app (X := Y) ((pullbackPushforwardAdjunction f).homEquiv _ _ b) ⊤ (1 : Γ(Y, ⊤)) := by
  let c := (pullbackObjUnitIso f).inv ≫ b
  have hc : (pullbackObjUnitIso f).hom ≫ c = b := by simp [c]
  change Hom.app (X := X) c ⊤ (1 : Γ(X, ⊤)) = _
  rw [← hc, Adjunction.homEquiv_naturality_right]
  have hu : (pullbackPushforwardAdjunction f).homEquiv _ _
      (pullbackObjUnitIso f).hom = unitToPushforwardObjUnit f.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  rw [hu]
  change Hom.app (X := X) c ⊤ (1 : Γ(X, ⊤)) =
    Hom.app (X := X) c ⊤ (f.appTop (1 : Γ(Y, ⊤)))
  rw [map_one f.appTop.hom]

private theorem free_pairing {W : Scheme.{u}} (N : W.Modules) (r s : ℕ)
    (c : free (R := W.ringCatSheaf) (ULift.{u} (Fin r)) ⟶
      free (R := W.ringCatSheaf) (ULift.{u} (Fin s)))
    (b : free (R := W.ringCatSheaf) (ULift.{u} (Fin s)) ⟶ N) (j : Fin r) :
    Hom.app (X := W) (ιFree (ULift.up j) ≫ c ≫ b) ⊤ (1 : Γ(W, ⊤)) =
      ∑ i : Fin s, freeMatrix c (ULift.up i) (ULift.up j) •
        Hom.app (X := W) (ιFree (ULift.up i) ≫ b) ⊤ (1 : Γ(W, ⊤)) := by
  classical
  have hc : ιFree (ULift.up j) ≫ c ≫ b =
      ∑ i : ULift.{u} (Fin s),
        (ιFree (ULift.up j) ≫ c ≫ freeπ i) ≫ (ιFree i ≫ b) := by
    conv_lhs => rw [← Category.id_comp b, ← sum_freeπ_ιFree]
    simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
  rw [hc, Hom.sum_app_apply]
  refine Fintype.sum_equiv (Equiv.ulift : ULift.{u} (Fin s) ≃ Fin s) _ _ ?_
  rintro ⟨i⟩
  change Hom.app (X := W) (ιFree (ULift.up i) ≫ b) ⊤
    (freeMatrix c (ULift.up i) (ULift.up j)) = _
  rw [← Hom.app_smul]
  congr 1
  change _ = freeMatrix c (ULift.up i) (ULift.up j) * (1 : Γ(W, ⊤))
  exact (mul_one _).symm

private theorem frame_pairing {S W : Scheme.{u}} (r : ℕ) (F : S.Modules)
    (V : S.Opens) (e : Trivialization S r F V) (g : W ⟶ V.toScheme)
    (H : W.Modules) (B : F ⟶ (pushforward (g ≫ V.ι)).obj H) (j : Fin r) :
    Hom.app (X := W) (ιFree (ULift.up j) ≫ (pulledFrame S r F V e g).inv ≫
      ((pullbackPushforwardAdjunction (g ≫ V.ι)).homEquiv _ _).symm B) ⊤
        (1 : Γ(W, ⊤)) =
    H.presheaf.map (homOfLE (show (⊤ : W.Opens) ≤ (g ≫ V.ι) ⁻¹ᵁ V by
      simp)).op (B.val.app (op V) (frameSection S r F V e j)) := by
  let m := ((pullbackPushforwardAdjunction (g ≫ V.ι)).homEquiv _ _).symm B
  let b := B ≫ (pushforwardComp g V.ι).inv.app H
  let t := ((pullbackPushforwardAdjunction V.ι).homEquiv _ _).symm b
  let n := (Scheme.Modules.pullback g).map
      ((restrictFunctorIsoPullback V.ι).hom.app F) ≫ (pullbackComp g V.ι).hom.app F ≫ m
  have ht : (pullbackPushforwardAdjunction g).homEquiv _ _
      ((pullbackComp g V.ι).hom.app F ≫ m) = t := by
    apply ((pullbackPushforwardAdjunction V.ι).homEquiv _ _).injective
    apply (cancel_mono ((pushforwardComp g V.ι).hom.app H)).mp
    rw [← adjoint_comp]
    dsimp only [t, b]
    rw [Equiv.apply_symm_apply, Category.assoc, Iso.inv_hom_id_app,
      Category.comp_id, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    exact Equiv.apply_symm_apply _ _
  have hn : (pullbackPushforwardAdjunction g).homEquiv _ _ n =
      ((restrictAdjunction V.ι).homEquiv _ _).symm b := by
    dsimp only [n]
    rw [Adjunction.homEquiv_naturality_left, ht]
    apply ((restrictAdjunction V.ι).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right]
    have hu : (restrictAdjunction V.ι).homEquiv _ _
        ((restrictFunctorIsoPullback V.ι).hom.app F) =
        (pullbackPushforwardAdjunction V.ι).unit.app F := by
      unfold restrictFunctorIsoPullback
      exact Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ F
    rw [hu, ← Adjunction.homEquiv_unit]
    exact Equiv.apply_symm_apply _ _
  have hf : ιFree (ULift.up j) ≫ (pulledFrame S r F V e g).inv ≫ m =
      (pullbackObjUnitIso g).inv ≫
        (Scheme.Modules.pullback g).map (ιFree (ULift.up j) ≫ e.inv) ≫ n := by
    simp only [pulledFrame, Iso.trans_inv, Iso.app_inv, Iso.symm_inv,
      Functor.mapIso_inv, Functor.map_comp, Category.assoc, n]
    erw [reassoc_of% (ιFree_pullbackFreeIso_inv g (ULift.up j))]
  rw [show ((pullbackPushforwardAdjunction (g ≫ V.ι)).homEquiv _ _).symm B = m from rfl,
    hf]
  have hh := pullback_eval_one g H
    ((Scheme.Modules.pullback g).map (ιFree (ULift.up j) ≫ e.inv) ≫ n)
  rw [Adjunction.homEquiv_naturality_left, hn] at hh
  change Hom.app (X := W) ((pullbackObjUnitIso g).inv ≫
    (Scheme.Modules.pullback g).map (ιFree (ULift.up j) ≫ e.inv) ≫ n) ⊤
      (1 : Γ(W, ⊤)) = _ at hh
  erw [hh]
  let x := (e.inv.val.app (op ⊤)
    ((ιFree (R := V.toScheme.ringCatSheaf) (ULift.up j)).val.app (op ⊤)
      (1 : Γ(V.toScheme, ⊤))))
  change (((restrictAdjunction V.ι).homEquiv _ _).symm b).val.app (op ⊤) x = _
  rw [Adjunction.homEquiv_counit]
  change H.presheaf.map _ (B.val.app (op (V.ι ''ᵁ ⊤)) x) = _
  dsimp only [frameSection]
  erw [PresheafOfModules.naturality_apply B.val
    (eqToHom V.ι_image_top.symm).op]
  change H.presheaf.map _ _ = H.presheaf.map _ (H.presheaf.map _ _)
  rw [← ConcreteCategory.comp_apply, ← H.presheaf.map_comp]
  congr 2

private abbrev functionAlgebra {S X : Scheme.{u}} (f : X ⟶ S) : S.CommAlgebraSheaf :=
  Under.mk (⟨f.c⟩ : S.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf)

private def linearOfLift {S X : Scheme.{u}} [IsNoetherian S]
    (r : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank r] (ρ : X ⟶ S)
    (v : X ⟶ scheme S r F) (w : v ≫ π S r F = ρ) :
    F ⟶ (pushforward ρ).obj (Scheme.Modules.unit X) := by
  let β : functionAlgebra (π S r F) ⟶ functionAlgebra ρ :=
    Under.homMk ⟨{
      app := fun U ↦ v.appLE ((π S r F) ⁻¹ᵁ U.unop) (ρ ⁻¹ᵁ U.unop)
        (by rw [← w, Scheme.Hom.comp_preimage])
      naturality := by
        intros
        change (scheme S r F).presheaf.map _ ≫ _ = _ ≫ X.presheaf.map _
        simp only [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map] }⟩ (by
          apply Sheaf.hom_ext
          apply NatTrans.ext
          funext U
          change (π S r F).app U.unop ≫ v.appLE _ _ _ = _
          rw [← Scheme.Hom.comp_appLE,
            Scheme.Hom.appLE_congr_hom w _ _ _ le_rfl,
            Scheme.Hom.appLE_eq_app]
          rfl)
  exact SymmetricAlgebraSheaf.inclusion F ≫
    (commAlgebraSheafModuleFunctor S.sheaf).map (algebraIso S r F).hom ≫
    (commAlgebraSheafModuleFunctor S.sheaf).map β

private theorem frame_lift_pairing {S W X : Scheme.{u}} [IsNoetherian S]
    (r : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank r]
    (V : S.Opens) (e : Trivialization S r F V) (g : W ⟶ V.toScheme)
    (q : X ⟶ W) (ℓ : X ⟶ scheme S r F)
    (w : ℓ ≫ π S r F = q ≫ (g ≫ V.ι))
    (k : X ⟶ ((π S r F) ⁻¹ᵁ V).toScheme)
    (hk : k ≫ ((π S r F) ⁻¹ᵁ V).ι = ℓ) (j : Fin r) :
    Hom.app (X := W) (ιFree (ULift.up j) ≫ (pulledFrame S r F V e g).inv ≫
      ((pullbackPushforwardAdjunction (g ≫ V.ι)).homEquiv _ _).symm
        (linearOfLift r F (q ≫ (g ≫ V.ι)) ℓ w ≫
          (pushforwardComp q (g ≫ V.ι)).inv.app (Scheme.Modules.unit X))) ⊤
      (1 : Γ(W, ⊤)) = k.appTop (coordinate S r F V e j) := by
  rw [frame_pairing]
  change X.presheaf.map _ (ℓ.appLE ((π S r F) ⁻¹ᵁ V)
    ((q ≫ (g ≫ V.ι)) ⁻¹ᵁ V) _
      (VectorTraceGeometry.generator S r F V (frameSection S r F V e j))) = _
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  have eX : (⊤ : X.Opens) ≤ ℓ ⁻¹ᵁ ((π S r F) ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, w]
    simp
  have he : ℓ.appLE ((π S r F) ⁻¹ᵁ V) ⊤ eX =
      ((π S r F) ⁻¹ᵁ V).topIso.inv ≫ k.appTop := by
    have hι : ((π S r F) ⁻¹ᵁ V).ι.appLE ((π S r F) ⁻¹ᵁ V) ⊤
        (by simp) = ((π S r F) ⁻¹ᵁ V).topIso.inv := by
      rw [Scheme.Opens.ι_appLE]
      rfl
    rw [Scheme.Hom.appLE_congr_hom hk.symm _ _ _
      (by rw [Scheme.Hom.comp_preimage]; simp)]
    rw [← Scheme.Hom.appLE_comp_appLE k ((π S r F) ⁻¹ᵁ V).ι
      ((π S r F) ⁻¹ᵁ V) ⊤ ⊤ (by simp) (by simp), hι]
    erw [Scheme.Hom.appLE_eq_app]
  change ℓ.appLE ((π S r F) ⁻¹ᵁ V) ⊤ eX
    (VectorTraceGeometry.generator S r F V (frameSection S r F V e j)) = _
  rw [he]
  rfl

private theorem adjoint_congr {S W : Scheme.{u}} {p q : W ⟶ S} (h : p = q)
    (F : S.Modules) (H : W.Modules) (b : (Scheme.Modules.pullback p).obj F ⟶ H) :
    (pullbackPushforwardAdjunction q).homEquiv _ _
      ((pullbackCongr h.symm).hom.app F ≫ b) =
    (pullbackPushforwardAdjunction p).homEquiv _ _ b ≫ (pushforwardCongr h).hom.app H := by
  cases h
  have he : (pushforwardCongr (rfl : p = p)).hom.app H = 𝟙 _ := by
    apply Scheme.Modules.hom_ext
    intro U
    simp
  simp [pullbackCongr, he]

private theorem tower_map_coordinate {W V : Scheme.{u}} (g : W ⟶ V) (r : ℕ)
    (j : Fin r) :
    (affineTraceMap g r).appTop (affineTraceCoordinate V r j) =
      affineTraceCoordinate W r j := by
  induction r with
  | zero => exact Fin.elim0 j
  | succ r ih =>
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simpa only [affineTraceCoordinate, Fin.lastCases_last, affineTraceMap] using!
        (AffineSpace.map_appTop_coord (affineTraceMap g r) PUnit.unit)
    · simp only [affineTraceCoordinate, Fin.lastCases_castSucc]
      change (affineTraceMap g (r + 1)).appTop
        ((AffineSpace PUnit.{u + 1} (affineTraceTower V r) ↘
          affineTraceTower V r).appTop (affineTraceCoordinate V r i)) = _
      erw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
      change ((AffineSpace.map PUnit.{u + 1} (affineTraceMap g r)) ≫
        AffineSpace PUnit.{u + 1} (affineTraceTower V r) ↘ affineTraceTower V r).appTop _ = _
      rw [AffineSpace.map_over, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ih]

/-- A linear bundle map acts on each forward coordinate by the corresponding column
of the matrix of its module map in the pulled-back frames. This is a generator equation;
it asserts neither existence nor invertibility of a matrix, nor equality of inverse charts.
Source: blueprint sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md,
paragraph 2; Stacks Tags 01M2 and 01LX.
(blueprint: lem-pur-vector-bundle-map-frame-coordinates).

Proof: the inverse target chart sends the degree-one image of its i-th frame section to
its i-th polynomial variable. Pull both module frames to W. The pullback adjunction and
its composition comparison identify the image of a source basis section with its image
under framedPullbackMap. Expand that image in the target free basis; its coefficients
are freeMatrix. The generator equation in MapSpec sends this expansion to the identical
linear combination of degree-one functions. Restriction along the chart inclusion and
its topIso converts these functions to coordinate. Finally the affine tower comparison
sends its standard coordinates to affineTraceCoordinate. This argument uses only linearity
and the unit of the pullback adjunction, so applies to rectangular matrices, empty schemes,
and rank zero without any affine or nonemptiness hypothesis.
-/
theorem map_frame_coordinates
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (f : T ⟶ S) (r s : ℕ) (F : S.Modules) (G : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s]
    (m : (Scheme.Modules.pullback f).obj F ⟶ G)
    (v : VectorBundleZeroSection.scheme T s G ⟶ VectorBundleZeroSection.scheme S r F)
    (hv : VectorTraceGeometry.MapSpec f r s F G
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ m) v)
    (V : S.Opens) (eS : Trivialization S r F V)
    (U : T.Opens) (eT : Trivialization T s G U)
    (W : Scheme.{u}) (a : W ⟶ U.toScheme) (g : W ⟶ V.toScheme)
    (h : (a ≫ U.ι) ≫ f = g ≫ V.ι)
    (k : affineTraceTower W s ⟶ ((π S r F) ⁻¹ᵁ V).toScheme)
    (hk : k ≫ ((π S r F) ⁻¹ᵁ V).ι =
      (affineTraceMap a s ≫ Etale.vectorIntegrationChart T s G U eT) ≫ v)
    (j : Fin r) :
    (k ≫ trivializationMap S r F V eS).appTop (AffineSpace.coord V.toScheme (ULift.up j)) =
      ∑ i : Fin s, (affineTraceProjection W s).appTop
        (Scheme.Modules.freeMatrix (framedPullbackMap f r s F G m V eS U eT a g h)
          (ULift.up i) (ULift.up j)) * affineTraceCoordinate W s i := by
  classical
  let X := affineTraceTower W s
  let q := affineTraceProjection W s
  let p := a ≫ U.ι
  let t := g ≫ V.ι
  let ℓ := affineTraceMap a s ≫ Etale.vectorIntegrationChart T s G U eT
  have hℓ : ℓ ≫ π T s G = q ≫ p := by
    dsimp only [ℓ, q, p]
    rw [Category.assoc, (Etale.vectorIntegrationChart_isPullback T s G U eT).w,
      ← Category.assoc, (affineTraceMap_isPullback a s).w, Category.assoc]
  have w : (ℓ ≫ v) ≫ π S r F = q ≫ t := by
    rw [Category.assoc, hv.comm, ← Category.assoc, hℓ, Category.assoc, h]
  let H := (pushforward q).obj (Scheme.Modules.unit X)
  let B := linearOfLift s G (q ≫ p) ℓ hℓ ≫
    (pushforwardComp q p).inv.app (Scheme.Modules.unit X)
  let d := ((pullbackPushforwardAdjunction p).homEquiv _ _).symm B
  let D := (pullbackCongr h.symm).hom.app F ≫ (pullbackComp p f).inv.app F ≫
    (Scheme.Modules.pullback p).map m ≫ d
  let A := linearOfLift r F (q ≫ t) (ℓ ≫ v) w ≫
    (pushforwardComp q t).inv.app (Scheme.Modules.unit X)
  have hD : D = ((pullbackPushforwardAdjunction t).homEquiv _ _).symm A := by
    apply ((pullbackPushforwardAdjunction t).homEquiv _ _).injective
    dsimp only [D]
    rw [adjoint_congr h, adjoint_comp, Adjunction.homEquiv_naturality_left,
      show (pullbackPushforwardAdjunction p).homEquiv _ _ d = B from
        Equiv.apply_symm_apply _ _, Adjunction.homEquiv_naturality_right]
    rw [Equiv.apply_symm_apply]
    dsimp only [A, B, linearOfLift]
    apply Scheme.Modules.hom_ext
    intro Z
    ext x
    change X.presheaf.map _ (ℓ.appLE ((π T s G) ⁻¹ᵁ (f ⁻¹ᵁ Z))
      ((q ≫ p) ⁻¹ᵁ (f ⁻¹ᵁ Z)) _
        (VectorTraceGeometry.generator T s G (f ⁻¹ᵁ Z)
          (((pullbackPushforwardAdjunction f).homEquiv _ _ m).val.app (op Z) x))) =
      (ℓ ≫ v).appLE ((π S r F) ⁻¹ᵁ Z) ((q ≫ t) ⁻¹ᵁ Z) _
        (VectorTraceGeometry.generator S r F Z x)
    erw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    rw [← hv.generators Z x]
    erw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    rfl
  let b := (pulledFrame T s G U eT a).inv ≫ d
  have hs : Hom.app (X := W) (ιFree (ULift.up j) ≫
      framedPullbackMap f r s F G m V eS U eT a g h ≫ b) ⊤ (1 : Γ(W, ⊤)) =
      k.appTop (coordinate S r F V eS j) := by
    have hc : framedPullbackMap f r s F G m V eS U eT a g h ≫ b =
        (pulledFrame S r F V eS g).inv ≫ D := by
      dsimp only [framedPullbackMap, b, D]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rfl
    rw [hc, hD]
    exact frame_lift_pairing r F V eS g q (ℓ ≫ v) w k hk j
  have ht (i : Fin s) : Hom.app (X := W) (ιFree (ULift.up i) ≫ b) ⊤
      (1 : Γ(W, ⊤)) = affineTraceCoordinate W s i := by
    let := (trivializationMap_spec T s G U eT).1
    let kT := (affineTraceMap a s ≫ (affineTraceAffineSpaceIso U.toScheme s).hom) ≫
      inv (trivializationMap T s G U eT)
    have hkT : kT ≫ ((π T s G) ⁻¹ᵁ U).ι = ℓ := by
      simp only [kT, ℓ, Etale.vectorIntegrationChart, Category.assoc]
    have he := frame_lift_pairing s G U eT a q ℓ hℓ kT hkT i
    change Hom.app (X := W) (ιFree (ULift.up i) ≫ b) ⊤ _ = _ at he
    rw [he]
    have hc := congrArg (fun z ↦ z.appTop (AffineSpace.coord U.toScheme (ULift.up i)))
      (show kT ≫ trivializationMap T s G U eT =
        affineTraceMap a s ≫ (affineTraceAffineSpaceIso U.toScheme s).hom by
          simp [kT])
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, trivializationMap,
      affineTraceAffineSpaceIso, asIso_hom, affineTraceToAffineSpace,
      AffineSpace.homOfVector_appTop_coord, tower_map_coordinate] using hc
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, trivializationMap,
    AffineSpace.homOfVector_appTop_coord, ← hs,
    free_pairing H r s _ b j]
  apply Finset.sum_congr rfl
  intro i _
  rw [ht]
  rfl

end AlgebraicGeometry.VectorBundleZeroSection
