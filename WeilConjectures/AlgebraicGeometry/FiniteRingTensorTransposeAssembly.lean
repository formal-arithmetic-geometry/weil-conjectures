/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteRingSiteTensorTransposeData
import WeilConjectures.AlgebraicGeometry.FiniteRingAdjointTransport

/-! # Assembly of finite-ring projection and transpose transport

Source: finite-ring site transport, proof steps 4 and 9--11
(blueprint: lem-pur-finite-ring-tensor-transpose-assembly).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.ProEtale

/-- Projection compatibility and monoidal coherence imply both transpose formulas.
Source: proof steps 4 and 9--11 of the finite-ring site transport
(blueprint: lem-pur-finite-ring-tensor-transpose-assembly).

Proof: lift the two comparison functors to their essential images, obtaining equivalences.
Transport the adjunction by the counit-normalized mate. The projection square expresses
the second projection as a composite of isomorphisms, so it is invertible. Apply the
transpose transport identity to the first integration map and invert the projection
square. Tensor naturality and the unit identity identify its adjunct with the second
integration map. Finally precompose with the braiding and use braided coherence. -/
theorem finiteRingTensorTransposeAssembly
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
    {C' : Type u₃} [Category.{v₃} C'] [MonoidalCategory C'] [BraidedCategory C']
    {D' : Type u₄} [Category.{v₄} D'] [MonoidalCategory D']
    (E : C ⥤ C') (H : D ⥤ D') [E.Full] [E.Faithful] [H.Full] [H.Faithful]
    (F : C ⥤ D) (F' : C' ⥤ D') (P : D ⥤ C) (P' : D' ⥤ C')
    (PX : ObjectProperty C') (PY : ObjectProperty D')
    (hX : ∀ M, PX (E.obj M)) (hY : ∀ K, PY (H.obj K))
    (hx : ∀ N, E.essImage N ↔ PX N) (hy : ∀ N, H.essImage N ↔ PY N)
    (b : F ⋙ H ≅ E ⋙ F')
    (tx : ∀ M N, E.obj (M ⊗ N) ≅ E.obj M ⊗ E.obj N)
    (ty : ∀ M N, H.obj (M ⊗ N) ≅ H.obj M ⊗ H.obj N)
    (uy : H.obj (𝟙_ D) ≅ 𝟙_ D')
    (pb : ∀ K, E.obj (P.obj K) ≅ P'.obj (H.obj K))
    (pf : ∀ M K, F.obj M ⊗ K ⟶ F.obj (M ⊗ P.obj K))
    (pf' : ∀ M K, F'.obj M ⊗ K ⟶ F'.obj (M ⊗ P'.obj K))
    (hi : ∀ M K, IsIso (pf M K))
    (hc : ∀ M K, H.map (pf M K) ≫ b.hom.app (M ⊗ P.obj K) ≫
        F'.map (finiteRingTensorPullbackComparison E P P' H tx pb M K).hom =
      (ty (F.obj M) K).hom ≫ (b.hom.app M ⊗ₘ 𝟙 (H.obj K)) ≫ pf' (E.obj M) (H.obj K))
    (hu : ∀ (Z K : D) (e : Z ⟶ 𝟙_ D),
      H.map ((e ⊗ₘ 𝟙 K) ≫ (λ_ K).hom) =
        (ty Z K).hom ≫ ((H.map e ≫ uy.hom) ⊗ₘ 𝟙 (H.obj K)) ≫ (λ_ (H.obj K)).hom)
    (hb : ∀ M N, E.map (β_ M N).hom ≫ (tx N M).hom =
      (tx M N).hom ≫ (β_ (E.obj M) (E.obj N)).hom) :
    finiteRingSiteTensorTransposeStatement E H F F' P P' PX PY
      (fun M ↦ b.hom.app M) tx ty uy pb inferInstance inferInstance pf pf' := by
  let EX := finiteRingImageLift E PX hX
  let EY := finiteRingImageLift H PY hY
  have : EX.EssSurj := by
    constructor
    intro N
    obtain ⟨M, ⟨i⟩⟩ := (hx N.obj).2 N.property
    exact ⟨M, ⟨ObjectProperty.isoMk _ i⟩⟩
  have : EY.EssSurj := by
    constructor
    intro N
    obtain ⟨M, ⟨i⟩⟩ := (hy N.obj).2 N.property
    exact ⟨M, ⟨ObjectProperty.isoMk _ i⟩⟩
  have : EX.IsEquivalence := {}
  have : EY.IsEquivalence := {}
  refine ⟨inferInstance, inferInstance, hx, hX, hY, b, fun _ ↦ rfl, ?_⟩
  intro hs R ae G ap
  let FP := finiteRingRestriction F' PX PY hs
  let bs : F ⋙ EY ≅ EX ⋙ FP :=
    NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _ (b.app M)) (by
      intro M N f
      apply ObjectProperty.hom_ext
      exact b.hom.naturality f)
  obtain ⟨rho, hrho, huniq⟩ := finiteRingAdjointTransport EX EY F R ae FP G ap bs
  have hr (L : D) : b.hom.app (R.obj L) ≫ F'.map (rho.hom.app L).hom ≫
      (ap.counit.app (EY.obj L)).hom = H.map (ae.counit.app L) :=
    congrArg (fun f ↦ f.hom) (hrho L)
  let q (M : C) (K : D) := finiteRingTensorPullbackComparison E P P' H tx pb M K
  have hiso (M : C) (K : D) : IsIso (pf' (E.obj M) (H.obj K)) := by
    have := hi M K
    have h := hc M K
    have : IsIso ((ty (F.obj M) K).hom ≫
        (b.hom.app M ⊗ₘ 𝟙 (H.obj K)) ≫ pf' (E.obj M) (H.obj K)) := by
      rw [← h]
      infer_instance
    have : IsIso ((b.hom.app M ⊗ₘ 𝟙 (H.obj K)) ≫ pf' (E.obj M) (H.obj K)) :=
      IsIso.of_isIso_comp_left (ty (F.obj M) K).hom _
    exact IsIso.of_isIso_comp_left (b.hom.app M ⊗ₘ 𝟙 (H.obj K)) _
  let pe (M : C) (K : D) : F.obj M ⊗ K ≅ F.obj (M ⊗ P.obj K) :=
    @asIso _ _ _ _ (pf M K) (hi M K)
  let pp (M : C) (K : D) : F'.obj (E.obj M) ⊗ H.obj K ≅
      F'.obj (E.obj M ⊗ P'.obj (H.obj K)) := asIso (pf' (E.obj M) (H.obj K))
  have ht (M : C) (K : D) : PX (E.obj M ⊗ P'.obj (H.obj K)) :=
    (hx _).1 ⟨M ⊗ P.obj K, ⟨q M K⟩⟩
  refine ⟨rho, hr, ?_, pe, pp, ht, fun _ _ ↦ rfl, fun _ _ ↦ rfl, hc, ?_⟩
  · intro sigma hsigma
    apply huniq sigma
    intro L
    apply ObjectProperty.hom_ext
    exact hsigma L
  · have hfirst : ∀ (M : C) (K : D) (e : F.obj M ⟶ 𝟙_ D),
        E.map (ae.homEquiv _ _ ((pe M K).inv ≫ (e ⊗ₘ 𝟙 K) ≫ (λ_ K).hom)) ≫
          (rho.hom.app K).hom =
        (q M K).hom ≫ (ap.homEquiv ⟨_, ht M K⟩ (EY.obj K)
          (ObjectProperty.homMk ((pp M K).inv ≫
            (((b.app M).inv ≫ H.map e ≫ uy.hom) ⊗ₘ 𝟙 (H.obj K)) ≫
            (λ_ (H.obj K)).hom))).hom := by
      intro M K e
      let v : F.obj (M ⊗ P.obj K) ⟶ K := (pe M K).inv ≫ (e ⊗ₘ 𝟙 K) ≫ (λ_ K).hom
      have htrans := finiteRingAdjointTransport_transpose EX EY F R ae FP G ap bs rho.hom
        hrho (M ⊗ P.obj K) K v
      let w : F'.obj (E.obj M ⊗ P'.obj (H.obj K)) ⟶ H.obj K :=
        (pp M K).inv ≫ (((b.app M).inv ≫ H.map e ≫ uy.hom) ⊗ₘ 𝟙 (H.obj K)) ≫
          (λ_ (H.obj K)).hom
      have hw : F'.map (q M K).hom ≫ w =
          b.inv.app (M ⊗ P.obj K) ≫ H.map v := by
        apply (cancel_epi (H.map (pf M K) ≫ b.hom.app (M ⊗ P.obj K))).1
        have hs := hc M K
        change H.map (pf M K) ≫ b.hom.app (M ⊗ P.obj K) ≫ F'.map (q M K).hom = _ at hs
        dsimp only [w]
        simp only [Category.assoc]
        rw [reassoc_of% hs]
        simp only [pp, asIso_inv, IsIso.hom_inv_id_assoc,
          Iso.hom_inv_id_app_assoc]
        rw [← Category.assoc (b.hom.app M ⊗ₘ 𝟙 (H.obj K)),
          tensorHom_comp_tensorHom]
        simp only [Category.id_comp]
        simp only [Iso.app_inv, b.hom_inv_id_app_assoc]
        rw [← hu]
        dsimp only [v]
        rw [H.map_comp, H.map_comp, ← Category.assoc, ← H.map_comp]
        simp only [pe, asIso_inv]
        have := hi M K
        rw [← H.map_comp, IsIso.hom_inv_id, H.map_id, Category.id_comp]
      have ht' := congrArg (fun z ↦ z.hom) htrans
      change E.map (ae.homEquiv _ _ v) ≫ (rho.hom.app K).hom =
        (ap.homEquiv (EX.obj (M ⊗ P.obj K)) (EY.obj K)
          (ObjectProperty.homMk
            (b.inv.app (M ⊗ P.obj K) ≫ H.map v))).hom at ht'
      rw [ht', ← hw]
      exact congrArg (fun z ↦ z.hom)
        (ap.homEquiv_naturality_left
          (ObjectProperty.homMk (X := EX.obj (M ⊗ P.obj K))
            (Y := ⟨E.obj M ⊗ P'.obj (H.obj K), ht M K⟩) (q M K).hom)
          (ObjectProperty.homMk (X := FP.obj ⟨_, ht M K⟩) (Y := EY.obj K) w))
    refine ⟨hfirst, ?_⟩
    intro M K e
    rw [E.map_comp, Category.assoc, hfirst]
    dsimp only [q, finiteRingTensorPullbackComparison, Iso.trans_hom, tensorIso_hom,
      Iso.refl_hom]
    simp only [Category.assoc]
    rw [reassoc_of% (hb (P.obj K) M)]
    congr 1
    rw [BraidedCategory.braiding_naturality_assoc]
    rfl

end AlgebraicGeometry.ProEtale
