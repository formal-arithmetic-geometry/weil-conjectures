/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.RingTheory.TensorProduct.Quotient
public import WeilConjectures.CategoryTheory.Sites.PullbackCounitIso
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.RingTheory.ProEtale.ClosedLift
public import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale

/-!
# Lifting objects of the pro-étale site of a closed subscheme

Let `i : Z ⟶ X` be a closed immersion and `u : X_proét ⥤ Z_proét` the base change functor
`W ↦ W ×_X Z`. Every object `V` of `Z_proét` with a morphism `ψ : V ⟶ u W` is covered by
objects
of the form `u W'`, for objects `W'` of `X_proét` over `W`, compatibly with `ψ`
(`AlgebraicGeometry.Scheme.ProEt.generate_liftPresieve_mem_topology`).

Locally `W = Spec A` is affine, its closed fibre is `Spec (A ⧸ I)`, and `V` is covered by
`Spec C̄` with `C̄` ind-étale over `A ⧸ I` (`Algebra.WeaklyEtale.exists_indEtale`). The lift
`W' = Spec H_A(C̄)` of `Algebra.ClosedLift` (blueprint `def-exc-closed-site-lift`) then satisfies
`u W' = Spec (H_A(C̄) ⊗_A A ⧸ I) ≅ Spec C̄` by the reduction isomorphism
(`Algebra.ClosedLift.bijective_reduction`, blueprint `lem-exc-closed-lift-reduction`).

This is the geometric input to the full faithfulness of the closed direct image on pro-étale
sheaves (blueprint `lem-exc-proetale-closed-fully-faithful`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.ProEt

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]


/-- **Local lifting along a closed immersion.** Let `ψ : V ⟶ W ×_X Z` be a morphism of
`Z_proét`
and `x` a point of `V`. There are an affine open `b : Spec C₀ ⟶ V` around `x` and a surjective
quasi-compact morphism `p : V' ⟶ Spec C₀` of `Z_proét` such that `V'` is isomorphic to the base
change `W' ×_X Z` of an object `W'` of `X_proét` over `W`, compatibly with `ψ`. -/
theorem exists_liftPresieve {V : Z.ProEt} {W : X.ProEt}
    (ψ : V ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).obj W) (x : V.left) :
    ∃ (C₀ : CommRingCat.{u}) (b : Spec C₀ ⟶ V.left) (_ : IsOpenImmersion b),
      x ∈ Set.range b.base ∧ ∃ (V' : Z.ProEt) (p : V' ⟶ ofOpenImmersion V b),
        Surjective p.left ∧ QuasiCompact p.left ∧
          (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).liftPresieve ψ
            (p ≫ ofOpenImmersionHom V b) := by
  classical
  -- an affine chart `a : Spec A ⟶ W` around the image of `x`
  obtain ⟨A, a, ha, hya, -⟩ := exists_affine_mem_range_and_range_subset (X := W.left)
    (x := (ψ.left ≫ pullback.fst W.hom i).base x) (U := ⊤) trivial
  -- the closed fibre of the chart is `Spec (A ⧸ I)`
  obtain ⟨I, e, he⟩ := (IsClosedImmersion.Spec_iff (f := pullback.fst (a ≫ W.hom) i)).1
    inferInstance
  -- an affine chart `b : Spec C₀ ⟶ V` around `x` mapping into the chart `a`
  have hxO : x ∈ (ψ.left ≫ pullback.fst W.hom i) ⁻¹ᵁ a.opensRange := by
    exact hya
  obtain ⟨C₀, b, hb, hxb, hbO⟩ := exists_affine_mem_range_and_range_subset hxO
  have hrange : Set.range (b ≫ ψ.left ≫ pullback.fst W.hom i).base ⊆ Set.range a.base := by
    rintro _ ⟨y, rfl⟩
    exact hbO ⟨y, rfl⟩
  let m : Spec C₀ ⟶ Spec A := IsOpenImmersion.lift a _ hrange
  have hm : m ≫ a = b ≫ ψ.left ≫ pullback.fst W.hom i := IsOpenImmersion.lift_fac _ _ _
  have hψ : ψ.left ≫ pullback.snd W.hom i = V.hom := MorphismProperty.Over.w ψ
  let n : Spec C₀ ⟶ pullback (a ≫ W.hom) i :=
    pullback.lift m (b ≫ V.hom) (by
      rw [← Category.assoc, hm, Category.assoc, Category.assoc, pullback.condition,
        ← Category.assoc ψ.left, hψ, Category.assoc])
  have hn : WeaklyEtale n := by
    refine MorphismProperty.of_postcomp (W := @WeaklyEtale) (W' := @WeaklyEtale) n
      (pullback.snd (a ≫ W.hom) i) inferInstance ?_
    rw [pullback.lift_snd]
    infer_instance
  -- the ring map `A ⧸ I ⟶ C₀`
  obtain ⟨θ, hθ⟩ := Spec.map_surjective (n ≫ e.hom)
  let : Algebra (A ⧸ I) C₀ := θ.hom.toAlgebra
  have : Algebra.WeaklyEtale (A ⧸ I) C₀ := by
    rw [← weaklyEtale_SpecMap_algebraMap_iff]
    change WeaklyEtale (Spec.map θ)
    rw [hθ]
    infer_instance
  -- an ind-étale faithfully flat cover `C₀ ⟶ C̄` with `C̄` ind-étale over `A ⧸ I`
  obtain ⟨T, _, _, _, _, hT₁, hT₂, hT₃⟩ :=
    Algebra.WeaklyEtale.exists_indEtale (A ⧸ I) C₀
  let : Algebra A T := ((algebraMap (A ⧸ I) T).comp (Ideal.Quotient.mk I)).toAlgebra
  have : IsScalarTower A (A ⧸ I) T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- the lift `H = H_A(C̄)`
  let H := Algebra.ClosedLift A T
  let κ : C₀ ⟶ CommRingCat.of T := CommRingCat.ofHom (algebraMap C₀ T)
  let W' : X.ProEt :=
    Scheme.ProEt.mk (Spec.map (CommRingCat.ofHom (algebraMap A H)) ≫ a ≫ W.hom)
  let h : W' ⟶ W :=
    MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A H)) ≫ a)
  let V' : Z.ProEt := Scheme.ProEt.mk (Spec.map κ ≫ b ≫ V.hom)
  let p : V' ⟶ ofOpenImmersion V b := MorphismProperty.Over.homMk (Spec.map κ)
  -- the reduction isomorphism `H ⊗_A (A ⧸ I) ≃ C̄`
  let j : TensorProduct A H (A ⧸ I) ≃+* T :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot H I).symm.toRingEquiv.trans
      (RingEquiv.ofBijective _ (Algebra.ClosedLift.bijective_reduction A T I))
  have hj₁ : ∀ x : H, j (x ⊗ₜ 1) = Algebra.ClosedLift.toAlgHom A T x := by
    intro x
    simp only [j, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
      RingEquiv.ofBijective_apply]
    erw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul, one_smul]
    rfl
  have hj₂ : ∀ r : A ⧸ I, j (1 ⊗ₜ r) = algebraMap (A ⧸ I) T r := by
    intro r
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    simp only [j, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
      Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul, Algebra.smul_def, mul_one,
      RingEquiv.ofBijective_apply]
    change Algebra.ClosedLift.toAlgHom A T (algebraMap A H r) = _
    exact (Algebra.ClosedLift.toAlgHom A T).commutes r
  have hAT : CommRingCat.ofHom (algebraMap A T) =
      CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ θ ≫ κ := by
    ext r
    change algebraMap (A ⧸ I) T (Ideal.Quotient.mk I r) =
      algebraMap C₀ T (algebraMap (A ⧸ I) C₀ (Ideal.Quotient.mk I r))
    rw [← IsScalarTower.algebraMap_apply]
  have hspecAT : Spec.map (CommRingCat.ofHom (algebraMap A T)) = Spec.map κ ≫ m := by
    rw [hAT, Spec.map_comp, Spec.map_comp, hθ]
    simp only [Category.assoc]
    rw [← he]
    simp [n]
  -- the identification `Spec C̄ ≅ W' ×_X Z`
  have : IsIso (CommRingCat.ofHom (j : TensorProduct A H (A ⧸ I) →+* T)) :=
    inferInstanceAs (IsIso j.toCommRingCatIso.hom)
  let E : Spec (.of T) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap A H)) ≫ a ≫ W.hom) i :=
    asIso (Spec.map (CommRingCat.ofHom (j : TensorProduct A H (A ⧸ I) →+* T))) ≪≫
      (pullbackSpecIso A H (A ⧸ I)).symm ≪≫
      asIso (pullback.map _ _ _ _ (𝟙 _) e.inv (𝟙 _) (by simp) (by simp [he])) ≪≫
      pullbackRightPullbackFstIso (a ≫ W.hom) i (Spec.map (CommRingCat.ofHom (algebraMap A H)))
  have hE₁ :
      E.hom ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A H)) ≫ a ≫ W.hom) i =
      Spec.map (CommRingCat.ofHom (Algebra.ClosedLift.toAlgHom A T : H →+* T)) := by
    simp only [E, Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc,
      pullbackRightPullbackFstIso_hom_fst, pullback.lift_fst, Category.comp_id,
      pullbackSpecIso_inv_fst]
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact hj₁ x
  have hjr : CommRingCat.ofHom (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
      A ⧸ I →ₐ[A] TensorProduct A H (A ⧸ I))) ≫
      CommRingCat.ofHom (j : TensorProduct A H (A ⧸ I) →+* T) = θ ≫ κ := by
    ext r
    change j (1 ⊗ₜ r) = algebraMap C₀ T (θ r)
    rw [hj₂, IsScalarTower.algebraMap_apply (A ⧸ I) C₀ T]
    rfl
  have hE₂ :
      E.hom ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A H)) ≫ a ≫ W.hom) i =
      Spec.map κ ≫ b ≫ V.hom := by
    simp only [E, Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc,
      pullbackRightPullbackFstIso_hom_snd, pullback.lift_snd_assoc,
      pullbackSpecIso_inv_snd_assoc]
    rw [← Spec.map_comp_assoc]
    erw [hjr]
    rw [Spec.map_comp, Category.assoc, hθ, Category.assoc, e.hom_inv_id_assoc, pullback.lift_snd]
  let c : V' ≅ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).obj W' :=
    MorphismProperty.Over.isoMk E hE₂
  have hpq : QuasiCompact p.left := by
    change QuasiCompact (Spec.map κ)
    infer_instance
  refine ⟨C₀, b, hb, hxb, V', p, ?_, hpq, W', h, c, ?_⟩
  · have : Module.FaithfullyFlat C₀ T := hT₂
    exact ((flat_and_surjective_SpecMap_iff κ).2
      (RingHom.faithfullyFlat_algebraMap_iff.2 this)).2
  · ext1
    apply pullback.hom_ext
    · simp only [MorphismProperty.Over.pullback_map_left,
        MorphismProperty.Comma.comp_left, Category.assoc, pullback.lift_fst]
      change E.hom ≫
          pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A H)) ≫ a ≫ W.hom) i ≫
          Spec.map (CommRingCat.ofHom (algebraMap A H)) ≫ a =
        Spec.map κ ≫ b ≫ ψ.left ≫ pullback.fst W.hom i
      rw [reassoc_of% hE₁, ← Spec.map_comp_assoc, ← hm, ← Category.assoc, ← hspecAT]
      congr 2
      ext r
      exact (Algebra.ClosedLift.toAlgHom A T).commutes r
    · simp only [MorphismProperty.Over.pullback_map_left,
        MorphismProperty.Comma.comp_left, Category.assoc, pullback.lift_snd]
      change E.hom ≫
          pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A H)) ≫ a ≫ W.hom) i =
        Spec.map κ ≫ b ≫ ψ.left ≫ pullback.snd W.hom i
      rw [hE₂, hψ]

/-- Let `i : Z ⟶ X` be a closed immersion and `ψ : V ⟶ W ×_X Z` a morphism of `Z_proét`. The
morphisms `f : V' ⟶ V` such that `f ≫ ψ` is, up to isomorphism, the base change of a morphism
`W' ⟶ W` of `X_proét` generate a covering sieve: locally on `V`, they are the lifts of
`AlgebraicGeometry.Scheme.ProEt.exists_liftPresieve`. -/
theorem generate_liftPresieve_mem_topology {V : Z.ProEt} {W : X.ProEt}
    (ψ : V ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).obj W) :
    Sieve.generate ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).liftPresieve ψ) ∈
      topology Z V := by
  let S := Sieve.generate ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).liftPresieve ψ)
  let R : Sieve V :=
    { arrows := fun _ f ↦ S.pullback f ∈ topology Z _
      downward_closed := fun {_ _ f} hf g ↦ by
        rw [Sieve.pullback_comp]
        exact (topology Z).pullback_stable g hf }
  choose C₀ b hb hxb V' p hp hpq hpS using exists_liftPresieve i ψ
  have hR : R ∈ topology Z V := by
    refine mem_topology_of_openImmersion R b (fun x ↦ ⟨x, hxb x⟩) fun x ↦ ?_
    change S.pullback _ ∈ topology Z _
    rw [mem_topology_iff]
    refine ⟨Presieve.singleton (p x), ?_, ?_⟩
    · rw [mem_precoverage_iff, Presieve.map_singleton]
      have : Surjective ((ProEt.forget Z ⋙ Over.forget Z).map (p x)) := hp x
      have : QuasiCompact ((ProEt.forget Z ⋙ Over.forget Z).map (p x)) := hpq x
      exact Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale)
        (MorphismProperty.of_postcomp (W := @WeaklyEtale) (W' := @WeaklyEtale) (p x).left
          (ofOpenImmersion V (b x)).hom (ofOpenImmersion V (b x)).prop
          (by rw [MorphismProperty.Over.w (p x)]; exact (V' x).prop))
    · rintro _ _ ⟨⟩
      exact Sieve.le_generate _ _ _ (hpS x)
  exact (topology Z).transitive hR S (fun _ f hf ↦ hf)

/-- Every object of the pro-étale site of a closed subscheme `Z ⊆ X` is covered by base changes
`W' ×_X Z` of objects `W'` of `X_proét`. -/
theorem generate_exists_iso_mem_topology (V : Z.ProEt) :
    Sieve.generate (fun V' (_ : V' ⟶ V) ↦ ∃ W' : X.ProEt,
      Nonempty (V' ≅ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).obj W')) ∈
      topology Z V := by
  let ψ : V ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).obj (Scheme.ProEt.mk (𝟙 X)) :=
    MorphismProperty.Over.homMk (pullback.lift (V.hom ≫ i) V.hom (by erw [Category.comp_id]))
      (by simp)
  refine (topology Z).superset_covering ?_ (generate_liftPresieve_mem_topology i ψ)
  rw [Sieve.generate_le_iff]
  intro V' f hf
  obtain ⟨W', -, c, -⟩ := hf
  exact Sieve.le_generate _ _ _ ⟨W', ⟨c⟩⟩

end AlgebraicGeometry.Scheme.ProEt
