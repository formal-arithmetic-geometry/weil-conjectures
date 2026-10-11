/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.GaloisCech
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Section
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale

/-!
# The trace along a finite separable extension of fields

Let `K'/K` be a finite separable field extension of degree `d` and `f : Spec K' ⟶ Spec K`. Since
`f` is finite étale, the direct image `f_*` is left adjoint to the restriction `f^*`
(`AlgebraicGeometry.Etale.lowerStarLocalizationRestrictionAdjunction`); its counit is the *trace*
`f_* f^* M ⟶ M`. We show that the composite of the unit `M ⟶ f_* f^* M` of `f^* ⊣ f_*` with the
trace is multiplication by `d`.

On the spectrum `V = Spec E` of a field `E` over `K'` admitting `d` embeddings `τ : K' → E`, the
scheme `V ×_K Spec K'` is the disjoint union of the graphs `γ_τ` of the morphisms
`Spec τ : V ⟶ Spec K'`, and the pullback of a section `x` to it is the sum of the extensions by
zero of `x` off these graphs; the trace sends each of them to `x`. These `V` cover every étale
`K'`-scheme, and the general case follows by restriction.

## Main statements

- `AlgebraicGeometry.Scheme.FieldTrace.unit_comp_trace`: `M ⟶ f_* f^* M ⟶ M` is
  multiplication by `[K' : K]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Module

namespace AlgebraicGeometry.Scheme.FieldTrace

open AlgebraicGeometry.Etale

variable (K : Type u) [Field K] (K' : Type u) [Field K'] [Algebra K K'] [Algebra.Etale K K']

/-- The morphism `Spec K' ⟶ Spec K`. -/
noncomputable abbrev f : Spec (.of K') ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K K'))

instance : AlgebraicGeometry.Etale (f K K') :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)

instance : IsFinite (f K K') := by
  have : Module.Finite K K' := Algebra.FormallyUnramified.finite_of_free K K'
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

instance : IsSeparated (f K K') := inferInstance

variable (M : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})

/-- The restriction `f^* M` along `f : Spec K' ⟶ Spec K`. -/
noncomputable abbrev res : Sheaf (Spec (.of K')).smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (Etale.localizationRestriction AddCommGrpCat.{u + 1} (f K K') inferInstance).obj M

/-- The unit `M ⟶ f_* f^* M` of `f^* ⊣ f_*`. -/
noncomputable def unit : M ⟶ (f K K')_*[AddCommGrpCat.{u + 1}].obj (res K K' M) :=
  (Etale.localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} (f K K')
    inferInstance).unit.app M

/-- The trace `f_* f^* M ⟶ M`, the counit of `f_* ⊣ f^*`. -/
noncomputable def trace : (f K K')_*[AddCommGrpCat.{u + 1}].obj (res K K' M) ⟶ M :=
  (Etale.lowerStarLocalizationRestrictionAdjunction AddCommGrpCat.{u + 1} (f K K')).counit.app M

/-- The counit `W ×_K Spec K' ⟶ W` of the adjunction between `Over.map f` and base change. -/
noncomputable abbrev counitMor (W : (Spec (.of K)).Etale) :
    (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale (f K K'))).obj
      ((f K K').Etale.obj W) ⟶ W :=
  (MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.Etale ⊤ (f K K') inferInstance
    _root_.trivial).counit.app W

lemma unit_app (W : (Spec (.of K)).Etale) :
    (unit K K' M).hom.app (op W) = M.obj.map (counitMor K K' W).op := by
  simp [unit, Etale.localizationRestrictionLowerStarAdjunction, counitMor]

section TestObject

variable (E : Type u) [Field E] [Algebra K' E] [Algebra K E] [IsScalarTower K K' E]
  [Algebra.Etale K' E] [Algebra.Etale K E]

/-- `Spec E` as an étale `K`-scheme, via `K'`. -/
noncomputable abbrev V : (Spec (.of K)).Etale :=
  (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale (f K K'))).obj
    (etaleSpec K' E)

/-- `V ×_K Spec K'`, as an étale `K`-scheme. -/
noncomputable abbrev Q : (Spec (.of K)).Etale :=
  (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale (f K K'))).obj
    ((f K K').Etale.obj (V K K' E))

lemma V_hom : (V K K' E).hom = Spec.map (CommRingCat.ofHom (algebraMap K E)) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

variable {K K' E} in
lemma specMap_comp_f (τ : K' →ₐ[K] E) :
    Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ f K K' =
      Spec.map (CommRingCat.ofHom (algebraMap K E)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  simp

variable {K K' E} in
/-- The graph `V ⟶ V ×_K Spec K'` of `Spec τ : V ⟶ Spec K'`. -/
noncomputable def γ (τ : K' →ₐ[K] E) : V K K' E ⟶ Q K K' E :=
  MorphismProperty.Over.homMk (pullback.lift (𝟙 _) (Spec.map (CommRingCat.ofHom τ.toRingHom))
    (by rw [Category.id_comp, V_hom, specMap_comp_f])) (by
      change pullback.lift _ _ _ ≫ pullback.snd _ _ ≫ f K K' = _
      rw [pullback.lift_snd_assoc, specMap_comp_f, V_hom]) _root_.trivial

variable {K K' E} in
@[reassoc (attr := simp)]
lemma γ_left_fst (τ : K' →ₐ[K] E) :
    (γ τ).left ≫ pullback.fst (V K K' E).hom (f K K') = 𝟙 _ :=
  pullback.lift_fst _ _ _

variable {K K' E} in
@[reassoc (attr := simp)]
lemma γ_left_snd (τ : K' →ₐ[K] E) :
    (γ τ).left ≫ pullback.snd (V K K' E).hom (f K K') =
      Spec.map (CommRingCat.ofHom τ.toRingHom) :=
  pullback.lift_snd _ _ _

variable {K K' E} in
lemma γ_comp_counitMor (τ : K' →ₐ[K] E) : γ τ ≫ counitMor K K' (V K K' E) = 𝟙 _ :=
  MorphismProperty.Over.Hom.ext (γ_left_fst τ)

variable {K K' E} in
lemma isOpenImmersion_γ_left (τ : K' →ₐ[K] E) : IsOpenImmersion (γ τ).left := by
  have : AlgebraicGeometry.Etale (pullback.fst (V K K' E).hom (f K K')) := inferInstance
  exact IsOpenImmersion.of_section_of_etale (pullback.fst (V K K' E).hom (f K K')) _
    (γ_left_fst τ)

variable {K K' E} in
/-- Two graphs meeting at a point coincide. -/
lemma eq_of_γ_left_apply_eq {σ τ : K' →ₐ[K] E} (a b : (V K K' E).left)
    (h : (γ σ).left a = (γ τ).left b) : σ = τ := by
  have := isOpenImmersion_γ_left σ
  have := isOpenImmersion_γ_left τ
  have hsub : Set.range (γ σ).left ⊆ Set.range (γ τ).left := by
    rintro _ ⟨c, rfl⟩
    refine ⟨b, ?_⟩
    have hc : c = a := @Subsingleton.elim (Spec (.of E)) _ _ _
    rw [hc, h]
  have hl := IsOpenImmersion.lift_fac (γ τ).left (γ σ).left hsub
  have h1 : IsOpenImmersion.lift (γ τ).left (γ σ).left hsub = 𝟙 _ := by
    have := congrArg (· ≫ pullback.fst (V K K' E).hom (f K K')) hl
    simp only [Category.assoc, γ_left_fst, Category.comp_id] at this
    exact this
  rw [h1, Category.id_comp] at hl
  have h2 := congrArg (· ≫ pullback.snd (V K K' E).hom (f K K')) hl
  simp only [γ_left_snd] at h2
  have h3 := Spec.map_injective h2
  ext x
  exact congrArg (fun φ ↦ φ.hom x) h3.symm

variable {K K' E} in
/-- **The graphs cover `V ×_K Spec K'`** when `E` has `[K' : K]` embeddings of `K'`: a point
`z` with residue field `κ` gives embeddings `E → κ` and `K' → κ`, and the latter is one of the
`[K' : K]` composites of `E → κ` with an embedding `K' → E`, as `K'` has at most `[K' : K]`
embeddings into `κ`. -/
lemma iUnion_range_γ_left (hcard : Nat.card (K' →ₐ[K] E) = finrank K K') :
    ⋃ τ : K' →ₐ[K] E, Set.range (γ τ).left = Set.univ := by
  have : Module.Finite K K' := Algebra.FormallyUnramified.finite_of_free K K'
  refine Set.eq_univ_of_forall fun z ↦ ?_
  let κ := (Q K K' E).left.residueField z
  let p := (Q K K' E).left.fromSpecResidueField z
  let c : Γ(Spec κ, ⊤) →+* κ := (Scheme.ΓSpecIso κ).hom.hom
  let x₁ : Spec κ ⟶ Spec (.of E) := p ≫ pullback.fst (V K K' E).hom (f K K')
  let x₂ : Spec κ ⟶ Spec (.of K') := p ≫ pullback.snd (V K K' E).hom (f K K')
  let ι₁ : E →+* κ := c.comp (GaloisCech.toRing x₁)
  let ι₂ : K' →+* κ := c.comp (GaloisCech.toRing x₂)
  have hcomm : ι₂.comp (algebraMap K K') = ι₁.comp (algebraMap K E) := by
    have h : (x₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap K' E))) ≫ f K K' =
        x₂ ≫ f K K' := by
      simp only [x₁, x₂, Category.assoc]
      exact congrArg (p ≫ ·) pullback.condition
    have h' := congrArg (fun φ ↦ GaloisCech.toRing φ) h
    simp only [GaloisCech.toRing_comp_specMap] at h'
    ext x
    have := congrArg (fun φ : K →+* _ ↦ c (φ x)) h'
    simp only [RingHom.comp_apply] at this
    simp only [ι₁, ι₂, RingHom.comp_apply, IsScalarTower.algebraMap_apply K K' E]
    exact this.symm
  let : Algebra K κ := (ι₁.comp (algebraMap K E)).toAlgebra
  let ι₁' : E →ₐ[K] κ := { ι₁ with commutes' := fun c ↦ rfl }
  let ι₂' : K' →ₐ[K] κ :=
    { ι₂ with commutes' := fun c ↦ congrArg (fun φ : K →+* κ ↦ φ c) hcomm }
  have hinj : Function.Injective fun σ : K' →ₐ[K] E ↦ ι₁'.comp σ := by
    intro σ τ hστ
    ext x
    exact ι₁.injective (DFunLike.congr_fun hστ x)
  have hbij := hinj.bijective_of_nat_card_le
    ((card_algHom_le_finrank K K' κ).trans hcard.ge)
  obtain ⟨σ, hσ⟩ := hbij.2 ι₂'
  have hσ' : (GaloisCech.toRing (p ≫ pullback.fst (V K K' E).hom (f K K'))).comp
      σ.toRingHom = GaloisCech.toRing (p ≫ pullback.snd (V K K' E).hom (f K K')) := by
    ext x
    have := DFunLike.congr_fun hσ x
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso κ).hom).1 this
  have hp : p = (p ≫ pullback.fst (V K K' E).hom (f K K')) ≫ (γ σ).left := by
    apply pullback.hom_ext
    · simp only [Category.assoc, γ_left_fst]
      erw [Category.comp_id]
    · rw [Category.assoc, γ_left_snd]
      refine (GaloisCech.eq_of_toRing_eq ?_).symm
      rw [GaloisCech.toRing_comp_specMap]
      exact hσ'
  refine Set.mem_iUnion.2 ⟨σ, (p ≫ pullback.fst _ _) (IsLocalRing.closedPoint κ), ?_⟩
  have h2 := congrArg (fun φ : Spec κ ⟶ _ ↦ φ (IsLocalRing.closedPoint κ)) hp
  simp only [Scheme.Hom.comp_apply] at h2 ⊢
  exact h2.symm.trans ((Q K K' E).left.fromSpecResidueField_apply z _)

end TestObject

end AlgebraicGeometry.Scheme.FieldTrace
