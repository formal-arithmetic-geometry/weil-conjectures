/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FormallyUnramifiedSections
public import WeilConjectures.WeilSheaf.ConstantFieldComponent

/-!
# The geometric fibre over a smaller base field is a disjoint union of components

Let `k₀ ⊆ k'` be fields with `k'` algebraic over `k₀`, and let `V` be a scheme over `k'` through
`c : V ⟶ Spec k'`, hence over `k₀` through `f = c ≫ (Spec k' ⟶ Spec k₀)`. Put
`S = Spec k' ×_{k₀} Spec k̄`. The geometric fibre `V ⊗_{k₀} k̄` maps to `S`
(`AlgebraicGeometry.Scheme.Hom.geometricFiberToConstantFieldFiber`), and is the base change of
`c` along `S ⟶ Spec k'`. The component map `θ : V ⊗_{k'} k̄' ⟶ V ⊗_{k₀} k̄`
(`AlgebraicGeometry.Scheme.Hom.geometricFiberComponentMap`) is the base change of a section
`s₀ : Spec k̄ ⟶ S` of the projection `S ⟶ Spec k̄`; when `k'/k₀` is separable, sections of this
étale projection are open immersions, so `θ` is an open immersion onto the preimage of the
range of `s₀` (`AlgebraicGeometry.Scheme.Hom.isOpenImmersion_geometricFiberComponentMap`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {k₀ k' : Type u} [Field k₀] [Field k'] [Algebra k₀ k'] [Algebra.IsAlgebraic k₀ k']
  {V : Scheme.{u}} (c : V ⟶ Spec (.of k')) (f : V ⟶ Spec (.of k₀))
  (hc : c ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k')) = f)

variable (k₀ k') in
/-- The scheme `S = Spec k' ×_{k₀} Spec k̄`. -/
abbrev constantFieldFiber : Scheme.{u} :=
  pullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ k'))) (Scheme.specAlgebraicClosure k₀).hom

include hc in
/-- The map `V ⊗_{k₀} k̄ ⟶ Spec k' ×_{k₀} Spec k̄` induced by `c`. -/
def geometricFiberToConstantFieldFiber : f.geometricFiber ⟶ constantFieldFiber k₀ k' :=
  pullback.lift (f.geometricFiberProj ≫ c) f.geometricFiberToAlgebraicClosure (by
    rw [Category.assoc, hc, geometricFiber_condition])

@[reassoc (attr := simp)]
lemma geometricFiberToConstantFieldFiber_fst :
    geometricFiberToConstantFieldFiber c f hc ≫ pullback.fst _ _ = f.geometricFiberProj ≫ c :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma geometricFiberToConstantFieldFiber_snd :
    geometricFiberToConstantFieldFiber c f hc ≫ pullback.snd _ _ =
      f.geometricFiberToAlgebraicClosure :=
  pullback.lift_snd _ _ _

/-- The geometric fibre `V ⊗_{k₀} k̄` is the base change of `c : V ⟶ Spec k'` along
`S ⟶ Spec k'`. -/
lemma isPullback_geometricFiberToConstantFieldFiber :
    IsPullback f.geometricFiberProj (geometricFiberToConstantFieldFiber c f hc) c
      (pullback.fst _ _) := by
  refine IsPullback.of_bot ?_ (geometricFiberToConstantFieldFiber_fst c f hc).symm
    (IsPullback.of_hasPullback _ _)
  rw [geometricFiberToConstantFieldFiber_snd, hc]
  exact IsPullback.of_hasPullback _ _

/-- The section `s₀ : Spec k̄ ⟶ S` given by `k' ⟶ k̄' ≅ k̄`. -/
def constantFieldFiberSection : Spec (.of (AlgebraicClosure k₀)) ⟶ constantFieldFiber k₀ k' :=
  pullback.lift (Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k').toRingHom) ≫
    (Scheme.specAlgebraicClosure k').hom) (𝟙 _) (by
    rw [Category.id_comp, Category.assoc]
    simp only [Scheme.specAlgebraicClosure, Over.mk_hom, ← Spec.map_comp]
    congr 1
    ext x
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply]
    exact (algebraicClosureAlgEquiv k₀ k').commutes x)

@[reassoc (attr := simp)]
lemma constantFieldFiberSection_snd :
    constantFieldFiberSection (k₀ := k₀) (k' := k') ≫ pullback.snd _ _ = 𝟙 _ :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma constantFieldFiberSection_fst :
    constantFieldFiberSection (k₀ := k₀) (k' := k') ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k').toRingHom) ≫
        (Scheme.specAlgebraicClosure k').hom :=
  pullback.lift_fst _ _ _

/-- The component map `θ` is the base change of the section `s₀` along
`V ⊗_{k₀} k̄ ⟶ S`. -/
lemma isPullback_geometricFiberComponentMap :
    IsPullback (geometricFiberComponentMap c f hc)
      (c.geometricFiberToAlgebraicClosure ≫
        Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k').symm.toRingHom))
      (geometricFiberToConstantFieldFiber c f hc) constantFieldFiberSection := by
  let e : Spec (.of (AlgebraicClosure k')) ≅ Spec (.of (AlgebraicClosure k₀)) :=
    Scheme.Spec.mapIso (algebraicClosureAlgEquiv k₀ k').symm.toRingEquiv.toCommRingCatIso.op
  refine IsPullback.of_right ?_ ?_ (isPullback_geometricFiberToConstantFieldFiber c f hc)
  · rw [geometricFiberComponentMap_comp_geometricFiberProj, constantFieldFiberSection_fst]
    have h := (IsPullback.of_hasPullback c (Scheme.specAlgebraicClosure k').hom)
    refine IsPullback.of_iso h (Iso.refl _) (Iso.refl _) e (Iso.refl _) ?_ ?_ ?_ ?_
    · simp only [Iso.refl_hom, Category.comp_id]
      rfl
    · simp only [Iso.refl_hom, Category.id_comp]
      rfl
    · simp
    · have he : e.hom = Spec.map (CommRingCat.ofHom
          (algebraicClosureAlgEquiv k₀ k').symm.toRingEquiv.toRingHom) := rfl
      simp only [Iso.refl_hom, Category.comp_id]
      rw [he, ← Category.assoc, spec_map_comp_spec_map_eq _ _ (RingHom.id _) (fun x ↦ by simp),
        CommRingCat.ofHom_id, Spec.map_id]
      exact (Category.id_comp _).symm
  · refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, geometricFiberToConstantFieldFiber_fst,
        geometricFiberComponentMap_comp_geometricFiberProj_assoc, constantFieldFiberSection_fst]
      have h1 : Spec.map (CommRingCat.ofHom
            (algebraicClosureAlgEquiv k₀ k').symm.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k').toRingHom) = 𝟙 _ := by
        rw [spec_map_comp_spec_map_eq _ _ (RingHom.id _) (fun x ↦ by simp), CommRingCat.ofHom_id,
          Spec.map_id]
      rw [geometricFiber_condition]
      erw [reassoc_of% h1]
    · simp

section Separable

variable [Algebra.IsSeparable k₀ k'] [Module.Finite k₀ k']

variable (k₀ k') in
lemma formallyUnramified_specMap_algebraMap :
    FormallyUnramified (Spec.map (CommRingCat.ofHom (algebraMap k₀ k'))) := by
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
  exact RingHom.formallyUnramified_algebraMap.2 (Algebra.FormallyUnramified.of_isSeparable k₀ k')

omit [Algebra.IsAlgebraic k₀ k'] [Algebra.IsSeparable k₀ k'] in
variable (k₀ k') in
lemma locallyOfFiniteType_specMap_algebraMap :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k₀ k'))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.2 inferInstance

variable (k₀ k') in
/-- The projection `S ⟶ Spec k̄` is formally unramified and locally of finite type. -/
lemma formallyUnramified_constantFieldFiber_snd :
    FormallyUnramified (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k₀ k')))
      (Scheme.specAlgebraicClosure k₀).hom) :=
  have := formallyUnramified_specMap_algebraMap k₀ k'
  MorphismProperty.pullback_snd _ _ inferInstance

variable (k₀ k') in
lemma locallyOfFiniteType_constantFieldFiber_snd :
    LocallyOfFiniteType (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k₀ k')))
      (Scheme.specAlgebraicClosure k₀).hom) :=
  have := locallyOfFiniteType_specMap_algebraMap k₀ k'
  MorphismProperty.pullback_snd _ _ inferInstance

/-- The section `s₀` is an open immersion. -/
lemma isOpenImmersion_constantFieldFiberSection :
    IsOpenImmersion (constantFieldFiberSection (k₀ := k₀) (k' := k')) :=
  have := formallyUnramified_constantFieldFiber_snd k₀ k'
  have := locallyOfFiniteType_constantFieldFiber_snd k₀ k'
  FormallyUnramified.isOpenImmersion_of_comp_eq_id _ _ constantFieldFiberSection_snd

/-- **The component map is an open immersion.** -/
instance isOpenImmersion_geometricFiberComponentMap :
    IsOpenImmersion (geometricFiberComponentMap c f hc) :=
  have := isOpenImmersion_constantFieldFiberSection (k₀ := k₀) (k' := k')
  MorphismProperty.of_isPullback (isPullback_geometricFiberComponentMap c f hc).flip inferInstance

end Separable

end AlgebraicGeometry.Scheme.Hom
