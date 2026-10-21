/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.AlgebraicGeometry.RelativeProjData
import WeilConjectures.AlgebraicGeometry.RelativeProj.GradedTensor
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme

/-! # Affine restriction of relative Proj charts

Source: Stacks Project, Constructions, Tags 01NO and 01NP.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TensorProduct

noncomputable section

namespace AlgebraicGeometry.RelativeProjAlgebra

private theorem baseChange_of_directSum
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M N : ℕ → Type*} [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (M i)] [∀ i, Module R (N i)] [∀ i, Module S (N i)]
    [∀ i, IsScalarTower R S (N i)] (f : ∀ i, M i →ₗ[R] N i)
    (h : IsBaseChange S (DirectSum.lmap f)) (i : ℕ) : IsBaseChange S (f i) := by
  classical
  let e := TensorProduct.directSumRight R S S M
  let g := DirectSum.lmap (fun i ↦ (f i).liftBaseChange S)
  have hg : g.comp e.toLinearMap = h.equiv.toLinearMap := by
    apply LinearMap.ext
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
        apply DirectSum.ext
        intro j
        simp [g, e, TensorProduct.directSumRight_tmul, IsBaseChange.equiv_tmul,
          DirectSum.smul_apply]
    | add x y hx hy => simp_all
  have hb : Function.Bijective g := by
    have hh : Function.Bijective (g.comp e.toLinearMap) := by
      rw [hg]
      exact h.equiv.bijective
    exact (Function.Bijective.of_comp_iff g e.bijective).mp hh
  have hi : Function.Bijective ((f i).liftBaseChange S) :=
    ⟨(DirectSum.lmap_injective _).mp hb.1 i, (DirectSum.lmap_surjective _).mp hb.2 i⟩
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective _ hi) (by simp)

variable {X : Scheme.{u}} (A : RelativeProjAlgebra X)

private noncomputable instance sectionAlgebra (V : X.affineOpens) :
    Algebra Γ(X, V.1) (A.sections V) := (A.algebra.obj.hom.hom.app (op V.1)).hom.toAlgebra

private noncomputable def grade (V : X.affineOpens) (n : ℕ) :
    Submodule Γ(X, V.1) (A.sections V) :=
  ((Sigma.ι A.piece n ≫ A.decomposition.hom).val.app (op V.1)).hom.range

private noncomputable instance gradeRing (V : X.affineOpens) : GradedAlgebra (A.grade V) where
  toDecomposition :=
    { decompose' := DirectSum.decompose (A.sectionGrade V)
      left_inv := fun a ↦ (DirectSum.decompose (A.sectionGrade V)).left_inv a
      right_inv := fun a ↦ (DirectSum.decompose (A.sectionGrade V)).right_inv a }
  one_mem := A.sectionGrade_one V
  mul_mem := A.sectionGrade_mul V

private def toGrade (V : X.affineOpens) : A.sectionGrade V →+*ᵍ A.grade V :=
  { RingHom.id _ with map_mem := fun ha ↦ ha }

private def fromGrade (V : X.affineOpens) : A.grade V →+*ᵍ A.sectionGrade V :=
  { RingHom.id _ with map_mem := fun ha ↦ ha }

private lemma toGrade_irrelevant (V : X.affineOpens) :
    HomogeneousIdeal.irrelevant (A.grade V) ≤
      (HomogeneousIdeal.irrelevant (A.sectionGrade V)).map (A.toGrade V) := by
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro n hn x hx
  exact Ideal.mem_map_of_mem (A.toGrade V)
    (HomogeneousIdeal.mem_irrelevant_of_mem _ hn hx)

private lemma fromGrade_irrelevant (V : X.affineOpens) :
    HomogeneousIdeal.irrelevant (A.sectionGrade V) ≤
      (HomogeneousIdeal.irrelevant (A.grade V)).map (A.fromGrade V) := by
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro n hn x hx
  exact Ideal.mem_map_of_mem (A.fromGrade V)
    (HomogeneousIdeal.mem_irrelevant_of_mem _ hn hx)

private noncomputable def gradeIso (V : X.affineOpens) :
    A.localProj V ≅ Proj (A.grade V) where
  hom := Proj.map (A.fromGrade V) (A.fromGrade_irrelevant V)
  inv := Proj.map (A.toGrade V) (A.toGrade_irrelevant V)
  hom_inv_id := by
    rw [← Proj.map_comp]
    exact (Proj.map_congr
      (show (A.fromGrade V).comp (A.toGrade V) = .id _ from
        GradedRingHom.ext fun _ ↦ rfl) _ (by simp)).trans Proj.map_id
  inv_hom_id := by
    rw [← Proj.map_comp]
    exact (Proj.map_congr
      (show (A.toGrade V).comp (A.fromGrade V) = .id _ from
        GradedRingHom.ext fun _ ↦ rfl) _ (by simp)).trans Proj.map_id

private lemma gradeIso_hom_base (V : X.affineOpens) :
    (A.gradeIso V).hom ≫ Proj.toSpecOfAlgebra (A.grade V) ≫ V.2.isoSpec.inv =
      A.localBase V := by
  dsimp only [gradeIso, Proj.toSpecOfAlgebra, localBase]
  rw [← Category.assoc, ← Category.assoc, Proj.map_toSpecZero]
  simp only [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

end AlgebraicGeometry.RelativeProjAlgebra

namespace GradedRingHom

private theorem gradedBaseChange_of_total
    {R S C E : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [CommRing C] [Algebra R C] [CommRing E] [Algebra S E] [Algebra R E]
    [IsScalarTower R S E]
    {𝒞 : ℕ → Submodule R C} [GradedAlgebra 𝒞]
    {ℰ : ℕ → Submodule S E} [GradedAlgebra ℰ]
    (f : 𝒞 →+*ᵍ ℰ) (hf : ∀ r, f (algebraMap R C r) = algebraMap R E r)
    (h : IsBaseChange S (f.toLinearMap' hf)) : f.IsGradedBaseChange := by
  classical
  refine ⟨hf, fun n ↦ ?_⟩
  have hh : IsBaseChange S (DirectSum.lmap fun i ↦ f.degreeLinearMap hf i) := by
    apply (IsBaseChange.iff_of_equiv_comm (DirectSum.decomposeLinearEquiv 𝒞).symm
      (DirectSum.decomposeLinearEquiv ℰ).symm ?_).mpr h
    refine DirectSum.linearMap_ext R fun i ↦ LinearMap.ext fun a ↦ ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      DirectSum.decomposeLinearEquiv_symm_lof, toLinearMap'_apply,
      LinearEquiv.restrictScalars_apply, DirectSum.lmap_lof]
    rw [DirectSum.lof_eq_of, DirectSum.decomposeLinearEquiv_symm_apply,
      DirectSum.decompose_symm_of]
    rfl
  exact AlgebraicGeometry.RelativeProjAlgebra.baseChange_of_directSum _ hh n

end GradedRingHom

namespace AlgebraicGeometry.RelativeProjAlgebra

variable {X : Scheme.{u}} (A : RelativeProjAlgebra X)

/-- Restriction of affine Proj charts is cartesian over the affine inclusion.

Source: Stacks Project, Constructions, Tag 01NO (lemma-proj-inclusion)
(blueprint: lem-nagata-proj-affine-restriction).

Proof: the homogeneous section images are submodules because their inclusions are linear.
Their underlying additive groups give the specified internal grading. Quasi-coherence of
the underlying algebra identifies its affine section restriction with scalar extension.
Decompose source and target into homogeneous components: tensor products commute with
these direct sums, so the bijective total tensor map is bijective in each degree.
Apply base change for affine Proj, and transport the base spectra through the canonical
affine identifications. This does not assume that the degree-zero algebra equals the base.
-/
theorem localTransition_isPullback {V W : X.affineOpens} (h : W ≤ V) :
    IsPullback (A.localTransition h) (A.localBase W) (A.localBase V) (X.homOfLE h) := by
  classical
  let R := Γ(X, V.1)
  let S := Γ(X, W.1)
  let C := A.sections V
  let E := A.sections W
  let f := (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom
  let : Algebra R S := f.toAlgebra
  let : Algebra R E := ((algebraMap S E).comp f).toAlgebra
  let : IsScalarTower R S E := .of_algebraMap_eq' rfl
  let ψ : A.grade V →+*ᵍ A.grade W :=
    { A.restriction h with map_mem := fun ha ↦ A.restriction_mem h _ _ ha }
  have hψ : ∀ r : R, ψ (algebraMap R C r) = algebraMap R E r := by
    intro r
    exact congrArg (fun q ↦ q r)
      (congrArg CommRingCat.Hom.hom (A.algebra.obj.hom.hom.naturality
        (homOfLE (X := X.Opens) h).op)).symm
  have hqc : A.algebra.obj.toModule.IsQuasicoherent := A.algebra.property
  let := hqc
  obtain ⟨c, hc, _, ht⟩ :=
    Scheme.Modules.quasiCoherent_affine_section_baseChange X A.algebra.obj.toModule W V h
  have ht' (a : C) (r : S) : c (a ⊗ₜ[R] r) = r • ψ a := by
    exact ht a r
  let d : S ⊗[R] C →ₗ[S] E :=
    { toFun t := c (TensorProduct.comm R S C t)
      map_add' x y := by simp
      map_smul' s t := by
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul r a =>
            simp only [TensorProduct.smul_tmul', smul_eq_mul,
              TensorProduct.comm_tmul, ht', mul_smul, RingHom.id_apply]
        | add x y hx hy => simp_all }
  have hd : Function.Bijective d := hc.comp (TensorProduct.comm R S C).bijective
  have hb : IsBaseChange S (ψ.toLinearMap' hψ) := by
    apply IsBaseChange.of_equiv (LinearEquiv.ofBijective d hd)
    intro a
    change c (TensorProduct.comm R S C (1 ⊗ₜ[R] a)) = ψ a
    rw [TensorProduct.comm_tmul]
    simpa only [one_smul] using ht' a 1
  have hg := GradedRingHom.gradedBaseChange_of_total ψ hψ hb
  have hp := Proj.isPullback_map_of_isGradedBaseChange ψ hg
  have w : Spec.map (CommRingCat.ofHom f) ≫ V.2.isoSpec.inv =
      W.2.isoSpec.inv ≫ X.homOfLE h := by
    exact specMap_res_isoSpec_inv h
  have hn : (A.gradeIso W).hom ≫ Proj.map ψ hg.irrelevant_le =
      A.localTransition h ≫ (A.gradeIso V).hom := by
    dsimp only [gradeIso, localTransition]
    rw [← Proj.map_comp, ← Proj.map_comp]
    apply Proj.map_congr
    exact GradedRingHom.ext fun _ ↦ rfl
  refine (hp.paste_vert (IsPullback.of_vert_isIso ⟨w⟩)).of_iso
    (A.gradeIso W).symm (A.gradeIso V).symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · apply (cancel_epi (A.gradeIso W).hom).mp
    simp only [Iso.symm_hom, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [hn]
    simp
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    rw [← A.gradeIso_hom_base W]
    simp
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    rw [← A.gradeIso_hom_base V]
    simp
  · simp

/-- Identity restriction induces the identity on Proj.
Source: Stacks Project, Constructions, Tag 01NP
(blueprint: lem-nagata-proj-affine-restriction). -/
theorem localTransition_id (V : X.affineOpens) : A.localTransition (le_refl V) = 𝟙 _ := by
  have h : A.restriction (le_refl V) = .id (A.sectionGrade V) := by
    apply GradedRingHom.ext
    intro a
    change A.algebra.obj.right.obj.map (𝟙 (op V.1)) a = a
    simp
  exact (Proj.map_congr h _ (by simp)).trans Proj.map_id

/-- Restriction maps on Proj compose.
Source: Stacks Project, Constructions, Tag 01NP
(blueprint: lem-nagata-proj-affine-restriction). -/
theorem localTransition_comp {U V W : X.affineOpens} (h : U ≤ V) (k : V ≤ W) :
    A.localTransition (h.trans k) = A.localTransition h ≫ A.localTransition k := by
  have hh : A.restriction (h.trans k) = (A.restriction h).comp (A.restriction k) := by
    apply GradedRingHom.ext
    intro a
    exact congrArg (fun q ↦ q a)
      (A.algebra.obj.right.obj.map_comp
        (homOfLE (X := X.Opens) k).op (homOfLE (X := X.Opens) h).op)
  exact (Proj.map_congr hh _
    (HomogeneousIdeal.irrelevant_le_map_comp (A.irrelevant_le k)
      (A.irrelevant_le h))).trans (Proj.map_comp _ _ _ _)

end AlgebraicGeometry.RelativeProjAlgebra
