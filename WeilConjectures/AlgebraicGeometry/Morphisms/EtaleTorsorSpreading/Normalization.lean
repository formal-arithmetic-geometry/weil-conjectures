/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading.Datum
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization

/-!
# The normalization of `C` in the Galois cover over the generic fibre

In the situation of the spreading theorem (blueprint `sbc-thm-spreading-finite-etale-galois`),
the relative normalization of `C` in `ν : Z.P ⟶ C_η ⟶ C` restricts to `Z.P` over the generic
fibre `C_η`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.SpreadingDatum

variable {G : Type (u + 1)} [Group G] [Finite G] (D : SpreadingDatum G)

set_option backward.isDefEq.respectTransparency false in
/-- Over affine opens `W ⊆ S` and `U ⊆ c⁻¹ W`, the sections of the generic fibre over `j⁻¹ U`
are the localization of `Γ(C, U)` at the nonzero elements of `Γ(S, W)`: the square of sections
is a pushout, and `Γ(Spec K, ⊤)` is the fraction field of `Γ(S, W)`. -/
lemma isLocalization_appLE_j {W : D.S.Opens} (hW : IsAffineOpen W) [Nonempty W]
    {U : D.C.Opens} (hU : IsAffineOpen U) (hUW : U ≤ D.c ⁻¹ᵁ W) :
    letI := (D.c.appLE W U hUW).hom.toAlgebra
    letI := (D.j.appLE U (D.j ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid Γ(D.C, U) (nonZeroDivisors Γ(D.S, W)))
      Γ(D.Cη, D.j ⁻¹ᵁ U) := by
  have hK := top_le_preimage_fromSpecFunctionField W
  have hY : D.j ⁻¹ᵁ U = D.q ⁻¹ᵁ ⊤ ⊓ D.j ⁻¹ᵁ U := by simp
  have := isIso_pushoutSection_of_isAffineOpen D.isPullback hUW hK hY hW hU (isAffineOpen_top _)
  have hP := (isIso_pushoutSection_iff _ _ _ _).mp this
  have hloc := isLocalization_fromSpecFunctionField_appLE hW hK
  algebraize [(D.S.fromSpecFunctionField.appLE W ⊤ hK).hom, (D.c.appLE W U hUW).hom,
    (D.j.appLE U (D.j ⁻¹ᵁ U) le_rfl).hom,
    (D.q.appLE ⊤ (D.j ⁻¹ᵁ U) (le_top.trans D.q.preimage_top.ge)).hom,
    (D.c.appLE W U hUW ≫ D.j.appLE U (D.j ⁻¹ᵁ U) le_rfl).hom]
  have : IsScalarTower Γ(D.S, W) Γ(D.C, U) Γ(D.Cη, D.j ⁻¹ᵁ U) := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(D.S, W) Γ(Spec D.S.functionField, ⊤) Γ(D.Cη, D.j ⁻¹ᵁ U) :=
    .of_algebraMap_eq' congr(($(hP.w)).hom).symm
  have : Algebra.IsPushout Γ(D.S, W) Γ(Spec D.S.functionField, ⊤) Γ(D.C, U)
      Γ(D.Cη, D.j ⁻¹ᵁ U) := CommRingCat.isPushout_iff_isPushout.mp hP
  exact (Algebra.isLocalization_iff_isPushout (nonZeroDivisors Γ(D.S, W))
    Γ(Spec D.S.functionField, ⊤)).mpr this.symm

/-- The preimage under `j : C_η ⟶ C` of an affine open `U ⊆ c⁻¹ W`, with `W ⊆ S` affine, is
affine: it is `U ×_W Spec K`. -/
lemma isAffineOpen_preimage_j {W : D.S.Opens} (hW : IsAffineOpen W) [Nonempty W]
    {U : D.C.Opens} (hU : IsAffineOpen U) (hUW : U ≤ D.c ⁻¹ᵁ W) :
    IsAffineOpen (D.j ⁻¹ᵁ U) := by
  have hY : D.j ⁻¹ᵁ U = D.q ⁻¹ᵁ ⊤ ⊓ D.j ⁻¹ᵁ U := by simp
  have : IsAffine _ := hW
  have : IsAffine _ := hU
  have : IsAffine _ := isAffineOpen_top (Spec D.S.functionField)
  exact .of_isIso (Scheme.Hom.isPullback_resLE D.isPullback hUW
    (top_le_preimage_fromSpecFunctionField W) hY).isoPullback.hom

/-- Every point of `C` lies in an affine open `U ⊆ c⁻¹ W` with `W ⊆ S` a nonempty affine open. -/
lemma exists_affineOpens (x : D.C) : ∃ (W : D.S.Opens) (_ : IsAffineOpen W) (U : D.C.Opens)
    (_ : IsAffineOpen U) (_ : U ≤ D.c ⁻¹ᵁ W), x ∈ U ∧ Nonempty W := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := D.S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (D.c x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := D.C.isBasis_affineOpens.exists_subset_of_mem_open
    (a := x) hxW (D.c ⁻¹ᵁ W).2
  exact ⟨W, hW, U, hU, hUW, hxU, ⟨⟨_, hxW⟩⟩⟩

instance : IsAffineHom D.j := by
  refine isAffineHom_of_forall_exists_isAffineOpen _ fun x ↦ ?_
  obtain ⟨W, hW, U, hU, hUW, hxU, hne⟩ := D.exists_affineOpens x
  exact ⟨U, hxU, hU, D.isAffineOpen_preimage_j hW hU hUW⟩

instance : IsPreimmersion D.j := MorphismProperty.of_isPullback D.isPullback inferInstance

/-- The relative normalization of `C` in `ν : Z.P ⟶ C` commutes with the base change along
`j : C_η ⟶ C`: integral closure commutes with localization. -/
lemma isIso_normalizationPullback_ν : IsIso (D.ν.normalizationPullback D.j) := by
  refine Scheme.Hom.isIso_normalizationPullback_of_isAffineHom _ _ fun y ↦ ?_
  obtain ⟨W, hW, U, hU, hUW, hyU, hne⟩ := D.exists_affineOpens (D.j y)
  refine ⟨U, hU, D.j ⁻¹ᵁ U, D.isAffineOpen_preimage_j hW hU hUW, le_rfl, hyU, ?_⟩
  let := (D.c.appLE W U hUW).hom.toAlgebra
  let := (D.j.appLE U (D.j ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  let := (D.ν.app U).hom.toAlgebra
  have := D.isLocalization_appLE_j hW hU hUW
  exact TensorProduct.toIntegralClosure_bijective_of_isLocalization
    (Algebra.algebraMapSubmonoid Γ(D.C, U) (nonZeroDivisors Γ(D.S, W)))

/-- Step of the proof of blueprint `sbc-thm-spreading-finite-etale-galois`: the relative
normalization `N ⟶ C` of `C` in `ν : Z.P ⟶ C` restricts to `Z.P ⟶ C_η` over the generic fibre,
that is, the square formed by `ν.toNormalization`, `Z.π`, `ν.fromNormalization` and `j` is
cartesian.

Proof sketch: relative normalization commutes with localization (as in the proof of
[Stacks 03GV] for smooth base change, `AlgebraicGeometry.Scheme.Hom.normalizationPullback`, with
`TensorProduct.toIntegralClosure_bijective_of_smooth` replaced by the fact that integral closure
commutes with localization). Over affine opens `Spec A ⊆ S` and `Spec B ⊆ c⁻¹(Spec A)`, the
generic fibre is `Spec (B ⊗_A K) = Spec (B_{A∖0})`, `Z.P` is `Spec D` for a finite étale
`B_{A∖0}`-algebra `D`, and the normalization is `Spec B'` with `B'` the integral closure of `B`
in `D`. Then `B' ⊗_B B_{A∖0} = B'_{A∖0}` is the integral closure of `B_{A∖0}` in `D`, which is
`D` since `D` is integral over `B_{A∖0}`. Finally `j` is a monomorphism, so
`Z.P ×_C C_η = Z.P`. -/
theorem isPullback_toNormalization :
    IsPullback D.ν.toNormalization D.Z.π D.ν.fromNormalization D.j := by
  have := D.isIso_normalizationPullback_ν
  let e : D.Z.P ⟶ pullback D.ν D.j := pullback.lift (𝟙 _) D.Z.π (by simp [ν])
  have : IsIso e := ⟨⟨pullback.fst _ _, by simp [e], by
    apply pullback.hom_ext
    · simp [e]
    · rw [← cancel_mono D.j]
      simp [e, ← pullback.condition, ν]⟩⟩
  have : IsIntegralHom (pullback.snd D.ν D.j) := by
    have : pullback.snd D.ν D.j = inv e ≫ D.Z.π := by
      rw [IsIso.eq_inv_comp]; simp [e]
    rw [this]; infer_instance
  refine IsPullback.of_iso_pullback ⟨by simp [ν]⟩
    (asIso (e ≫ (pullback.snd D.ν D.j).toNormalization ≫ D.ν.normalizationPullback D.j))
    ?_ ?_
  · simp only [e, asIso_hom, Category.assoc, Hom.toNormalization_normalizationPullback_fst]
    simp only [pullback.lift_fst_assoc]
    exact Category.id_comp _
  · simp [e]

/-- If the normalization `N ⟶ C` of `C` in the Galois cover is étale over every point of `S`,
it is étale. -/
theorem etale_fromNormalization_of_forall_etaleOver (h : ∀ s, D.EtaleOver s) :
    Etale D.ν.fromNormalization := by
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Etale)
    (fun U : {U : D.ν.normalization.Opens // Etale (U.ι ≫ D.ν.fromNormalization)} ↦ U.1)
    (top_unique fun x _ ↦ ?_) fun U ↦ U.2
  obtain ⟨U, hxU, hU⟩ := h _ x rfl
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU⟩, hxU⟩

/-- If the normalization `N ⟶ C` of `C` in the Galois cover is étale over every point of `S`,
then the Galois cover `Z.P` of the generic fibre extends to a finite étale `C`-scheme, namely
`N`. -/
theorem exists_isFinite_etale_isPullback_of_forall_etaleOver (h : ∀ s, D.EtaleOver s) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ D.C) (_ : IsFinite p) (_ : Etale p) (ψ : D.Z.P ⟶ Y),
      IsPullback ψ D.Z.π p D.j := by
  have := D.etale_fromNormalization_of_forall_etaleOver h
  refine ⟨_, D.ν.fromNormalization, ?_, this, _, D.isPullback_toNormalization⟩
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).2 ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme.SpreadingDatum
