/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalData
import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.RingTheory.MvPolynomial.Ideal
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSectionChart
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartPolynomial
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Canonical

/-! # The coordinate hyperplane of projective space

Source: Stacks Project, Constructions, Tags 01NG and 01MS.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

/-- The coordinate-hyperplane identification needed by coordinate geometry.
Source: Stacks Project, Constructions, Tags 01NG and 01MS.
(blueprint: lem-pur-projective-bundle-coordinate-subschemes). -/
structure ProjectiveBundleCoordinateSubschemes (K : Type u) [Field K] (n : ℕ) where
  hyperplane : ∀ _hn : 1 ≤ n,
    (Scheme.Modules.Hom.zeroLocus (ProjectiveSpace.coordinateSection
      (ULift.{u} (Fin (n + 1))) (Spec (.of K)) ⟨0⟩)).subscheme ≅
        RelativeProjectiveSpace.scheme (Spec (.of K)) (n - 1)
  hyperplane_over : ∀ hn : 1 ≤ n,
    (hyperplane hn).hom ≫ RelativeProjectiveSpace.π (Spec (.of K)) (n - 1) =
      (Scheme.Modules.Hom.zeroLocus (ProjectiveSpace.coordinateSection
        (ULift.{u} (Fin (n + 1))) (Spec (.of K)) ⟨0⟩)).subschemeι ≫
          (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of K)) ↘ Spec (.of K))
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
private def coordinateDrop {I R : Type u} [CommRing R] (i : I) :
    MvPolynomial I R →+* MvPolynomial {j : I // j ≠ i} R := by
  classical
  exact MvPolynomial.eval₂Hom MvPolynomial.C
    (fun j ↦ if h : j = i then 0 else MvPolynomial.X ⟨j, h⟩)
private lemma coordinateDrop_X {I R : Type u} [CommRing R] (i : I)
    (j : {j : I // j ≠ i}) :
    coordinateDrop (R := R) i (MvPolynomial.X j.val) = MvPolynomial.X j := by
  classical
  simp [coordinateDrop, j.property]
private lemma coordinateDrop_X_self {I R : Type u} [CommRing R] (i : I) :
    coordinateDrop (R := R) i (MvPolynomial.X i) = 0 := by
  classical
  simp [coordinateDrop]
private lemma coordinateDrop_rename {I R : Type u} [CommRing R] (i : I)
    (p : MvPolynomial {j : I // j ≠ i} R) :
    coordinateDrop i (MvPolynomial.rename Subtype.val p) = p := by
  have h : (coordinateDrop (R := R) i).comp (MvPolynomial.rename Subtype.val).toRingHom =
      RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [coordinateDrop]
    · intro j
      simp [coordinateDrop_X]
  exact RingHom.congr_fun h p
private lemma coordinateDrop_ker {I R : Type u} [CommRing R] (i : I) :
    RingHom.ker (coordinateDrop (R := R) i) = Ideal.span {MvPolynomial.X i} := by
  classical
  let J : Ideal (MvPolynomial I R) := Ideal.span {MvPolynomial.X i}
  let q := Ideal.Quotient.mk J
  have hqi : q (MvPolynomial.X i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hcomp : (q.comp (MvPolynomial.rename Subtype.val).toRingHom).comp
      (coordinateDrop i) = q := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [coordinateDrop]
    · intro j
      by_cases h : j = i
      · subst j
        simp [coordinateDrop, hqi]
      · simp [coordinateDrop, h]
  apply le_antisymm
  · intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← RingHom.congr_fun hcomp p]
    change q (MvPolynomial.rename Subtype.val (coordinateDrop i p)) = 0
    rw [RingHom.mem_ker.mp hp, map_zero, map_zero]
  · apply Ideal.span_le.mpr
    rintro _ rfl
    exact coordinateDrop_X_self i
private theorem coordinateDrop_homogeneous {I R : Type u} [CommRing R] (i : I)
    {d : ℕ} {p : MvPolynomial I R} (hp : p.IsHomogeneous d) :
    (coordinateDrop i p).IsHomogeneous d := by
  classical
  let v : I → MvPolynomial {j : I // j ≠ i} R :=
    fun j ↦ if h : j = i then 0 else MvPolynomial.X ⟨j, h⟩
  have hv (j : I) : (v j).IsHomogeneous 1 := by
    dsimp only [v]
    split
    · exact MvPolynomial.isHomogeneous_zero _ _ _
    · exact MvPolynomial.isHomogeneous_X _ _
  change (MvPolynomial.eval₂ MvPolynomial.C v p).IsHomogeneous d
  simpa only [one_mul] using
    hp.eval₂ MvPolynomial.C v (fun r ↦ MvPolynomial.isHomogeneous_C _ r) hv
private def coordinateDropGraded {I R : Type u} [CommRing R] (i : I) :
    MvPolynomial.homogeneousSubmodule I R →+*ᵍ
      MvPolynomial.homogeneousSubmodule {j : I // j ≠ i} R where
  toRingHom := coordinateDrop (R := R) i
  map_mem := coordinateDrop_homogeneous i
private lemma coordinateDropGraded_surjective {I R : Type u} [CommRing R] (i : I) :
    Function.Surjective (coordinateDropGraded (R := R) i) := by
  intro p
  exact ⟨MvPolynomial.rename Subtype.val p, coordinateDrop_rename i p⟩
private lemma coordinateDropGraded_irrelevant {I R : Type u} [CommRing R] (i : I) :
    HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule {j : I // j ≠ i} R) ≤
      (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule I R)).map
        (coordinateDropGraded i) :=
  GradedRingHom.irrelevant_le_map_of_surjective (coordinateDropGraded_surjective i)
private lemma coordinateDropGraded_range {I R : Type u} [CommRing R] (i : I) :
    Set.range (Proj.map (coordinateDropGraded (R := R) i)
      (coordinateDropGraded_irrelevant i)) =
        {x | MvPolynomial.X i ∈ x.asHomogeneousIdeal} := by
  classical
  let f := coordinateDropGraded (R := R) i
  have hf : Function.Surjective f := coordinateDropGraded_surjective i
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change f (MvPolynomial.X i) ∈ y.asHomogeneousIdeal
    change coordinateDrop i (MvPolynomial.X i) ∈ y.asHomogeneousIdeal
    rw [coordinateDrop_X_self]
    exact y.asHomogeneousIdeal.zero_mem
  · intro hx
    have hk : RingHom.ker f ≤ x.asHomogeneousIdeal.toIdeal := by
      change RingHom.ker (coordinateDrop i) ≤ _
      rw [coordinateDrop_ker]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
    let J := x.asHomogeneousIdeal.map f
    have hc : J.toIdeal.comap f = x.asHomogeneousIdeal.toIdeal := by
      change (x.asHomogeneousIdeal.toIdeal.map f).comap f = _
      rw [Ideal.comap_map_of_surjective f hf,
        show Ideal.comap f ⊥ = RingHom.ker f from rfl, sup_eq_left.mpr hk]
    have hp : J.toIdeal.IsPrime := by
      have : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
      exact Ideal.map_isPrime_of_surjective hf hk
    have hirr : ¬ HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule {j : I // j ≠ i} R) ≤ J := by
      intro h
      apply x.not_irrelevant_le
      change (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule I R)).toIdeal ≤ x.asHomogeneousIdeal.toIdeal
      rw [MvPolynomial.toIdeal_irrelevant_homogeneousSubmodule]
      apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      rw [← hc]
      change f (MvPolynomial.X j) ∈ J
      by_cases hij : j = i
      · subst j
        change coordinateDrop i (MvPolynomial.X i) ∈ J
        rw [coordinateDrop_X_self]
        exact J.zero_mem
      · apply h
        change coordinateDrop i (MvPolynomial.X j) ∈ _
        rw [coordinateDrop_X i ⟨j, hij⟩]
        exact HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.zero_lt_one
          (MvPolynomial.isHomogeneous_X _ _)
    let y : Proj (MvPolynomial.homogeneousSubmodule {j : I // j ≠ i} R) :=
      ⟨J, hp, hirr⟩
    refine ⟨y, ?_⟩
    apply ProjectiveSpectrum.ext
    exact HomogeneousIdeal.ext hc
private def integralDrop (I : Type u) (i : I) :
    Proj.projectiveSpaceOverAffine {j : I // j ≠ i} (ULift.{u} ℤ) ⟶
      Proj.projectiveSpaceOverAffine I (ULift.{u} ℤ) :=
  Proj.map (coordinateDropGraded i) (coordinateDropGraded_irrelevant i)
private instance integralDrop_closed (I : Type u) (i : I) :
    IsClosedImmersion (integralDrop I i) :=
  Proj.isClosedImmersion_map _ _ (coordinateDropGraded_surjective i)
private def coordinateEmbedding (I : Type u) (S : Scheme.{u}) (i : I) :
    ℙ({j : I // j ≠ i}; S) ⟶ ℙ(I; S) :=
  pullback.map _ _ _ _ (𝟙 S)
    (integralDrop I i) (𝟙 _) (by simp) (terminal.hom_ext _ _)
private instance embedding_closed (I : Type u) (S : Scheme.{u}) (i : I) :
    IsClosedImmersion (coordinateEmbedding I S i) := by
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstance : IsClosedImmersion (𝟙 S))
    (integralDrop_closed I i) (by simp) (terminal.hom_ext _ _)
private theorem embedding_over (I : Type u) (S : Scheme.{u}) (i : I) :
    coordinateEmbedding I S i ≫ (ℙ(I; S) ↘ S) = (ℙ({j : I // j ≠ i}; S) ↘ S) := by
  change coordinateEmbedding I S i ≫ pullback.fst _ _ = pullback.fst _ _
  simp [coordinateEmbedding]
private theorem embedding_range (I : Type u) (S : Scheme.{u}) (i : I) :
    Set.range (coordinateEmbedding I S i) =
      ((ProjectiveSpace.coordinateSection I S i).zeroLocus.support : Set ℙ(I; S)) := by
  have hr := Scheme.Pullback.range_map
    (f := terminal.from S)
    (g := terminal.from (Proj.projectiveSpaceOverAffine {j : I // j ≠ i} (ULift.{u} ℤ)))
    (terminal.from S) (terminal.from (Proj.projectiveSpaceOverAffine I (ULift.{u} ℤ)))
    (𝟙 S) (integralDrop I i) (𝟙 _) (by simp) (terminal.hom_ext _ _)
  have hr' : Set.range (coordinateEmbedding I S i) =
      (ProjectiveSpace.toProjInt I S) ⁻¹' Set.range (integralDrop I i) := by
    dsimp only [ProjectiveSpace]
    simpa only [coordinateEmbedding, ProjectiveSpace.toProjInt, Scheme.Hom.id_base,
      TopCat.hom_id, ContinuousMap.coe_id,
      Set.range_id, Set.preimage_univ, Set.univ_inter] using hr
  rw [hr', show Set.range (integralDrop I i) =
    {x | MvPolynomial.X i ∈ x.asHomogeneousIdeal} from coordinateDropGraded_range i]
  have hc := ProjectiveSpace.compl_support_zeroLocus_coordinateSection I S i
  have hc' := congrArg (fun W : (ℙ(I; S)).Opens ↦ (W : Set (ℙ(I; S)))) hc
  apply compl_injective
  exact hc'.symm
private theorem projectiveReduced (I K : Type u) [Field K] :
    IsReduced (ℙ(I; Spec (.of K))) := by
  let C := Scheme.openCoverOfIsOpenCover _
    (ProjectiveSpace.standardOpen I (Spec (.of K)))
    (ProjectiveSpace.iSup_standardOpen I (Spec (.of K)))
  let (j : C.I₀) : IsReduced (C.X j) := by
    let e := ProjectiveSpace.standardOpenIso I (Spec (.of K)) j ≪≫
      (AffineSpace.SpecIso {k : I // k ≠ j} (.of K))
    exact isReduced_of_isOpenImmersion e.hom
  exact IsReduced.of_openCover _ C
private theorem coordinateRadical (I K : Type u) [Field K] (i : I) :
    (ProjectiveSpace.coordinateSection I (Spec (.of K)) i).zeroLocus.radical =
      (ProjectiveSpace.coordinateSection I (Spec (.of K)) i).zeroLocus := by
  classical
  let S := Spec (.of K)
  let U : I → (ℙ(I; S)).affineOpens := fun j ↦
    ⟨ProjectiveSpace.standardOpen I S j, ProjectiveSpace.isAffineOpen_standardOpen I S j⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U (ProjectiveSpace.iSup_standardOpen I S)
  intro j
  rw [Scheme.IdealSheafData.radical_ideal]
  have : SheafOfModules.IsInvertible.{u, u, u} (𝟙_ (ℙ(I; S)).Modules) :=
    Scheme.Modules.IsInvertible.sheafOfModules_isInvertible (𝟙_ (ℙ(I; S)).Modules)
  have hid : (ProjectiveSpace.coordinateSection I S i).zeroLocus.ideal (U j) =
      Ideal.span {ProjectiveSpace.coordRatio I S j i} :=
    Scheme.Modules.Hom.ideal_zeroLocus (ProjectiveSpace.coordinateSection I S i) (U j)
      (Scheme.Modules.isFreeGenerator_one (X := ℙ(I; S)) (U j).1)
      (ProjectiveSpace.isFreeGenerator_twistGenerator I S 1 j)
      (ProjectiveSpace.coordinateSection_app_standardOpen I S i j)
  rw [hid]
  by_cases hij : i = j
  · subst i
    simp [ProjectiveSpace.coordRatio_self]
  · have hp : (Ideal.span {MvPolynomial.X (R := K) (⟨i, hij⟩ : {k : I // k ≠ j})}).IsPrime := by
      rw [← coordinateDrop_ker]
      exact RingHom.ker_isPrime _
    have hm := Ideal.map_isPrime_of_surjective
      (f := (ProjectiveSpace.chartRingEquiv I K j).toRingHom)
      (ProjectiveSpace.chartRingEquiv I K j).surjective
      (I := Ideal.span {MvPolynomial.X (R := K) (⟨i, hij⟩ : {k : I // k ≠ j})})
      (by simp)
    rw [Ideal.map_span, Set.image_singleton] at hm
    change (Ideal.span {(ProjectiveSpace.chartRingEquiv I K j)
      (MvPolynomial.X ⟨i, hij⟩)}).IsPrime at hm
    rw [ProjectiveSpace.chartRingEquiv_X] at hm
    exact hm.isRadical.radical
private theorem hyperplaneIso (I K : Type u) [Field K] (i : I) :
    ∃ e : (ProjectiveSpace.coordinateSection I (Spec (.of K)) i).zeroLocus.subscheme ≅
        ℙ({j : I // j ≠ i}; Spec (.of K)),
      e.hom ≫ coordinateEmbedding I (Spec (.of K)) i =
        (ProjectiveSpace.coordinateSection I (Spec (.of K)) i).zeroLocus.subschemeι := by
  let Z := (ProjectiveSpace.coordinateSection I (Spec (.of K)) i).zeroLocus
  let f := coordinateEmbedding I (Spec (.of K)) i
  have : IsReduced (ℙ({j : I // j ≠ i}; Spec (.of K))) := projectiveReduced _ K
  have hk : f.ker = Z := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal]
    have hc : (⟨closure (Set.range f), isClosed_closure⟩ :
        TopologicalSpace.Closeds (ℙ(I; Spec (.of K)))) = Z.support := by
      apply SetLike.coe_injective
      change closure (Set.range f) = _
      rw [show Set.range f = Z.support from embedding_range I (Spec (.of K)) i,
        Z.support.isClosed.closure_eq]
    rw [hc, Scheme.IdealSheafData.vanishingIdeal_support]
    exact coordinateRadical I K i
  have hh : f.ker = Z.subschemeι.ker := hk.trans Z.ker_subschemeι.symm
  let a := IsClosedImmersion.lift f Z.subschemeι hh.le
  have : IsIso a := IsClosedImmersion.isIso_lift f Z.subschemeι hh
  exact ⟨asIso a, IsClosedImmersion.lift_fac f Z.subschemeι hh.le⟩
private def renameGraded {I J R : Type u} [CommRing R] (e : I ≃ J) :
    MvPolynomial.homogeneousSubmodule I R →+*ᵍ
      MvPolynomial.homogeneousSubmodule J R where
  toRingHom := (MvPolynomial.rename e).toRingHom
  map_mem := fun h ↦ h.rename_isHomogeneous
private lemma renameGraded_surjective {I J R : Type u} [CommRing R] (e : I ≃ J) :
    Function.Surjective (renameGraded (R := R) e) :=
  (MvPolynomial.renameEquiv R e).surjective
private def renameProj {I J : Type u} (e : I ≃ J) :
    Proj.projectiveSpaceOverAffine J (ULift.{u} ℤ) ⟶
      Proj.projectiveSpaceOverAffine I (ULift.{u} ℤ) :=
  Proj.map (renameGraded e)
    (GradedRingHom.irrelevant_le_map_of_surjective (renameGraded_surjective e))
private lemma renameGraded_comp {I J R : Type u} [CommRing R] (e : I ≃ J) :
    (renameGraded (R := R) e.symm).comp (renameGraded e) =
      GradedRingHom.id (MvPolynomial.homogeneousSubmodule I R) := by
  apply GradedRingHom.ext
  intro p
  exact (MvPolynomial.renameEquiv R e).symm_apply_apply p
private instance renameProj_isIso {I J : Type u} (e : I ≃ J) :
    IsIso (renameProj e) := by
  refine ⟨⟨renameProj e.symm, ?_, ?_⟩⟩
  · change Proj.map _ _ ≫ Proj.map _ _ =
      𝟙 (Proj (MvPolynomial.homogeneousSubmodule J (ULift.{u} ℤ)))
    rw [← Proj.map_comp]
    exact (Proj.map_congr (renameGraded_comp e.symm) _ _).trans Proj.map_id
  · change Proj.map _ _ ≫ Proj.map _ _ =
      𝟙 (Proj (MvPolynomial.homogeneousSubmodule I (ULift.{u} ℤ)))
    rw [← Proj.map_comp]
    exact (Proj.map_congr (renameGraded_comp e) _ _).trans Proj.map_id
private def renameSpace {I J : Type u} (S : Scheme.{u}) (e : I ≃ J) :
    ℙ(J; S) ⟶ ℙ(I; S) :=
  pullback.map _ _ _ _ (𝟙 S) (renameProj e) (𝟙 _)
    (by simp) (terminal.hom_ext _ _)
private instance renameSpace_isIso {I J : Type u} (S : Scheme.{u}) (e : I ≃ J) :
    IsIso (renameSpace S e) := by
  unfold renameSpace
  infer_instance
private lemma renameSpace_over {I J : Type u} (S : Scheme.{u}) (e : I ≃ J) :
    renameSpace S e ≫ (ℙ(I; S) ↘ S) = (ℙ(J; S) ↘ S) := by
  change renameSpace S e ≫ pullback.fst _ _ = pullback.fst _ _
  simp [renameSpace]
private theorem relativePolynomialChart (S : Scheme.{u}) (n : ℕ) :
    ∃ e : RelativeProjectiveSpace.scheme S n ≅ ℙ(ULift.{u} (Fin (n + 1)); S),
      e.hom ≫ (ℙ(ULift.{u} (Fin (n + 1)); S) ↘ S) =
        RelativeProjectiveSpace.π S n := by
  let F := RelativeProjectiveSpace.freeModule S n
  have : F.IsQuasicoherent := by
    dsimp only [F, RelativeProjectiveSpace.freeModule]
    infer_instance
  obtain ⟨D, _, _, _, _, _, _, hfree⟩ :=
    ProjectiveBundleQuotientGeometry.projective_bundle_quotient_geometry S F
  obtain ⟨er, es, _, hr, hs, _, _⟩ := hfree n (Iso.refl F)
  refine ⟨er.symm ≪≫ es, ?_⟩
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, hs, ← hr, Iso.inv_hom_id_assoc]
private theorem hyperplaneRelative (K : Type u) [Field K] (n : ℕ) (hn : 1 ≤ n) :
    ∃ e : (ProjectiveSpace.coordinateSection
        (ULift.{u} (Fin (n + 1))) (Spec (.of K)) ⟨0⟩).zeroLocus.subscheme ≅
          RelativeProjectiveSpace.scheme (Spec (.of K)) (n - 1),
      e.hom ≫ RelativeProjectiveSpace.π (Spec (.of K)) (n - 1) =
        (ProjectiveSpace.coordinateSection
          (ULift.{u} (Fin (n + 1))) (Spec (.of K)) ⟨0⟩).zeroLocus.subschemeι ≫
          (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of K)) ↘ Spec (.of K)) := by
  classical
  let I := ULift.{u} (Fin (n + 1))
  let J := {j : I // j ≠ ⟨0⟩}
  let eJ : J ≃ ULift.{u} (Fin (n - 1 + 1)) :=
    (Equiv.subtypeEquiv Equiv.ulift (by
      intro i
      exact not_congr (show i = ULift.up 0 ↔ i.down = 0 from ULift.ext_iff))).trans
      ((finSuccAboveEquiv (0 : Fin (n + 1))).symm.trans
        ((finCongr (by omega)).trans Equiv.ulift.symm))
  obtain ⟨e, he⟩ := hyperplaneIso I K ⟨0⟩
  obtain ⟨t, ht⟩ := relativePolynomialChart (Spec (.of K)) (n - 1)
  let r := asIso (renameSpace (Spec (.of K)) eJ.symm)
  refine ⟨e ≪≫ r ≪≫ t.symm, ?_⟩
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [← ht]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change e.hom ≫ renameSpace (Spec (.of K)) eJ.symm ≫ _ = _
  rw [renameSpace_over, ← embedding_over I (Spec (.of K)) ⟨0⟩,
    ← Category.assoc, he]
end

/-- The coordinate hyperplane is projective space of one lower dimension.
Source: Stacks Project, Constructions, Tags 01NG and 01MS;
parent proof step 10.
(blueprint: lem-pur-projective-bundle-coordinate-subschemes).

Proof: quotient the homogeneous coordinate ring by T_0. The resulting graded
surjection induces a closed immersion from projective space on the remaining
n coordinates. On every nonzero chart j, the kernel of the ring map is generated
by T_0/T_j: polynomial expansion separates the constant term from multiples of
that variable. The zeroth chart is empty. Thus the closed image is exactly the
zero subscheme of T_0, and the maps commute with the structure map to Spec K.
For n=0 the hyperplane assertion has the impossible hypothesis 1 ≤ 0, so the
record has no data to construct. For n≥1 the indexing of the remaining variables
is Fin n, and relative projective (n-1)-space has n coordinates since n-1+1=n. -/
theorem exists_projectiveBundleCoordinateSubschemes (K : Type u) [Field K] (n : ℕ) :
    Nonempty (ProjectiveBundleCoordinateSubschemes K n) := by
  classical
  choose e he using hyperplaneRelative K n
  exact ⟨⟨e, he⟩⟩

end AlgebraicGeometry
