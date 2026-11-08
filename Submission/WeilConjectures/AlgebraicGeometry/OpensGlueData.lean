/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Gluing schemes along open subschemes

A family of schemes `U i`, opens `V i j ⊆ U i` with `V i i = ⊤`, and morphisms
`t i j : V i j ⟶ V j i` with `t i i = 𝟙`, mapping `V i j ⊓ V i k` into `V j k` and satisfying
the triple cocycle condition `t j k ∘ t i j = t i k` on `V i j ⊓ V i k`, glue to a scheme.
This is the form of the gluing theorem in which the overlaps are recorded as opens of the
charts, rather than as abstract schemes with open immersions as in `Scheme.GlueData`.

## Main definitions

- `AlgebraicGeometry.Scheme.OpensGlueData`: the gluing data.
- `AlgebraicGeometry.Scheme.OpensGlueData.toGlueData`: the associated `Scheme.GlueData`.
- `AlgebraicGeometry.Scheme.OpensGlueData.glued`, `AlgebraicGeometry.Scheme.OpensGlueData.ι`:
  the glued scheme and the open immersions of the charts.
- `AlgebraicGeometry.Scheme.OpensGlueData.glueMorphisms`: morphisms out of the glued scheme
  are glued from morphisms out of the charts which are compatible on the overlaps.

## Main results

- `AlgebraicGeometry.Scheme.OpensGlueData.isPullback`: the overlaps are the fibre products of
  the charts over the glued scheme.
- `AlgebraicGeometry.Scheme.OpensGlueData.preimage_opensRange_ι`: `ι i ⁻¹ (range ι j) = V i j`.
- `AlgebraicGeometry.Scheme.OpensGlueData.compactSpace_glued`: finitely many quasi-compact charts
  glue to a quasi-compact scheme.

This is the affine gluing theorem used in the blueprint proofs of
`lemma-nagata-finite-presentation-descends` and `def-nagata-noetherian-stage`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Gluing data for schemes in which the overlaps are given as opens of the charts. -/
structure OpensGlueData where
  /-- The index type of the charts. -/
  J : Type u
  /-- The charts. -/
  U : J → Scheme.{u}
  /-- The overlap of the `i`-th chart with the `j`-th chart, as an open of the `i`-th chart. -/
  V : ∀ i, J → (U i).Opens
  V_self : ∀ i, V i i = ⊤
  /-- The transition morphisms. -/
  t : ∀ i j, (V i j).toScheme ⟶ (V j i).toScheme
  t_self : ∀ i, t i i = 𝟙 _
  /-- `t i j` maps `V i j ⊓ V i k` into `V j k`. -/
  t_mem : ∀ i j k (x : V i j), x.1 ∈ V i k → (t i j x).1 ∈ V j k
  /-- The cocycle condition on `V i j ⊓ V i k`. -/
  cocycle : ∀ i j k,
    IsOpenImmersion.lift (V j k).ι
        ((U i).homOfLE (inf_le_left : V i j ⊓ V i k ≤ V i j) ≫ t i j ≫ (V j i).ι) (by
          rintro _ ⟨x, rfl⟩
          rw [Scheme.Opens.range_ι]
          exact t_mem i j k _ (by
            have h := Scheme.homOfLE_apply (X := U i) (inf_le_left : V i j ⊓ V i k ≤ V i j) x
            exact h ▸ x.2.2)) ≫ t j k ≫ (V k j).ι =
      (U i).homOfLE (inf_le_right : V i j ⊓ V i k ≤ V i k) ≫ t i k ≫ (V k i).ι

namespace OpensGlueData

variable (D : OpensGlueData.{u})

/-- (Implementation) `t i j` restricted to `V i j ⊓ V i k`, landing in `V j k ⊓ V j i`. -/
noncomputable def tInf (i j k : D.J) :
    (D.V i j ⊓ D.V i k).toScheme ⟶ (D.V j k ⊓ D.V j i).toScheme :=
  IsOpenImmersion.lift (D.V j k ⊓ D.V j i).ι
    ((D.U i).homOfLE inf_le_left ≫ D.t i j ≫ (D.V j i).ι) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      refine ⟨D.t_mem i j k _ ?_, ?_⟩
      · have h := Scheme.homOfLE_apply (X := D.U i)
          (inf_le_left : D.V i j ⊓ D.V i k ≤ D.V i j) x
        exact h ▸ x.2.2
      · exact (D.t i j _).2)

@[reassoc (attr := simp)]
lemma tInf_ι (i j k : D.J) :
    D.tInf i j k ≫ (D.V j k ⊓ D.V j i).ι =
      (D.U i).homOfLE inf_le_left ≫ D.t i j ≫ (D.V j i).ι :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc]
lemma tInf_homOfLE (i j k : D.J) :
    D.tInf i j k ≫ (D.U j).homOfLE inf_le_right = (D.U i).homOfLE inf_le_left ≫ D.t i j := by
  rw [← cancel_mono (D.V j i).ι]
  simp [Scheme.homOfLE_ι]

lemma cocycle_tInf (i j k : D.J) :
    D.tInf i j k ≫ (D.U j).homOfLE inf_le_left ≫ D.t j k ≫ (D.V k j).ι =
      (D.U i).homOfLE inf_le_right ≫ D.t i k ≫ (D.V k i).ι := by
  rw [← D.cocycle i j k, ← Category.assoc]
  refine congrArg (· ≫ D.t j k ≫ (D.V k j).ι) ?_
  exact IsOpenImmersion.lift_uniq _ _ _ _ (by simp [Scheme.homOfLE_ι])

/-- The transition maps are mutually inverse; this follows from the cocycle condition. -/
@[reassoc]
lemma t_inv (i j : D.J) : D.t i j ≫ D.t j i = 𝟙 _ := by
  have h := D.cocycle_tInf i j i
  have e : D.tInf i j i ≫ (D.U j).homOfLE (inf_le_left : D.V j i ⊓ D.V j i ≤ D.V j i) =
      (D.U i).homOfLE inf_le_left ≫ D.t i j := D.tInf_homOfLE i j i
  rw [reassoc_of% e, D.t_self, Category.id_comp, Scheme.homOfLE_ι] at h
  have : IsIso ((D.U i).homOfLE (inf_le_left : D.V i j ⊓ D.V i i ≤ D.V i j)) :=
    ⟨(D.U i).homOfLE (le_inf le_rfl (D.V_self i ▸ le_top)), by simp [Scheme.homOfLE_homOfLE,
      Scheme.homOfLE_rfl], by simp [Scheme.homOfLE_homOfLE, Scheme.homOfLE_rfl]⟩
  rw [← cancel_mono (D.V i j).ι, ← cancel_epi ((D.U i).homOfLE
    (inf_le_left : D.V i j ⊓ D.V i i ≤ D.V i j))]
  simpa [Scheme.homOfLE_ι] using h

instance isIso_t (i j : D.J) : IsIso (D.t i j) := ⟨⟨D.t j i, D.t_inv i j, D.t_inv j i⟩⟩

@[reassoc]
lemma tInf_tInf_tInf (i j k : D.J) : D.tInf i j k ≫ D.tInf j k i ≫ D.tInf k i j = 𝟙 _ := by
  rw [← cancel_mono (D.V i j ⊓ D.V i k).ι, Category.assoc, Category.assoc, tInf_ι,
    Category.id_comp]
  have h := D.cocycle_tInf j k i
  rw [h, D.tInf_homOfLE_assoc, D.t_inv_assoc, Scheme.homOfLE_ι]

/-- The `Scheme.GlueData` associated to gluing data along opens. -/
noncomputable def toGlueData (D : OpensGlueData.{u}) : Scheme.GlueData.{u} where
  J := D.J
  U := D.U
  V ij := D.V ij.1 ij.2
  f i j := (D.V i j).ι
  f_id i := D.V_self i ▸ (Scheme.topIso _).isIso_hom
  f_hasPullback := inferInstance
  f_open := inferInstance
  t := D.t
  t_id := D.t_self
  t' i j k := (isPullback_opens_inf (D.V i j) (D.V i k)).isoPullback.inv ≫ D.tInf i j k ≫
    (isPullback_opens_inf (D.V j k) (D.V j i)).isoPullback.hom
  t_fac i j k := by
    simp [D.tInf_homOfLE]
  cocycle i j k := by
    simp [D.tInf_tInf_tInf_assoc]

/-- The glued scheme. -/
noncomputable def glued : Scheme.{u} := D.toGlueData.glued

/-- The open immersion of the `i`-th chart into the glued scheme. -/
noncomputable def ι (i : D.J) : D.U i ⟶ D.glued := D.toGlueData.ι i

instance (i : D.J) : IsOpenImmersion (D.ι i) :=
  Scheme.GlueData.ι_isOpenImmersion D.toGlueData i

lemma ι_jointly_surjective (x : D.glued) : ∃ (i : D.J) (y : D.U i), D.ι i y = x :=
  D.toGlueData.ι_jointly_surjective x

/-- Two points of the charts agree in the glued scheme iff they are related by some `t i j`. -/
lemma ι_eq_iff {i j : D.J} (x : D.U i) (y : D.U j) :
    D.ι i x = D.ι j y ↔ ∃ z : D.V i j, z.1 = x ∧ (D.t i j z).1 = y :=
  D.toGlueData.ι_eq_iff i j x y

lemma preimage_opensRange_ι (i j : D.J) : D.ι i ⁻¹ᵁ (D.ι j).opensRange = D.V i j := by
  ext x
  simp only [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange, SetLike.mem_coe]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl, -⟩ := (D.ι_eq_iff x y).mp hy.symm
    exact z.2
  · intro hx
    refine ⟨(D.t i j ⟨x, hx⟩).1, ?_⟩
    exact ((D.ι_eq_iff x _).mpr ⟨⟨x, hx⟩, rfl, rfl⟩).symm

/-- The overlap `V i j` is the fibre product of the charts `U j` and `U i` over the glued scheme. -/
lemma isPullback (i j : D.J) :
    IsPullback (D.t i j ≫ (D.V j i).ι) (D.V i j).ι (D.ι j) (D.ι i) :=
  (IsPullback.of_isLimit (D.toGlueData.vPullbackConeIsLimit i j)).flip

/-- The charts as an open cover of the glued scheme. -/
noncomputable def openCover : D.glued.OpenCover := D.toGlueData.openCover

@[simp]
lemma openCover_I₀ : D.openCover.I₀ = D.J := rfl

@[simp]
lemma openCover_X (i : D.J) : D.openCover.X i = D.U i := rfl

@[simp]
lemma openCover_f (i : D.J) : D.openCover.f i = D.ι i := rfl

/-- Glue morphisms out of the charts that are compatible on the overlaps. -/
noncomputable def glueMorphisms {Y : Scheme.{u}} (g : ∀ i, D.U i ⟶ Y)
    (hg : ∀ i j, D.t i j ≫ (D.V j i).ι ≫ g j = (D.V i j).ι ≫ g i) : D.glued ⟶ Y :=
  Multicoequalizer.desc D.toGlueData.diagram _ g fun ij ↦ (hg ij.1 ij.2).symm.trans
    (Category.assoc _ _ _).symm

/-- Finitely many quasi-compact charts glue to a quasi-compact scheme. -/
instance compactSpace_glued [Finite D.J] [∀ i, CompactSpace (D.U i)] : CompactSpace D.glued := by
  refine ⟨?_⟩
  have : (Set.univ : Set D.glued) = ⋃ i, Set.range (D.ι i) := by
    refine (Set.eq_univ_of_forall fun x ↦ ?_).symm
    obtain ⟨i, y, rfl⟩ := D.ι_jointly_surjective x
    exact Set.mem_iUnion.mpr ⟨i, y, rfl⟩
  rw [this]
  exact isCompact_iUnion fun i ↦ isCompact_range (D.ι i).continuous

end OpensGlueData

end AlgebraicGeometry.Scheme
