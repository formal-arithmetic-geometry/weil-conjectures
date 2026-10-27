/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups V2 and Z7, Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Additive

/-! # Good truncations under an exact additive functor

Source: Stacks Project, Tag 0118, functorial good truncations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u a b c d
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex
namespace WeilConjectures

-- The lower-boundary calculations follow the proved source-library argument in
-- WeilConjectures.Algebra.Homology.RightExactTruncGEIso.
private theorem projection_f_eq_opcycles
    {A : Type a} [Category.{b} A] [Abelian A]
    (K : CochainComplex A ℤ) (n : ℤ) :
    (K.πTruncGE n).f n = K.pOpcycles n ≫ (K.truncGEXIsoOpcycles n).inv := by
  dsimp only [CochainComplex.πTruncGE, HomologicalComplex.πTruncGE]
  rw [ComplexShape.Embedding.liftExtend_f _ _ _ (i := 0) (by simp)]
  rw [HomologicalComplex.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv
    _ _ (i := 0) (i' := n) (by simp)
      (by simp [ComplexShape.boundaryGE_embeddingUpIntGE_iff])]
  simp [CochainComplex.truncGEXIsoOpcycles, HomologicalComplex.truncGEXIsoOpcycles]

private noncomputable def projectionIsCokernel
    {A : Type a} [Category.{b} A] [Abelian A]
    (K : CochainComplex A ℤ) (n : ℤ) :
    IsColimit (CokernelCofork.ofπ ((K.πTruncGE n).f n)
      (show K.d (n - 1) n ≫ (K.πTruncGE n).f n = 0 by
        rw [projection_f_eq_opcycles, ← Category.assoc, K.d_pOpcycles, zero_comp])) :=
  IsCokernel.cokernelIso _ _ (K.opcyclesIsCokernel (i := n - 1) (j := n) (by simp))
    (K.truncGEXIsoOpcycles n).symm (projection_f_eq_opcycles K n).symm

private theorem isIso_projection_f
    {A : Type a} [Category.{b} A] [Abelian A]
    (K : CochainComplex A ℤ) (n i : ℤ) (hi : n < i) :
    IsIso ((K.πTruncGE n).f i) := by
  have he : (ComplexShape.embeddingUpIntGE n).f (i - n).natAbs = i := by
    change n + ((i - n).natAbs : ℤ) = i
    rw [Int.natAbs_of_nonneg (by omega), add_sub_cancel]
  have hb : ¬ (ComplexShape.embeddingUpIntGE n).BoundaryGE (i - n).natAbs := by
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff, Int.natAbs_eq_zero]
    omega
  dsimp only [CochainComplex.πTruncGE, HomologicalComplex.πTruncGE]
  rw [ComplexShape.Embedding.isIso_liftExtend_f_iff _ _ _ he]
  exact HomologicalComplex.isIso_restrictionToTruncGE' K _ _ hb

-- The upper-boundary coordinate calculation follows
-- WeilConjectures.Algebra.Homology.UpperTruncationStepSES.
private lemma truncLEXIsoCycles_comp_iCycles {C : Type a} [Category.{b} C] [Abelian C]
    (K : CochainComplex C ℤ) (q : ℤ) :
    (K.truncLEXIsoCycles q).hom ≫ K.iCycles q = (K.ιTruncLE q).f q := by
  have h : (K.op.πTruncGE (ComplexShape.embeddingUpIntLE q).op).f q =
      K.op.pOpcycles q ≫
        (K.op.truncGEXIsoOpcycles (ComplexShape.embeddingUpIntLE q).op
          (i := 0) (by change q - 0 = q; omega) (by simp [ComplexShape.Embedding.op_boundaryGE_iff,
            ComplexShape.boundaryLE_embeddingUpIntLE_iff])).inv := by
    rw [HomologicalComplex.πTruncGE,
      ComplexShape.Embedding.liftExtend_f (ComplexShape.embeddingUpIntLE q).op
        _ _ (i := 0) (by change q - 0 = q; omega),
      HomologicalComplex.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv
        K.op (ComplexShape.embeddingUpIntLE q).op (i := 0)
        (by change q - 0 = q; omega) (by simp [ComplexShape.Embedding.op_boundaryGE_iff,
          ComplexShape.boundaryLE_embeddingUpIntLE_iff])]
    simp [HomologicalComplex.truncGEXIsoOpcycles, Category.assoc]
  simp only [CochainComplex.truncLEXIsoCycles, HomologicalComplex.truncLEXIsoCycles,
    CochainComplex.ιTruncLE, HomologicalComplex.ιTruncLE, HomologicalComplex.unopFunctor_map_f,
    Quiver.Hom.unop_op, h, Iso.trans_hom, Iso.symm_hom, Iso.unop_inv, CategoryTheory.unop_comp,
    Category.assoc]
  have hh := congrArg Quiver.Hom.unop
    ((K.sc q).op_pOpcycles_opcyclesOpIso_hom)
  change (K.opcyclesOpIso q).hom.unop ≫ (K.op.pOpcycles q).unop = K.iCycles q at hh
  rw [← hh]
  simp only [← CategoryTheory.unop_comp, Category.assoc, Iso.hom_inv_id_assoc]

private theorem isIso_inclusion_f
    {A : Type a} [Category.{b} A] [Abelian A]
    (K : CochainComplex A ℤ) (n i : ℤ) (hi : i < n) :
    IsIso ((K.ιTruncLE n).f i) := by
  change IsIso ((K.op.πTruncGE (ComplexShape.embeddingUpIntLE n).op).f i).unop
  have he : (ComplexShape.embeddingUpIntLE n).op.f (n - i).natAbs = i := by
    change n - ((n - i).natAbs : ℤ) = i
    rw [Int.natAbs_of_nonneg (by omega)]
    omega
  have hb : ¬ (ComplexShape.embeddingUpIntLE n).op.BoundaryGE (n - i).natAbs := by
    simp only [ComplexShape.Embedding.op_boundaryGE_iff,
      ComplexShape.boundaryLE_embeddingUpIntLE_iff, Int.natAbs_eq_zero]
    omega
  have : IsIso ((K.op.πTruncGE (ComplexShape.embeddingUpIntLE n).op).f i) := by
    rw [HomologicalComplex.πTruncGE,
      ComplexShape.Embedding.isIso_liftExtend_f_iff _ _ _ he]
    exact HomologicalComplex.isIso_restrictionToTruncGE' K.op _ _ hb
  infer_instance

private noncomputable def inclusionIsKernel
    {A : Type a} [Category.{b} A] [Abelian A]
    (K : CochainComplex A ℤ) (n : ℤ) :
    IsLimit (KernelFork.ofι ((K.ιTruncLE n).f n)
      (show (K.ιTruncLE n).f n ≫ K.d n (n + 1) = 0 by
        rw [← truncLEXIsoCycles_comp_iCycles, Category.assoc, K.iCycles_d, comp_zero])) :=
  IsKernel.isoKernel _ _ (K.cyclesIsKernel n (n + 1) (by simp))
    (K.truncLEXIsoCycles n) (truncLEXIsoCycles_comp_iCycles K n)

private theorem upperComparison
    {A : Type a} [Category.{b} A] [Abelian A]
    {B : Type c} [Category.{d} B] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex A ℤ) (n : ℤ) :
    ∃ e : (F.mapHomologicalComplex (.up ℤ)).obj (K.truncLE n) ≅
        CochainComplex.truncLE ((F.mapHomologicalComplex (.up ℤ)).obj K) n,
      e.hom ≫ CochainComplex.ιTruncLE ((F.mapHomologicalComplex (.up ℤ)).obj K) n =
        (F.mapHomologicalComplex (.up ℤ)).map (K.ιTruncLE n) := by
  classical
  let L : CochainComplex B ℤ := (F.mapHomologicalComplex (.up ℤ)).obj K
  have term (i : ℤ) : ∃ e : F.obj ((K.truncLE n).X i) ≅ (L.truncLE n).X i,
      e.hom ≫ (L.ιTruncLE n).f i = F.map ((K.ιTruncLE n).f i) := by
    obtain hi | hi | hi := lt_trichotomy i n
    · have : IsIso ((K.ιTruncLE n).f i) := isIso_inclusion_f K n i hi
      have : IsIso ((L.ιTruncLE n).f i) := isIso_inclusion_f L n i hi
      refine ⟨asIso (F.map ((K.ιTruncLE n).f i)) ≪≫
        (asIso ((L.ιTruncLE n).f i)).symm, ?_⟩
      simp
    · subst i
      let h₁ := KernelFork.ofι ((K.ιTruncLE n).f n)
        (show (K.ιTruncLE n).f n ≫ K.d n (n + 1) = 0 by
          rw [← truncLEXIsoCycles_comp_iCycles, Category.assoc, K.iCycles_d, comp_zero])
      let hc₁ := h₁.mapIsLimit (inclusionIsKernel K n) F
      let hc₂ := inclusionIsKernel L n
      let e := hc₁.conePointUniqueUpToIso hc₂
      exact ⟨e, hc₁.conePointUniqueUpToIso_hom_comp hc₂ WalkingParallelPair.zero⟩
    · have hz₁ := F.map_isZero ((K.truncLE n).isZero_of_isStrictlyLE n i hi)
      have hz₂ := (L.truncLE n).isZero_of_isStrictlyLE n i hi
      exact ⟨hz₁.iso hz₂, hz₁.eq_of_src _ _⟩
  choose e he using term
  let E : (F.mapHomologicalComplex (.up ℤ)).obj (K.truncLE n) ≅ L.truncLE n :=
      HomologicalComplex.Hom.isoOfComponents e (by
    intro i j hij
    have : Mono ((L.ιTruncLE n).f j) := by
      dsimp only [CochainComplex.ιTruncLE]
      infer_instance
    apply (cancel_mono ((L.ιTruncLE n).f j)).1
    change ((e i).hom ≫ (L.truncLE n).d i j) ≫ (L.ιTruncLE n).f j =
      (F.map ((K.truncLE n).d i j) ≫ (e j).hom) ≫ (L.ιTruncLE n).f j
    simp only [Category.assoc]
    rw [← (L.ιTruncLE n).comm i j, ← Category.assoc, he i, he j]
    change F.map ((K.ιTruncLE n).f i) ≫ F.map (K.d i j) =
      F.map ((K.truncLE n).d i j) ≫ F.map ((K.ιTruncLE n).f j)
    rw [← F.map_comp, ← F.map_comp, (K.ιTruncLE n).comm i j])
  refine ⟨E, ?_⟩
  ext i
  exact he i

private theorem lowerComparison
    {A : Type a} [Category.{b} A] [Abelian A]
    {B : Type c} [Category.{d} B] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
    (K : CochainComplex A ℤ) (n : ℤ) :
    ∃ e : (F.mapHomologicalComplex (.up ℤ)).obj (K.truncGE n) ≅
        CochainComplex.truncGE ((F.mapHomologicalComplex (.up ℤ)).obj K) n,
      (F.mapHomologicalComplex (.up ℤ)).map (K.πTruncGE n) ≫ e.hom =
        CochainComplex.πTruncGE ((F.mapHomologicalComplex (.up ℤ)).obj K) n := by
  classical
  let L : CochainComplex B ℤ := (F.mapHomologicalComplex (.up ℤ)).obj K
  have term (i : ℤ) : ∃ e : F.obj ((K.truncGE n).X i) ≅ (L.truncGE n).X i,
      F.map ((K.πTruncGE n).f i) ≫ e.hom = (L.πTruncGE n).f i := by
    obtain hi | hi | hi := lt_trichotomy i n
    · have hz₁ := F.map_isZero ((K.truncGE n).isZero_of_isStrictlyGE n i hi)
      have hz₂ := (L.truncGE n).isZero_of_isStrictlyGE n i hi
      exact ⟨hz₁.iso hz₂, hz₂.eq_of_tgt _ _⟩
    · subst i
      let h₁ := (CokernelCofork.ofπ ((K.πTruncGE n).f n)
          (show K.d (n - 1) n ≫ (K.πTruncGE n).f n = 0 by
            rw [projection_f_eq_opcycles, ← Category.assoc, K.d_pOpcycles, zero_comp]))
      let hc₁ := h₁.mapIsColimit (projectionIsCokernel K n) F
      let hc₂ := projectionIsCokernel L n
      let e := hc₁.coconePointUniqueUpToIso hc₂
      exact ⟨e, hc₁.comp_coconePointUniqueUpToIso_hom hc₂ WalkingParallelPair.one⟩
    · have : IsIso ((K.πTruncGE n).f i) := isIso_projection_f K n i hi
      have : IsIso ((L.πTruncGE n).f i) := isIso_projection_f L n i hi
      refine ⟨(asIso (F.map ((K.πTruncGE n).f i))).symm ≪≫
        asIso ((L.πTruncGE n).f i), ?_⟩
      simp
  choose e he using term
  let E : (F.mapHomologicalComplex (.up ℤ)).obj (K.truncGE n) ≅ L.truncGE n :=
      HomologicalComplex.Hom.isoOfComponents e (by
    intro i j hij
    have : Epi ((K.πTruncGE n).f i) := by
      dsimp only [CochainComplex.πTruncGE]
      infer_instance
    have : Epi (F.map ((K.πTruncGE n).f i)) := inferInstance
    apply (cancel_epi (F.map ((K.πTruncGE n).f i))).1
    rw [← Category.assoc, he i, (L.πTruncGE n).comm i j]
    change F.map (K.d i j) ≫ (L.πTruncGE n).f j =
      F.map ((K.πTruncGE n).f i) ≫ F.map ((K.truncGE n).d i j) ≫ (e j).hom
    rw [← Category.assoc, ← F.map_comp, (K.πTruncGE n).comm i j,
      F.map_comp, Category.assoc, he j])
  refine ⟨E, ?_⟩
  ext i
  exact he i

/-- Exact additive functors commute with both good truncations and the canonical arrows.
Source: Stacks Project, Tag 0118
(blueprint: lem-trf-exact-functor-good-truncations).

Proof: in degrees below the upper boundary and above the lower boundary use identity
maps. At the upper boundary use the kernel comparison supplied by preservation of
finite limits. At the lower boundary use the cokernel comparison supplied by
preservation of finite colimits. Outside the retained half-line use the unique map
between zero objects. The defining kernel and cokernel equations show that these
maps commute with every differential and with every complex map. The inverse
comparisons give the inverses degreewise. Their universal property also identifies
the upper inclusion and lower projection with the images of the original arrows. -/
theorem exactFunctorGoodTruncations {A : Type a} [Category.{b} A] [Abelian A]
    {B : Type c} [Category.{d} B] [Abelian B] (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (p q : ℤ) :
  ∃ (e : (ComplexShape.embeddingUpIntLE q).truncLEFunctor A ⋙
        F.mapHomologicalComplex (.up ℤ) ≅ F.mapHomologicalComplex (.up ℤ) ⋙
          (ComplexShape.embeddingUpIntLE q).truncLEFunctor B)
    (f : (ComplexShape.embeddingUpIntGE p).truncGEFunctor A ⋙
        F.mapHomologicalComplex (.up ℤ) ≅ F.mapHomologicalComplex (.up ℤ) ⋙
          (ComplexShape.embeddingUpIntGE p).truncGEFunctor B),
    (∀ K : CochainComplex A ℤ,
      e.hom.app K ≫ CochainComplex.ιTruncLE
          ((F.mapHomologicalComplex (.up ℤ)).obj K) q =
        (F.mapHomologicalComplex (.up ℤ)).map (K.ιTruncLE q)) ∧
    (∀ K : CochainComplex A ℤ,
      (F.mapHomologicalComplex (.up ℤ)).map (K.πTruncGE p) ≫ f.hom.app K =
        CochainComplex.πTruncGE ((F.mapHomologicalComplex (.up ℤ)).obj K) p) := by
  classical
  let G := F.mapHomologicalComplex (.up ℤ)
  choose e he using fun K : CochainComplex A ℤ ↦ upperComparison F K q
  choose f hf using fun K : CochainComplex A ℤ ↦ lowerComparison F K p
  let e' : (ComplexShape.embeddingUpIntLE q).truncLEFunctor A ⋙ G ≅
      G ⋙ (ComplexShape.embeddingUpIntLE q).truncLEFunctor B :=
    NatIso.ofComponents e (by
      intro K L φ
      have : Mono (CochainComplex.ιTruncLE (G.obj L) q) := by
        dsimp only [CochainComplex.ιTruncLE]
        infer_instance
      apply (cancel_mono (CochainComplex.ιTruncLE (G.obj L) q)).1
      change (G.map (CochainComplex.truncLEMap φ q) ≫ (e L).hom) ≫
          CochainComplex.ιTruncLE (G.obj L) q =
        ((e K).hom ≫ CochainComplex.truncLEMap (G.map φ) q) ≫ CochainComplex.ιTruncLE (G.obj L) q
      rw [Category.assoc, he L, Category.assoc, CochainComplex.ιTruncLE_naturality,
        ← Category.assoc, he K, ← G.map_comp, CochainComplex.ιTruncLE_naturality,
        G.map_comp])
  let f' : (ComplexShape.embeddingUpIntGE p).truncGEFunctor A ⋙ G ≅
      G ⋙ (ComplexShape.embeddingUpIntGE p).truncGEFunctor B :=
    NatIso.ofComponents f (by
      intro K L φ
      have : Epi (CochainComplex.πTruncGE K p) := by
        dsimp only [CochainComplex.πTruncGE]
        infer_instance
      have : Epi (G.map (CochainComplex.πTruncGE K p)) := inferInstance
      apply (cancel_epi (G.map (CochainComplex.πTruncGE K p))).1
      change G.map (CochainComplex.πTruncGE K p) ≫
          (G.map (CochainComplex.truncGEMap φ p) ≫ (f L).hom) =
        G.map (CochainComplex.πTruncGE K p) ≫
          ((f K).hom ≫ CochainComplex.truncGEMap (G.map φ) p)
      rw [← Category.assoc, ← G.map_comp, CochainComplex.πTruncGE_naturality,
        G.map_comp, Category.assoc, hf L, ← Category.assoc, hf K,
        CochainComplex.πTruncGE_naturality])
  exact ⟨e', f', he, hf⟩

end WeilConjectures
