/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.Algebra.Homology.LowerTruncationTransitionKernel

/-!
# Successive canonical lower truncations

Source: Stacks Project, Homology, Section 12.15 (Tag 0118), and Derived Categories,
Remark 13.12.4 (Tag 08J5) (blueprint: lem-pc-derived-lower-truncation-step-ses).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

private lemma truncGE_strict_prev (C : Type u) [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (m : ℤ) : (K.truncGE (m + 1)).IsStrictlyGE m := by
  exact isStrictlyGE_of_ge _ m (m + 1) (by omega)

private noncomputable def stepQ {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (m : ℤ) : K.truncGE m ⟶ K.truncGE (m + 1) := by
  have := truncGE_strict_prev C K m
  exact truncGEMap (K.πTruncGE (m + 1)) m ≫ inv ((K.truncGE (m + 1)).πTruncGE m)

private lemma stepQ_factor {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (m : ℤ) :
    K.πTruncGE m ≫ stepQ K m = K.πTruncGE (m + 1) := by
  have := truncGE_strict_prev C K m
  simp [stepQ, ← Category.assoc]

private lemma pi_f_above {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (m r : ℤ) (hr : m < r) :
    (K.πTruncGE m).f r = (K.truncGEXIso m r hr).inv := by
  dsimp only [πTruncGE, HomologicalComplex.πTruncGE, truncGEXIso,
    HomologicalComplex.truncGEXIso, Iso.trans_inv]
  have h : (ComplexShape.embeddingUpIntGE m).f (r - m).natAbs = r := by
    change m + ((r - m).natAbs : ℤ) = r
    rw [Int.natAbs_of_nonneg (by omega)]
    omega
  have hb : ¬ (ComplexShape.embeddingUpIntGE m).BoundaryGE (r - m).natAbs := by
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff, Int.natAbs_eq_zero]
    omega
  rw [ComplexShape.Embedding.liftExtend_f _ _ _ h,
    HomologicalComplex.restrictionToTruncGE'_f_eq_iso_hom_iso_inv _ _ h hb]
  simp

private lemma pi_f_self {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (m : ℤ) :
    (K.πTruncGE m).f m = K.pOpcycles m ≫ (K.truncGEXIsoOpcycles m).inv := by
  dsimp only [πTruncGE, HomologicalComplex.πTruncGE, truncGEXIsoOpcycles,
    HomologicalComplex.truncGEXIsoOpcycles, Iso.trans_inv]
  have h : (ComplexShape.embeddingUpIntGE m).f 0 = m := by simp
  have hb : (ComplexShape.embeddingUpIntGE m).BoundaryGE 0 := by
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
  rw [ComplexShape.Embedding.liftExtend_f _ _ _ h,
    HomologicalComplex.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv _ _ h hb]
  simp

private lemma stepQ_epi {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (m : ℤ) : Epi (stepQ K m) := by
  have : Epi (K.πTruncGE (m + 1)) := by
    dsimp only [πTruncGE]
    infer_instance
  have : Epi (K.πTruncGE m ≫ stepQ K m) := by
    rw [stepQ_factor]
    infer_instance
  exact epi_of_epi (K.πTruncGE m) (stepQ K m)

private lemma stepQ_naturality {C : Type u} [Category.{v} C] [Abelian C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (m : ℤ) :
    truncGEMap f m ≫ stepQ L m = stepQ K m ≫ truncGEMap f (m + 1) := by
  have : Epi (K.πTruncGE m) := by
    dsimp only [πTruncGE]
    infer_instance
  apply (cancel_epi (K.πTruncGE m)).mp
  simp only [← Category.assoc, πTruncGE_naturality]
  simp only [Category.assoc, stepQ_factor]
  simp only [πTruncGE_naturality]

private lemma stepQ_boundary {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (m : ℤ) :
    (stepQ K m).f m = 0 ∧
      (K.truncGEXIso m (m + 1)).inv ≫ (stepQ K m).f (m + 1) =
        (K.πTruncGE (m + 1)).f (m + 1) := by
  constructor
  · exact ((K.truncGE (m + 1)).isZero_of_isStrictlyGE (m + 1) m).eq_of_tgt _ _
  · have h := congrArg (fun f => f.f (m + 1)) (stepQ_factor K m)
    simpa only [HomologicalComplex.comp_f, pi_f_above K m (m + 1) (by omega)] using h

private lemma stepQ_above {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (m r : ℤ) (hr : m + 1 < r) :
    (K.truncGEXIso m r (by omega)).inv ≫ (stepQ K m).f r ≫
      (K.truncGEXIso (m + 1) r hr).hom = 𝟙 (K.X r) := by
  have h := congrArg (fun f => f.f r) (stepQ_factor K m)
  simp only [HomologicalComplex.comp_f, pi_f_above K m r (by omega),
    pi_f_above K (m + 1) r hr] at h
  rw [← Category.assoc, h, Iso.inv_hom_id]

private lemma truncGEMap_f_self {C : Type u} [Category.{v} C] [Abelian C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (m : ℤ) :
    (K.truncGEXIsoOpcycles m).inv ≫ (truncGEMap f m).f m =
      HomologicalComplex.opcyclesMap f m ≫ (L.truncGEXIsoOpcycles m).inv := by
  apply (cancel_epi (K.pOpcycles m)).mp
  have h := congrArg (fun f => f.f m) (πTruncGE_naturality f m)
  simpa only [HomologicalComplex.comp_f, pi_f_self, Category.assoc,
    HomologicalComplex.p_opcyclesMap_assoc] using h

set_option backward.isDefEq.respectTransparency false in
/-- (blueprint: lem-pc-derived-lower-truncation-step-ses) Stacks, Tag 0118 and Tag 08J5.
For an abelian category and any integer `m`, the transition from the canonical lower
truncation at `m` to that at `m + 1` is the quotient in degree `m + 1`, zero in degree
`m`, and the identity in higher degrees. Its kernel is the two-term complex with
`K.opcycles m = K^m / im(d^(m-1))` in degree `m` and `im(d^m)` in degree `m + 1`;
the differential is induced by `d^m`. The kernel inclusion and transition form a
degreewise short exact sequence. The canonical map from the complex concentrated
in degree `m` with value `H^m(K)` is a quasi-isomorphism, since the kernel's
cohomology is `H^m(K)` in degree `m` and zero in degree `m + 1`. For a chain map,
the maps on images and quotients give a map between these sequences, commuting
with the canonical maps from cohomology.
Proof steps (Stacks Tag 0118). First, in degrees below `m`, at `m`, at `m + 1`, and
above `m + 1`, the displayed kernel sequence is respectively zero, the identity on
`K.opcycles m`, the inclusion of `im (d^m)` as the kernel of the quotient, and the
identity. The composites are chain maps because the differential is induced by `d^m`
and `d^(m+1) d^m = 0`, so the sequence is degreewise short exact. Second, the map from
`H^m(K)[-m]` is the inclusion of cycles modulo boundaries in degree `m`; the kernel
has cohomology `H^m(K)` in degree `m`, zero in degree `m + 1`, and zero elsewhere, so
this map is a quasi-isomorphism. Third, a chain map preserves cycles and boundaries,
therefore induces the maps on images, quotients, truncations, kernels, and cohomology;
these induced maps commute with the short exact sequences and the canonical maps.
-/
theorem exists_lowerTruncationStepSES {C : Type u} [Category.{v} C] [Abelian C] :
    ∃ (q : ∀ (K : CochainComplex C ℤ) (m : ℤ),
          K.truncGE m ⟶ K.truncGE (m + 1)),
      ∃ (φ : ∀ (K : CochainComplex C ℤ) (m : ℤ),
            ((singleFunctor C m).obj (K.homology m)) ⟶
              kernel (q K m)),
        (∀ (K : CochainComplex C ℤ) (m : ℤ),
          K.πTruncGE m ≫ q K m = K.πTruncGE (m + 1)) ∧
        (∀ (K : CochainComplex C ℤ) (m : ℤ),
          (ShortComplex.mk (kernel.ι (q K m)) (q K m)
            (kernel.condition (q K m))).ShortExact) ∧
        (∀ (K : CochainComplex C ℤ) (m : ℤ),
          ∃ (e₀ : (kernel (q K m)).X m ≅ K.opcycles m)
            (e₁ : (kernel (q K m)).X (m + 1) ≅
              Abelian.image (K.d m (m + 1))),
            e₀.inv ≫ (kernel.ι (q K m)).f m =
              (K.truncGEXIsoOpcycles m).inv ∧
            e₁.inv ≫ (kernel.ι (q K m)).f (m + 1) ≫
              (K.truncGEXIso m (m + 1)).hom =
                Abelian.image.ι (K.d m (m + 1)) ∧
            e₀.inv ≫ (kernel (q K m)).d m (m + 1) ≫ e₁.hom ≫
              Abelian.image.ι (K.d m (m + 1)) =
                K.fromOpcycles m (m + 1) ∧
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m
                (K.homology m)).inv ≫ (φ K m).f m ≫ e₀.hom =
                  K.homologyι m) ∧
        (∀ (K : CochainComplex C ℤ) (m r : ℤ),
          r ≠ m → r ≠ m + 1 → IsZero ((kernel (q K m)).X r)) ∧
        (∀ (K : CochainComplex C ℤ) (m : ℤ),
          (q K m).f m = 0 ∧
          (K.truncGEXIso m (m + 1)).inv ≫ (q K m).f (m + 1) =
            (K.πTruncGE (m + 1)).f (m + 1)) ∧
        (∀ (K : CochainComplex C ℤ) (m r : ℤ) (hr : m + 1 < r),
          (K.truncGEXIso m r (by omega)).inv ≫ (q K m).f r ≫
            (K.truncGEXIso (m + 1) r (by omega)).hom = 𝟙 (K.X r)) ∧
        (∀ (K : CochainComplex C ℤ) (m : ℤ), QuasiIso (φ K m)) ∧
        (∀ {K L : CochainComplex C ℤ} (f : K ⟶ L) (m : ℤ),
          truncGEMap f m ≫ q L m = q K m ≫ truncGEMap f (m + 1) ∧
          ∃ (g : kernel (q K m) ⟶ kernel (q L m)),
            g ≫ kernel.ι (q L m) =
              kernel.ι (q K m) ≫ truncGEMap f m ∧
            (singleFunctor C m).map (HomologicalComplex.homologyMap f m) ≫
              φ L m = φ K m ≫ g) := by
  classical
  have hkernel := fun (K : CochainComplex C ℤ) (m : ℤ) =>
    exists_lowerTruncationTransitionKernel K m (stepQ K m) (stepQ_factor K m)
  let φ := fun (K : CochainComplex C ℤ) (m : ℤ) => (hkernel K m).choose
  have hφ := fun (K : CochainComplex C ℤ) (m : ℤ) => (hkernel K m).choose_spec
  refine ⟨stepQ, φ, stepQ_factor, ?_, ?_, ?_, stepQ_boundary, stepQ_above, ?_, ?_⟩
  · intro K m
    have := stepQ_epi K m
    exact { exact := ShortComplex.exact_kernel (stepQ K m) }
  · intro K m
    exact (hφ K m).1
  · intro K m r hr₀ hr₁
    exact (hφ K m).2.1 r hr₀ hr₁
  · intro K m
    exact (hφ K m).2.2
  · intro K L f m
    refine ⟨stepQ_naturality f m, ?_⟩
    let g := kernel.map (stepQ K m) (stepQ L m) (truncGEMap f m)
      (truncGEMap f (m + 1)) (stepQ_naturality f m).symm
    refine ⟨g, ?_, ?_⟩
    · simp [g]
    · have hcomp (T : CochainComplex C ℤ) :
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m (T.homology m)).inv ≫
            (φ T m).f m ≫ (kernel.ι (stepQ T m)).f m =
              T.homologyι m ≫ (T.truncGEXIsoOpcycles m).inv := by
        obtain ⟨e₀, e₁, he₀, he₁, hd, hhom⟩ := (hφ T m).1
        rw [← he₀, ← hhom]
        simp [φ, Category.assoc]
      apply (cancel_mono (kernel.ι (stepQ L m))).mp
      apply HomologicalComplex.from_single_hom_ext
      apply (cancel_epi
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m (K.homology m)).inv).mp
      simp only [HomologicalComplex.comp_f, Category.assoc]
      have hg : g.f m ≫ (kernel.ι (stepQ L m)).f m =
          (kernel.ι (stepQ K m)).f m ≫ (truncGEMap f m).f m := by
        simpa only [HomologicalComplex.comp_f] using
          congrArg (fun t => t.f m) (show g ≫ kernel.ι (stepQ L m) =
            kernel.ι (stepQ K m) ≫ truncGEMap f m by simp [g])
      rw [hg]
      have hs : ((singleFunctor C m).map (HomologicalComplex.homologyMap f m)).f m =
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m (K.homology m)).hom ≫
            HomologicalComplex.homologyMap f m ≫
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m (L.homology m)).inv :=
        HomologicalComplex.single_map_f_self _ _ _
      rw [hs]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [hcomp L]
      have hK := congrArg (fun t => t ≫ (truncGEMap f m).f m) (hcomp K)
      simp only [Category.assoc, truncGEMap_f_self] at hK
      rw [hK, HomologicalComplex.homologyι_naturality_assoc]

end CochainComplex
