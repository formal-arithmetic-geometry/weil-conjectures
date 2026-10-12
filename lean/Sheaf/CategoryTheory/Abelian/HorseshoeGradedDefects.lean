/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Graded maps and their horseshoe defects

Source: Weibel, Theorem 2.4.6; Stacks Project, Tags 0136 and 013T.
(blueprint: lem-weil-pbc-horseshoe-graded-defects).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.InjectiveResolution

/-- Degreewise splittings give a graded middle map whose differential and augmentation
errors factor through the outer terms.

Source: Weibel, Theorem 2.4.6, the splitting and defect-factorization steps; Stacks
Project, Tag 0136, for the injective splittings, and Tag 013T for the horseshoe diagram.
Proof: split the source row using a retraction `r` of `alpha` and split the target row
using a section `s'` of `beta'`. Put `chi_n = r_n phiA_n alpha'_n + beta_n phiC_n s'_n`.
The splitting identities and the zero composites prove both outer squares. Its defect
`D_n = chi_n d'_n - d_n chi_(n+1)` vanishes after precomposition with `alpha_n`
and after postcomposition with `beta'_(n+1)`, by the chain-map identities of the four
row maps and the two outer lifts. First descend across the epic `beta_n`, then lift
across the monic `alpha'_(n+1)`, to obtain `E_n` with `D_n = beta_n E_n alpha'_(n+1)`.
The differential-square-zero identities give `D_n d'_(n+1) + d_n D_(n+1) = 0`.
Cancelling the epic `beta_n` and monic `alpha'_(n+2)` proves the cocycle identity.
The augmentation error `w = iB chi_0 - b jB` vanishes on `f` by the first outer
square, the augmentation equations and the first square of `F`. It vanishes under
`beta'_0` by the second outer square and the second square of `F`. Exactness of
`S` and of the target row therefore gives `w = g e alpha'_0`. Compose with `d'_0`,
use the augmentation differential identities, and substitute the factorization of
`D_0`. Cancel the epic `g` and the monic `alpha'_1` to obtain `iC E_0 = e d'_A`.
This construction is degreewise and makes no claim that `chi` is a chain map.
(blueprint: lem-weil-pbc-horseshoe-graded-defects) -/
theorem horseshoe_graded_defects
    {C : Type u} [Category.{v} C] [Abelian C]
    (S T : ShortComplex C) (hS : S.ShortExact) (_hT : T.ShortExact) (F : S ⟶ T)
    (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
    (IC : InjectiveResolution S.X₃) (JA : InjectiveResolution T.X₁)
    (JB : InjectiveResolution T.X₂) (JC : InjectiveResolution T.X₃)
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (α' : JA.cocomplex ⟶ JB.cocomplex) (β' : JB.cocomplex ⟶ JC.cocomplex)
    (hαβ : α ≫ β = 0) (hαβ' : α' ≫ β' = 0)
    (hα : IA.ι ≫ α = (CochainComplex.single₀ C).map S.f ≫ IB.ι)
    (hβ : IB.ι ≫ β = (CochainComplex.single₀ C).map S.g ≫ IC.ι)
    (hα' : JA.ι ≫ α' = (CochainComplex.single₀ C).map T.f ≫ JB.ι)
    (hβ' : JB.ι ≫ β' = (CochainComplex.single₀ C).map T.g ≫ JC.ι)
    (hexact : ∀ n : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact)
    (hexact' : ∀ n : ℕ, ((ShortComplex.mk α' β' hαβ').map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact)
    (φA : IA.cocomplex ⟶ JA.cocomplex) (φC : IC.cocomplex ⟶ JC.cocomplex)
    (hφA : IA.ι ≫ φA = (CochainComplex.single₀ C).map F.τ₁ ≫ JA.ι)
    (hφC : IC.ι ≫ φC = (CochainComplex.single₀ C).map F.τ₃ ≫ JC.ι) :
    ∃ (χ : ∀ n : ℕ, IB.cocomplex.X n ⟶ JB.cocomplex.X n)
      (E : ∀ n : ℕ, IC.cocomplex.X n ⟶ JA.cocomplex.X (n + 1))
      (e : S.X₃ ⟶ JA.cocomplex.X 0),
      (∀ n, α.f n ≫ χ n = φA.f n ≫ α'.f n) ∧
      (∀ n, χ n ≫ β'.f n = β.f n ≫ φC.f n) ∧
      (∀ n, χ n ≫ JB.cocomplex.d n (n + 1) -
        IB.cocomplex.d n (n + 1) ≫ χ (n + 1) = β.f n ≫ E n ≫ α'.f (n + 1)) ∧
      (IB.ι.f 0 ≫ χ 0 : S.X₂ ⟶ JB.cocomplex.X 0) - F.τ₂ ≫ JB.ι.f 0 = S.g ≫ e ≫ α'.f 0 ∧
      (∀ n, E n ≫ JA.cocomplex.d (n + 1) (n + 2) +
        IC.cocomplex.d n (n + 1) ≫ E (n + 1) = 0) ∧
      IC.ι.f 0 ≫ E 0 = e ≫ JA.cocomplex.d 0 1 := by
  classical
  have hz : ∀ n, α.f n ≫ β.f n = 0 := fun n ↦
    HomologicalComplex.congr_hom hαβ n
  have hz' : ∀ n, α'.f n ≫ β'.f n = 0 := fun n ↦
    HomologicalComplex.congr_hom hαβ' n
  have hR : ∀ n, (ShortComplex.mk (α.f n) (β.f n) (hz n)).ShortExact := hexact
  have hR' : ∀ n, (ShortComplex.mk (α'.f n) (β'.f n) (hz' n)).ShortExact := hexact'
  have : ∀ n : ℕ, Mono (α.f n) := fun n ↦ (hR n).mono_f
  have : ∀ n : ℕ, Epi (β.f n) := fun n ↦ (hR n).epi_g
  have : ∀ n : ℕ, Mono (α'.f n) := fun n ↦ (hR' n).mono_f
  have : ∀ n : ℕ, Epi (β'.f n) := fun n ↦ (hR' n).epi_g
  have : Epi S.g := hS.epi_g
  let r := fun n ↦ (hR n).splittingOfInjective.r
  let s' := fun n ↦ (hR' n).splittingOfInjective.s
  have hr : ∀ n, α.f n ≫ r n = 𝟙 _ := fun n ↦ (hR n).splittingOfInjective.f_r
  have hs' : ∀ n, s' n ≫ β'.f n = 𝟙 _ := fun n ↦ (hR' n).splittingOfInjective.s_g
  let χ := fun n ↦ r n ≫ φA.f n ≫ α'.f n + β.f n ≫ φC.f n ≫ s' n
  have hχα : ∀ n, α.f n ≫ χ n = φA.f n ≫ α'.f n := by
    intro n
    dsimp only [χ]
    simp only [Preadditive.comp_add, ← Category.assoc, hr, hz, Category.id_comp,
      zero_comp, add_zero]
  have hχβ : ∀ n, χ n ≫ β'.f n = β.f n ≫ φC.f n := by
    intro n
    dsimp only [χ]
    simp only [Preadditive.add_comp, Category.assoc, hz', hs', comp_zero,
      Category.comp_id, zero_add]
  let D := fun n ↦ χ n ≫ JB.cocomplex.d n (n + 1) -
    IB.cocomplex.d n (n + 1) ≫ χ (n + 1)
  have hαD : ∀ n, α.f n ≫ D n = 0 := by
    intro n
    dsimp only [D]
    rw [Preadditive.comp_sub, ← Category.assoc, hχα, Category.assoc, α'.comm,
      ← Category.assoc (φA.f n), φA.comm, Category.assoc,
      ← Category.assoc (α.f n), α.comm, Category.assoc, hχα, sub_self]
  have hDβ : ∀ n, D n ≫ β'.f (n + 1) = 0 := by
    intro n
    dsimp only [D]
    rw [Preadditive.sub_comp, Category.assoc, ← β'.comm,
      ← Category.assoc (χ n), hχβ, Category.assoc, φC.comm,
      ← Category.assoc (β.f n), β.comm, Category.assoc,
      Category.assoc, hχβ, sub_self]
  have factor : ∀ n, ∃ E : IC.cocomplex.X n ⟶ JA.cocomplex.X (n + 1),
      D n = β.f n ≫ E ≫ α'.f (n + 1) := by
    intro n
    let G := (hR n).exact.desc (D n) (hαD n)
    have hG : β.f n ≫ G = D n := (hR n).exact.g_desc _ _
    have hGβ : G ≫ β'.f (n + 1) = 0 := by
      apply (cancel_epi (β.f n)).1
      rw [← Category.assoc, hG, hDβ, comp_zero]
    refine ⟨(hR' (n + 1)).exact.lift G hGβ, ?_⟩
    rw [(hR' (n + 1)).exact.lift_f, hG]
  choose E hDE using factor
  let w : S.X₂ ⟶ JB.cocomplex.X 0 :=
    (IB.ι.f 0 ≫ χ 0 : S.X₂ ⟶ JB.cocomplex.X 0) - F.τ₂ ≫ JB.ι.f 0
  have ha : S.f ≫ IB.ι.f 0 = IA.ι.f 0 ≫ α.f 0 := by
    simpa using (HomologicalComplex.congr_hom hα 0).symm
  have hb : IB.ι.f 0 ≫ β.f 0 = S.g ≫ IC.ι.f 0 := by
    simpa using HomologicalComplex.congr_hom hβ 0
  have ha' : JA.ι.f 0 ≫ α'.f 0 = T.f ≫ JB.ι.f 0 := by
    simpa using HomologicalComplex.congr_hom hα' 0
  have hb' : JB.ι.f 0 ≫ β'.f 0 = T.g ≫ JC.ι.f 0 := by
    simpa using HomologicalComplex.congr_hom hβ' 0
  have hpa : IA.ι.f 0 ≫ φA.f 0 = F.τ₁ ≫ JA.ι.f 0 := by
    simpa using HomologicalComplex.congr_hom hφA 0
  have hpc : IC.ι.f 0 ≫ φC.f 0 = F.τ₃ ≫ JC.ι.f 0 := by
    simpa using HomologicalComplex.congr_hom hφC 0
  have hfw : S.f ≫ w = 0 := by
    dsimp only [w]
    rw [Preadditive.comp_sub, ← Category.assoc, ha, Category.assoc, hχα,
      ← Category.assoc, hpa, Category.assoc, ha', ← Category.assoc,
      F.comm₁₂, Category.assoc, sub_self]
  have hwβ : w ≫ β'.f 0 = 0 := by
    dsimp only [w]
    rw [Preadditive.sub_comp, Category.assoc, hχβ, ← Category.assoc, hb,
      Category.assoc, hpc, ← Category.assoc, ← F.comm₂₃, Category.assoc,
      ← hb', Category.assoc, sub_self]
  let wA := (hR' 0).exact.lift w hwβ
  have hwA : wA ≫ α'.f 0 = w := (hR' 0).exact.lift_f _ _
  have hfwA : S.f ≫ wA = 0 := by
    apply (cancel_mono (α'.f 0)).1
    rw [Category.assoc, hwA, hfw, zero_comp]
  let e := hS.exact.desc wA hfwA
  have hge : S.g ≫ e = wA := hS.exact.g_desc _ _
  have hwe : w = S.g ≫ e ≫ α'.f 0 := by rw [← Category.assoc, hge, hwA]
  refine ⟨χ, E, e, hχα, hχβ, hDE, hwe, ?_, ?_⟩
  · intro n
    apply (cancel_epi (β.f n)).1
    apply (cancel_mono (α'.f (n + 2))).1
    rw [comp_zero, zero_comp]
    calc
      (β.f n ≫ (E n ≫ JA.cocomplex.d (n + 1) (n + 2) +
          IC.cocomplex.d n (n + 1) ≫ E (n + 1))) ≫ α'.f (n + 2) =
          (β.f n ≫ E n ≫ α'.f (n + 1)) ≫ JB.cocomplex.d (n + 1) (n + 2) +
            IB.cocomplex.d n (n + 1) ≫ (β.f (n + 1) ≫ E (n + 1) ≫
              α'.f (n + 2)) := by
        simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
          α'.comm, ← β.comm_assoc]
      _ = D n ≫ JB.cocomplex.d (n + 1) (n + 2) +
          IB.cocomplex.d n (n + 1) ≫ D (n + 1) := by rw [← hDE n, ← hDE (n + 1)]
      _ = 0 := by
        dsimp only [D]
        simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc,
          HomologicalComplex.d_comp_d, HomologicalComplex.d_comp_d_assoc,
          comp_zero, zero_comp]
        abel
  · apply (cancel_epi S.g).1
    apply (cancel_mono (α'.f 1)).1
    calc
      (S.g ≫ IC.ι.f 0 ≫ E 0) ≫ α'.f 1 = IB.ι.f 0 ≫ D 0 := by
        simp only [Category.assoc]
        rw [← Category.assoc S.g, ← hb, Category.assoc, ← hDE 0]
      _ = w ≫ JB.cocomplex.d 0 1 := by
        dsimp only [D, w]
        rw [Preadditive.comp_sub, ← Category.assoc (IB.ι.f 0) (IB.cocomplex.d 0 1),
          IB.ι_f_zero_comp_complex_d, zero_comp, sub_zero,
          Preadditive.sub_comp, Category.assoc F.τ₂,
          JB.ι_f_zero_comp_complex_d, comp_zero, sub_zero, Category.assoc]
      _ = (S.g ≫ e ≫ JA.cocomplex.d 0 1) ≫ α'.f 1 := by
        rw [hwe]
        simp only [Category.assoc, α'.comm]

end CategoryTheory.InjectiveResolution
