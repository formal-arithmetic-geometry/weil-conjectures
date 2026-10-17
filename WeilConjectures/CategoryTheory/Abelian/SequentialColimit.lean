/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyColimit

/-!
# Sequential colimits as cokernels of `1 - shift`

Let `F : ℕ ⥤ C` be a sequence `F₀ ⟶ F₁ ⟶ ⋯` in a preadditive category, with a coproduct
`∐ₙ Fₙ` and the shift `t : ∐ₙ Fₙ ⟶ ∐ₙ Fₙ` (`CategoryTheory.Limits.sequenceShift`). Then:

* the colimit of `F` is the cokernel of `1 - t`
  (`CategoryTheory.Limits.isColimitCokernelCoforkSubSequenceShift`);
* if `C` is abelian and colimits of shape `ℕ` are exact (for instance if `C` satisfies AB5), then
  `1 - t` is a monomorphism (`CategoryTheory.Limits.mono_id_sub_sequenceShift`), so that
  `0 ⟶ ∐ₙ Fₙ ⟶ ∐ₙ Fₙ ⟶ colim F ⟶ 0` is a short exact sequence
  (`CategoryTheory.Limits.shortExact_sequenceShift`).

The injectivity of `1 - t` is reduced to the finite stages: `∐ₙ Fₙ` is the colimit of the finite
biproducts `⨁_{i ≤ N} Fᵢ`, and `1 - t` is the colimit of the maps
`⨁_{i ≤ N} Fᵢ ⟶ ⨁_{i ≤ N + 1} Fᵢ` induced by `1 - t`, which are monomorphisms (they are
unitriangular).
-/

@[expose] public section

namespace CategoryTheory.Limits

open Category

variable {C : Type*} [Category* C]

section Cokernel

variable [Preadditive C] {F : ℕ ⥤ C} {P : Cofan fun n : ℕ ↦ F.obj n} (hP : IsColimit P)

/-- The cocone over a sequence `F` given by a morphism out of `∐ₙ Fₙ` which is killed by
`1 - t`. -/
@[simps pt]
noncomputable def coconeOfSubSequenceShift {T : C} (h : P.pt ⟶ T)
    (hh : (𝟙 _ - sequenceShift hP) ≫ h = 0) : Cocone F where
  pt := T
  ι := NatTrans.ofSequence (fun n ↦ P.inj n ≫ h) (fun n ↦ by
    have : P.inj n ≫ (𝟙 _ - sequenceShift hP) ≫ h = 0 := by rw [hh, comp_zero]
    rw [Preadditive.sub_comp, Preadditive.comp_sub, id_comp, inj_sequenceShift_assoc,
      sub_eq_zero] at this
    simp [← this])

@[simp]
lemma coconeOfSubSequenceShift_ι_app {T : C} (h : P.pt ⟶ T)
    (hh : (𝟙 _ - sequenceShift hP) ≫ h = 0) (n : ℕ) :
    (coconeOfSubSequenceShift hP h hh).ι.app n = P.inj n ≫ h := rfl

variable {c : Cocone F} (hc : IsColimit c)

lemma id_sub_sequenceShift_comp_desc :
    (𝟙 P.pt - sequenceShift hP) ≫ Cofan.IsColimit.desc hP (fun n ↦ c.ι.app n) = 0 :=
  Cofan.IsColimit.hom_ext hP _ _ fun n ↦ by
    simp [Preadditive.comp_sub, Preadditive.sub_comp, Cofan.IsColimit.fac, c.w]

/-- The colimit of a sequence `F` is the cokernel of `1 - t : ∐ₙ Fₙ ⟶ ∐ₙ Fₙ`. -/
noncomputable def isColimitCokernelCoforkSubSequenceShift :
    IsColimit (CokernelCofork.ofπ (Cofan.IsColimit.desc hP (fun n ↦ c.ι.app n))
      (id_sub_sequenceShift_comp_desc hP)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun h hh ↦ hc.desc (coconeOfSubSequenceShift hP h hh))
    (fun h hh ↦ Cofan.IsColimit.hom_ext hP _ _ fun n ↦ by
      simp only [Cofan.IsColimit.fac_assoc, IsColimit.fac, coconeOfSubSequenceShift_ι_app])
    (fun h hh m hm ↦ hc.hom_ext fun n ↦ by
      simp only [IsColimit.fac, coconeOfSubSequenceShift_ι_app, ← hm,
        Cofan.IsColimit.fac_assoc])

end Cokernel

section PartialSum

variable [Preadditive C] [HasFiniteBiproducts C] (F : ℕ ⥤ C)

/-- The finite biproduct `⨁_{i ≤ N + k} Fᵢ`. -/
noncomputable abbrev partialSum (k N : ℕ) : C := ⨁ fun i : Fin (N + k + 1) ↦ F.obj i

/-- The inclusion `⨁_{i ≤ N + k} Fᵢ ⟶ ⨁_{i ≤ N + 1 + k} Fᵢ`. -/
noncomputable def partialSumStep (k N : ℕ) : partialSum F k N ⟶ partialSum F k (N + 1) :=
  biproduct.desc fun i ↦
    biproduct.ι (fun i : Fin (N + 1 + k + 1) ↦ F.obj i) ⟨i, by omega⟩

/-- The sequence `N ↦ ⨁_{i ≤ N + k} Fᵢ` of finite partial sums. -/
noncomputable def partialSumFunctor (k : ℕ) : ℕ ⥤ C :=
  Functor.ofSequence (partialSumStep F k)

lemma ι_partialSumFunctor_map (k : ℕ) {N M : ℕ} (h : N ≤ M) (i : ℕ) (hi : i < N + k + 1) :
    biproduct.ι (fun i : Fin (N + k + 1) ↦ F.obj i) ⟨i, hi⟩ ≫
        (partialSumFunctor F k).map (homOfLE h) =
      biproduct.ι (fun i : Fin (M + k + 1) ↦ F.obj i) ⟨i, by omega⟩ := by
  induction M, h using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
    have : homOfLE (hNM.trans M.le_succ) = homOfLE hNM ≫ homOfLE M.le_succ := rfl
    rw [this, Functor.map_comp, reassoc_of% ih]
    simp [partialSumFunctor, partialSumStep]

variable {P : Cofan fun n : ℕ ↦ F.obj n} (hP : IsColimit P)

/-- The cocone of the finite partial sums `⨁_{i ≤ N + k} Fᵢ` with point `∐ₙ Fₙ`. -/
@[simps pt]
noncomputable def partialSumCocone (k : ℕ) : Cocone (partialSumFunctor F k) where
  pt := P.pt
  ι := NatTrans.ofSequence (fun N ↦ biproduct.desc fun i ↦ P.inj (i : ℕ)) (fun N ↦ by
    refine biproduct.hom_ext' _ _ fun i ↦ ?_
    simp [partialSumFunctor, partialSumStep])

@[simp]
lemma partialSumCocone_ι_app (k N : ℕ) :
    (partialSumCocone F k (P := P)).ι.app N = biproduct.desc fun i ↦ P.inj (i : ℕ) := rfl

/-- `∐ₙ Fₙ` is the colimit of the finite partial sums `⨁_{i ≤ N + k} Fᵢ`. -/
noncomputable def isColimitPartialSumCocone (k : ℕ) : IsColimit (partialSumCocone F k (P := P)) where
  desc s := Cofan.IsColimit.desc hP fun n ↦
    biproduct.ι (fun i : Fin (n + k + 1) ↦ F.obj i) ⟨n, by omega⟩ ≫ s.ι.app n
  fac s N := by
    refine biproduct.hom_ext' _ _ fun i ↦ ?_
    obtain ⟨i, hi⟩ := i
    have h₁ := s.w (homOfLE (le_max_left i N))
    have h₂ := s.w (homOfLE (le_max_right i N))
    simp only [partialSumCocone_ι_app, biproduct.ι_desc_assoc, Cofan.IsColimit.fac]
    rw [← h₁, ← h₂, ι_partialSumFunctor_map_assoc, ι_partialSumFunctor_map_assoc]
  uniq s m hm := Cofan.IsColimit.hom_ext hP _ _ fun n ↦ by
    rw [Cofan.IsColimit.fac, ← hm, partialSumCocone_ι_app, biproduct.ι_desc_assoc]

/-- The map `⨁_{i ≤ N} Fᵢ ⟶ ⨁_{i ≤ N + 1} Fᵢ` induced by `1 - t`. -/
noncomputable def partialSumSubShift (N : ℕ) :
    (partialSumFunctor F 0).obj N ⟶ (partialSumFunctor F 1).obj N :=
  biproduct.desc fun i ↦
    biproduct.ι (fun i : Fin (N + 1 + 1) ↦ F.obj i) ⟨i, by omega⟩ -
      F.map (homOfLE (i : ℕ).le_succ) ≫
        biproduct.ι (fun i : Fin (N + 1 + 1) ↦ F.obj i) ⟨i + 1, by omega⟩

/-- The natural transformation `(⨁_{i ≤ N} Fᵢ)_N ⟶ (⨁_{i ≤ N + 1} Fᵢ)_N` induced by `1 - t`. -/
noncomputable def partialSumSubShiftNatTrans : partialSumFunctor F 0 ⟶ partialSumFunctor F 1 :=
  NatTrans.ofSequence (partialSumSubShift F) (fun N ↦ by
    refine biproduct.hom_ext' _ _ fun i ↦ ?_
    simp [partialSumFunctor, partialSumStep, partialSumSubShift, Preadditive.sub_comp])

lemma partialSumSubShift_π_zero (N : ℕ) :
    partialSumSubShift F N ≫ biproduct.π (fun i : Fin (N + 1 + 1) ↦ F.obj i) ⟨0, by omega⟩ =
      biproduct.π (fun i : Fin (N + 0 + 1) ↦ F.obj i) ⟨0, by omega⟩ := by
  refine biproduct.hom_ext' _ _ fun i ↦ ?_
  obtain ⟨i, hi⟩ := i
  rw [partialSumSubShift, biproduct.ι_desc_assoc, Preadditive.sub_comp, assoc,
    biproduct.ι_π_ne _ (j := ⟨i + 1, _⟩) (by simp [Fin.ext_iff]), comp_zero, sub_zero]
  rcases eq_or_ne i 0 with rfl | h
  · simp only [biproduct.ι_π_self]
  · rw [biproduct.ι_π_ne _ (by simp [Fin.ext_iff, h]),
      biproduct.ι_π_ne _ (by simp [Fin.ext_iff, h])]

lemma partialSumSubShift_π_succ (N j : ℕ) (hj : j + 1 < N + 1) :
    partialSumSubShift F N ≫ biproduct.π (fun i : Fin (N + 1 + 1) ↦ F.obj i) ⟨j + 1, by omega⟩ =
      biproduct.π (fun i : Fin (N + 0 + 1) ↦ F.obj i) ⟨j + 1, hj⟩ -
        biproduct.π (fun i : Fin (N + 0 + 1) ↦ F.obj i) ⟨j, by omega⟩ ≫
          F.map (homOfLE j.le_succ) := by
  refine biproduct.hom_ext' _ _ fun i ↦ ?_
  obtain ⟨i, hi⟩ := i
  rw [partialSumSubShift, biproduct.ι_desc_assoc, Preadditive.sub_comp, assoc,
    Preadditive.comp_sub]
  rcases eq_or_ne i (j + 1) with rfl | h₁
  · rw [biproduct.ι_π_self, biproduct.ι_π_self,
      biproduct.ι_π_ne_assoc _ (by simp [Fin.ext_iff]),
      biproduct.ι_π_ne _ (j' := (⟨j + 1, _⟩ : Fin (N + 1 + 1))) (by simp [Fin.ext_iff]),
      zero_comp, comp_zero, sub_zero, sub_zero]
  · rw [biproduct.ι_π_ne _ (by simp [Fin.ext_iff, h₁]),
      biproduct.ι_π_ne _ (by simp [Fin.ext_iff, h₁]), zero_sub, zero_sub]
    rcases eq_or_ne i j with rfl | h₂
    · simp only [biproduct.ι_π_self, id_comp]
      rfl
    · rw [biproduct.ι_π_ne _ (j' := (⟨j + 1, _⟩ : Fin (N + 1 + 1)))
        (by simp [Fin.ext_iff]; omega), biproduct.ι_π_ne_assoc _ (by simp [Fin.ext_iff, h₂]),
        comp_zero, zero_comp]

instance mono_partialSumSubShift (N : ℕ) : Mono (partialSumSubShift F N) where
  right_cancellation {T} g₁ g₂ hg := by
    rw [← sub_eq_zero, ← Preadditive.sub_comp] at hg
    rw [← sub_eq_zero]
    set g := g₁ - g₂
    have key : ∀ (j : ℕ) (hj : j < N + 0 + 1),
        g ≫ biproduct.π (fun i : Fin (N + 0 + 1) ↦ F.obj i) ⟨j, hj⟩ = 0 := by
      intro j
      induction j with
      | zero =>
        intro hj
        rw [← partialSumSubShift_π_zero, reassoc_of% hg, zero_comp]
      | succ j ih =>
        intro hj
        have := hg =≫ biproduct.π (fun i : Fin (N + 1 + 1) ↦ F.obj i) ⟨j + 1, by omega⟩
        rw [assoc, partialSumSubShift_π_succ F N j (by omega), Preadditive.comp_sub,
          reassoc_of% (ih (by omega)), zero_comp, sub_zero, zero_comp] at this
        exact this
    exact biproduct.hom_ext _ _ fun j ↦ by
      obtain ⟨j, hj⟩ := j
      rw [key j hj, zero_comp]

end PartialSum

section Abelian

variable [Abelian C] (F : ℕ ⥤ C) {P : Cofan fun n : ℕ ↦ F.obj n} (hP : IsColimit P)

/-- In an abelian category with exact colimits of shape `ℕ`, the map
`1 - t : ∐ₙ Fₙ ⟶ ∐ₙ Fₙ` is a monomorphism. -/
lemma mono_id_sub_sequenceShift [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C] :
    Mono (𝟙 P.pt - sequenceShift hP) := by
  have : Mono (partialSumSubShiftNatTrans F) := by
    have (N : ℕ) : Mono ((partialSumSubShiftNatTrans F).app N) :=
      mono_partialSumSubShift F N
    exact NatTrans.mono_of_mono_app _
  refine colim.map_mono' (partialSumSubShiftNatTrans F) (isColimitPartialSumCocone F hP 0)
    (isColimitPartialSumCocone F hP 1) _ fun N ↦ ?_
  refine biproduct.hom_ext' _ _ fun i ↦ ?_
  simp [partialSumSubShiftNatTrans, partialSumSubShift, Preadditive.comp_sub,
    Preadditive.sub_comp]

variable {c : Cocone F} (hc : IsColimit c)

/-- In an abelian category with exact colimits of shape `ℕ`, a sequence `F` gives a short exact
sequence `0 ⟶ ∐ₙ Fₙ ──1 - t──▶ ∐ₙ Fₙ ⟶ colim F ⟶ 0`. -/
lemma shortExact_sequenceShift [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C] :
    (ShortComplex.mk _ _ (id_sub_sequenceShift_comp_desc hP (c := c))).ShortExact :=
  have := mono_id_sub_sequenceShift F hP
  have : Epi (Cofan.IsColimit.desc hP fun n ↦ c.ι.app n) :=
    Cofork.IsColimit.epi (isColimitCokernelCoforkSubSequenceShift hP hc)
  { exact := ShortComplex.exact_of_g_is_cokernel _
      (isColimitCokernelCoforkSubSequenceShift hP hc) }

end Abelian

end CategoryTheory.Limits
