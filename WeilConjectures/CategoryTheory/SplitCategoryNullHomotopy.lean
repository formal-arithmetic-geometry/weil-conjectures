/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Homotopy

/-! # Null homotopies in a split abelian category
-/

@[expose] public section
set_option autoImplicit false

open CategoryTheory Limits

namespace CochainComplex

/-- A map inducing zero on homology in a split abelian category is null homotopic. -/
theorem nonempty_nullHomotopy_of_homologyMap_zero
    {C : Type*} [Category* C] [Abelian C]
    [∀ X : C, Projective X] [∀ X : C, Injective X]
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hf : ∀ q : ℤ, HomologicalComplex.homologyMap f q = 0) :
    Nonempty (Homotopy f 0) := by
  classical
  let r (i : ℤ) := Injective.factorThru (𝟙 (K.cycles i)) (K.iCycles i)
  have hr (i : ℤ) : K.iCycles i ≫ r i = 𝟙 _ := by simp [r]
  have ht (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel j i) :
      ∃ t : K.cycles i ⟶ L.X j, t ≫ L.d j i = K.iCycles i ≫ f.f i := by
    let S := ShortComplex.mk (L.toCycles j i) (L.homologyπ i)
      (L.toCycles_comp_homologyπ j i)
    have hS : S.Exact := S.exact_of_g_is_cokernel
      (L.homologyIsCokernel j i ((ComplexShape.up ℤ).prev_eq' hij))
    have hz : HomologicalComplex.cyclesMap f i ≫ L.homologyπ i = 0 := by
      rw [← HomologicalComplex.homologyπ_naturality, hf, comp_zero]
    let t := hS.liftFromProjective (HomologicalComplex.cyclesMap f i) hz
    refine ⟨t, ?_⟩
    rw [← L.toCycles_i j i, ← Category.assoc]
    exact (congrArg (fun k ↦ k ≫ L.iCycles i)
      (hS.liftFromProjective_comp (HomologicalComplex.cyclesMap f i) hz)).trans
      (HomologicalComplex.cyclesMap_i f i)
  choose t ht using ht
  let T := Homotopy.nullHomotopicMap'
    (fun i j hij ↦ r i ≫ t i j hij)
  have hT (i : ℤ) : K.iCycles i ≫ T.f i = K.iCycles i ≫ f.f i := by
    rw [Homotopy.nullHomotopicMap'_f (by simp :
      (ComplexShape.up ℤ).Rel (i - 1) i) (by simp :
      (ComplexShape.up ℤ).Rel i (i + 1))]
    simp only [Preadditive.comp_add, ← Category.assoc, K.iCycles_d,
      zero_comp, zero_add, hr, Category.id_comp, ht]
  let g := f - T
  have hg (i : ℤ) : K.iCycles i ≫ g.f i = 0 := by
    simp only [g, HomologicalComplex.sub_f_apply, Preadditive.comp_sub, hT, sub_self]
  have hgd (i j : ℤ) : g.f i ≫ L.d i j = 0 := by
    rw [g.comm, ← K.toCycles_i i j, Category.assoc, hg, comp_zero]
  have hu (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
      ∃ u : K.X j ⟶ K.X i, K.d i j ≫ u = 𝟙 _ - r i ≫ K.iCycles i := by
    let S := ShortComplex.mk (K.iCycles i) (K.d i j) (K.iCycles_d i j)
    have hS : S.Exact := S.exact_of_f_is_kernel
      (K.cyclesIsKernel i j ((ComplexShape.up ℤ).next_eq' hij))
    have hz : K.iCycles i ≫ (𝟙 _ - r i ≫ K.iCycles i) = 0 := by
      simp only [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hr,
        Category.id_comp, sub_self]
    exact ⟨hS.descToInjective _ hz, hS.comp_descToInjective _ hz⟩
  choose u hu using hu
  let U := Homotopy.nullHomotopicMap'
    (fun i j hij ↦ u j i hij ≫ g.f j)
  have hU : U = g := by
    apply HomologicalComplex.Hom.ext
    funext i
    rw [Homotopy.nullHomotopicMap'_f (by simp :
      (ComplexShape.up ℤ).Rel (i - 1) i) (by simp :
      (ComplexShape.up ℤ).Rel i (i + 1))]
    simp only [Category.assoc, hgd, comp_zero, add_zero]
    rw [← Category.assoc, hu, Preadditive.sub_comp, Category.id_comp,
      Category.assoc, hg, comp_zero, sub_zero]
  have h := (Homotopy.nullHomotopy'
    (fun i j hij ↦ r i ≫ t i j hij)).add
    (Homotopy.nullHomotopy' (fun i j hij ↦ u j i hij ≫ g.f j))
  refine ⟨?_⟩
  convert h using 1
  · change f = T + U
    rw [hU]
    dsimp [g]
    abel
  · simp

end CochainComplex
