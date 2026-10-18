/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additive functors preserve existing kernels from pre-triangulated categories

Source: Stacks Project, Derived Categories, Tag 05QU, lemma-when-split
(blueprint: lem-cor-int-compactness-ii-pretriangulated-kernel-split).
-/

@[expose] public section

universe u₁ v₁ u₂ v₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

namespace Functor

/--
An additive functor from a pre-triangulated category to a preadditive category
preserves every kernel that exists in its source.  The proof follows Stacks
Project, Tag 05QU: a kernel arrow is a split monomorphism, and the resulting
projection-coprojection decompositions are carried through the additive functor.
The factorization and uniqueness equations give the universal property of the
mapped kernel for an arbitrary target object.  The pre-triangulated source
provides the cone triangles and their rotation exactness; no kernel is assumed
to exist in the target (blueprint: lem-cor-int-compactness-ii-pretriangulated-kernel-split).
-/
theorem preservesKernel_of_pretriangulated
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive]
    {X Y K : C} (d : X ⟶ Y) (k : K ⟶ X) (hk : k ≫ d = 0)
    (hK : IsLimit (KernelFork.ofι k hk)) :
    Nonempty (IsLimit (KernelFork.ofι (f := F.map d) (F.map k) (by
      rw [← F.map_comp, hk, F.map_zero]))) := by
  classical
  have : Mono k := Fork.IsLimit.mono hK
  obtain ⟨Z, p, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle k
  have hz : h = 0 :=
    Pretriangulated.Triangle.mor₃_eq_zero_of_mono₁ _ hT (by
      dsimp only [Pretriangulated.Triangle.mk]
      infer_instance)
  obtain ⟨e, he₁, he₂⟩ :=
    Pretriangulated.exists_iso_binaryBiproduct_of_distTriang _ hT hz
  dsimp only [Pretriangulated.Triangle.mk] at e he₁ he₂
  let r : X ⟶ K := e.hom ≫ biprod.fst
  let s : Z ⟶ X := biprod.inr ≫ e.inv
  have hkr : k ≫ r = 𝟙 K := by
    simp [r, ← Category.assoc, he₁]
  have hkp : k ≫ p = 0 := by
    rw [he₂, ← Category.assoc, he₁, biprod.inl_snd]
  have hsp : s ≫ p = 𝟙 Z := by
    simp [s, he₂]
  have hrs : r ≫ k + p ≫ s = 𝟙 X := by
    apply (cancel_mono e.hom).1
    dsimp [r, s]
    simp only [Preadditive.add_comp, Category.assoc, he₁, Iso.inv_hom_id,
      Category.comp_id, Category.id_comp]
    rw [he₂, Category.assoc, ← Preadditive.comp_add, biprod.total, Category.comp_id]
  let g : Z ⟶ Y := s ≫ d
  have hd : d = p ≫ g := by
    have hh := congrArg (fun a : X ⟶ X ↦ a ≫ d) hrs
    simpa [g, Preadditive.add_comp, Category.assoc, hk] using hh.symm
  have : Mono g := by
    rw [Preadditive.mono_iff_cancel_zero]
    intro A a ha
    obtain ⟨b, hb⟩ := KernelFork.IsLimit.lift' hK (a ≫ s) (by
      simpa [g, Category.assoc] using ha)
    have hh := congrArg (fun q : A ⟶ X ↦ q ≫ p) hb
    simpa [Category.assoc, hsp, hkp] using hh.symm
  have : IsSplitMono g := isSplitMono_of_mono g
  let t : Y ⟶ Z := retraction g
  have hgt : g ≫ t = 𝟙 Z := IsSplitMono.id g
  have hdt : d ≫ t = p := by
    rw [hd, Category.assoc, hgt, Category.comp_id]
  have hFkr : F.map k ≫ F.map r = 𝟙 (F.obj K) := by
    rw [← F.map_comp, hkr, F.map_id]
  have hFrs : F.map r ≫ F.map k + F.map p ≫ F.map s = 𝟙 (F.obj X) := by
    rw [← F.map_comp, ← F.map_comp, ← F.map_add, hrs, F.map_id]
  refine ⟨KernelFork.IsLimit.ofι (F.map k) _
    (fun a _ ↦ a ≫ F.map r) ?_ ?_⟩
  · intro A a ha
    have hap : a ≫ F.map p = 0 := by
      rw [← hdt, F.map_comp, ← Category.assoc, ha, zero_comp]
    calc
      (a ≫ F.map r) ≫ F.map k = a ≫
          (F.map r ≫ F.map k + F.map p ≫ F.map s) := by
        simp [Preadditive.comp_add, ← Category.assoc, hap]
      _ = a := by rw [hFrs, Category.comp_id]
  · intro A a ha m hm
    rw [← hm, Category.assoc, hFkr, Category.comp_id]

end Functor

end CategoryTheory
