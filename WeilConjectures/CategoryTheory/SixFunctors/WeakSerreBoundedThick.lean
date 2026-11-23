/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import Mathlib.CategoryTheory.ObjectProperty.Retract
import WeilConjectures.CategoryTheory.SmoothBaseChange.CohomologyInWeakSerreSubcategory

/-!
# Bounded cohomology in a weak Serre class is thick

Source: Stacks Project, Tag 06UQ, including
bounded versions; Homology, Tag 0754.
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Bounded derived objects with cohomology in a weak Serre class form a thick subcategory.
For each ambient retract, its cohomology inclusion is the kernel inclusion of one minus
its cohomological idempotent, and every interval bound passes to the retract unchanged.

Source: Stacks Project, Tag 06UQ (bounded and
saturated versions), and Tag 0754. -/
lemma weakSerre_bounded_homology_thick
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions] :
    (DerivedCategory.homologyProperty P ⊓ DerivedCategory.TStructure.t.bounded).IsTriangulated ∧
    (DerivedCategory.homologyProperty P ⊓
      DerivedCategory.TStructure.t.bounded).IsStableUnderRetracts ∧
    (∀ (L K : DerivedCategory A) (i : L ⟶ K) (r : K ⟶ L), i ≫ r = 𝟙 L →
      (DerivedCategory.homologyProperty P ⊓ DerivedCategory.TStructure.t.bounded) K →
      (∀ n : ℤ, ∃ e : (DerivedCategory.homologyFunctor A n).obj L ≅
          kernel (𝟙 ((DerivedCategory.homologyFunctor A n).obj K) -
            (DerivedCategory.homologyFunctor A n).map r ≫
              (DerivedCategory.homologyFunctor A n).map i),
        e.hom ≫ kernel.ι (𝟙 ((DerivedCategory.homologyFunctor A n).obj K) -
          (DerivedCategory.homologyFunctor A n).map r ≫
            (DerivedCategory.homologyFunctor A n).map i) =
          (DerivedCategory.homologyFunctor A n).map i) ∧
      (∀ a b : ℤ,
        (∀ n : ℤ, n < a ∨ b < n → IsZero ((DerivedCategory.homologyFunctor A n).obj K)) →
        ∀ n : ℤ, n < a ∨ b < n → IsZero ((DerivedCategory.homologyFunctor A n).obj L))) := by
  have kernel_iso {M N : A} (e : Retract M N) :
      ∃ φ : M ≅ kernel (𝟙 N - e.r ≫ e.i),
        φ.hom ≫ kernel.ι (𝟙 N - e.r ≫ e.i) = e.i := by
    let q : N ⟶ N := 𝟙 N - e.r ≫ e.i
    have hi : e.i ≫ q = 0 := by
      simp [q, Preadditive.comp_sub, ← Category.assoc]
    have hk : kernel.ι q ≫ e.r ≫ e.i = kernel.ι q := by
      have h := kernel.condition q
      change kernel.ι q ≫ (𝟙 N - e.r ≫ e.i) = 0 at h
      rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at h
      exact h.symm
    refine ⟨{
      hom := kernel.lift q e.i hi
      inv := kernel.ι q ≫ e.r
      hom_inv_id := by simp
      inv_hom_id := (cancel_mono (kernel.ι q)).1 (by simpa using hk)
    }, ?_⟩
    exact kernel.lift_ι q e.i hi
  refine ⟨(cohomology_in_weak_serre_subcategory P).2.2, ⟨?_⟩, ?_⟩
  · intro L K e hK
    constructor
    · intro n
      obtain ⟨φ, -⟩ := kernel_iso (e.map (DerivedCategory.homologyFunctor A n))
      exact P.prop_of_iso φ.symm (P.prop_kernel _ (hK.1 n) (hK.1 n))
    · obtain ⟨a, b, hab⟩ :=
        (DerivedCategory.exists_homologyConcentratedIn_iff_bounded K).2 hK.2
      exact (DerivedCategory.exists_homologyConcentratedIn_iff_bounded L).1
        ⟨a, b, (DerivedCategory.homologyConcentratedIn a b).prop_of_retract e hab⟩
  · intro L K i r hir _
    let e : Retract L K := ⟨i, r, hir⟩
    refine ⟨fun n ↦ kernel_iso (e.map (DerivedCategory.homologyFunctor A n)), ?_⟩
    intro a b hK n hn
    rw [IsZero.iff_id_eq_zero]
    rw [← (e.map (DerivedCategory.homologyFunctor A n)).retract,
      (hK n hn).eq_of_tgt (e.map (DerivedCategory.homologyFunctor A n)).i 0, zero_comp]

end CategoryTheory
