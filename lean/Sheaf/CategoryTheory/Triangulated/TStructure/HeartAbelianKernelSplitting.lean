/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.Heart

/-!
# Abelian hearts and supplementary kernels of idempotents

Source: BBD, Theorem 1.3.6 and Proposition 1.2.4; Stacks Project, Tag 0H9Q
(blueprint: prop-weil-heart-abelian).
-/

@[expose] public section

universe u v u' v'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Triangulated.TStructure

/-- The heart is abelian; in any abelian category an idempotent is the projection onto
`ker(1-e)` in the decomposition `ker(e) ⊞ ker(1-e)`.
Source: BBD, Theorem 1.3.6 and Proposition 1.2.4; Stacks Project, Tag 0H9Q
(blueprint: prop-weil-heart-abelian).

Proof plan: extension closure (`lem-sbc-tstructure-extension-closure`) puts the zero
object and, using the split distinguished triangle
(`lem-sbc-biproduct-triangle-distinguished`), binary biproducts in the heart. The
inclusion is full, faithful and additive. Shift stability and orthogonality in
`def-weil-t-structure` imply that negative shifted Hom groups between heart objects
vanish. Complete a heart morphism to a distinguished triangle (`def-weil-triangulated-category`);
its cone lies in degrees [-1,0]. Truncate that cone at (-1,0), obtaining a triangle
`K[1] → S → Q → K[2]` with K and Q in the heart, by extension closure and shift
stability. Apply `lem-sbc-abelian-subcategory-criterion` to obtain abelianity
(`def-sp-abelian`); this is also the existing upstream `abelianHeart` theorem.

For the supplementary assertion put g = 1-e. The identities eg = ge = 0 give
maps p : A → ker(e) and q : A → ker(g), whose composites with the kernel
inclusions i and j are g and e. Monicity gives i ≫ p = 1, j ≫ q = 1 and the
cross composites zero. Thus the maps (i,j) and (p,q) are inverse, because
g+e=1. The identities i ≫ e = 0 and j ≫ e = j identify e with the second
projection. This applies in particular to the abelian heart. -/
theorem heart_abelian_and_idempotent_kernel_decomposition
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C] (t : TStructure C) :
    Nonempty (Abelian t.heart.FullSubcategory) ∧
      ∀ (D : Type u') [Category.{v'} D] [Abelian D] (A : D) (e : A ⟶ A),
        e ≫ e = e →
          ∃ φ : A ≅ (kernel e ⊞ kernel (𝟙 A - e)),
            φ.inv = biprod.desc (kernel.ι e) (kernel.ι (𝟙 A - e)) ∧
              φ.inv ≫ e ≫ φ.hom = biprod.snd ≫ biprod.inr := by
  constructor
  · let := t.hasHeartFullSubcategory
    exact ⟨t.abelianHeart t.heart.FullSubcategory⟩
  · intro D _ _ A e he
    let g := 𝟙 A - e
    have hge : g ≫ e = 0 := by
      simp [g, Preadditive.sub_comp, he]
    have heg : e ≫ g = 0 := by
      simp [g, Preadditive.comp_sub, he]
    let p := kernel.lift e g hge
    let q := kernel.lift g e heg
    have hj : kernel.ι g ≫ e = kernel.ι g := by
      have h := kernel.condition g
      dsimp [g] at h ⊢
      simp only [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at h
      exact h.symm
    have hip : kernel.ι e ≫ p = 𝟙 _ := by
      apply (cancel_mono (kernel.ι e)).1
      simp [p, Category.assoc, g, Preadditive.comp_sub]
    have hiq : kernel.ι e ≫ q = 0 := by
      apply (cancel_mono (kernel.ι g)).1
      simp [q, Category.assoc]
    have hjp : kernel.ι g ≫ p = 0 := by
      apply (cancel_mono (kernel.ι e)).1
      simp [p, Category.assoc]
    have hjq : kernel.ι g ≫ q = 𝟙 _ := by
      apply (cancel_mono (kernel.ι g)).1
      simp [q, Category.assoc, hj]
    let φ : A ≅ kernel e ⊞ kernel g :=
      { hom := biprod.lift p q
        inv := biprod.desc (kernel.ι e) (kernel.ι g)
        hom_inv_id := by
          simp [biprod.lift_desc, p, q, g]
        inv_hom_id := by
          apply biprod.hom_ext' <;> apply biprod.hom_ext
          · simp [Category.assoc, hip]
          · simp [Category.assoc, hiq]
          · simp [Category.assoc, hjp]
          · simp [Category.assoc, hjq] }
    refine ⟨φ, rfl, ?_⟩
    have hφ : biprod.desc (kernel.ι e) (kernel.ι g) ≫ e =
        biprod.snd ≫ kernel.ι g := by
      apply biprod.hom_ext'
      · simp
      · simpa using hj
    have hjlift : kernel.ι g ≫ biprod.lift p q =
        (biprod.inr : kernel g ⟶ kernel e ⊞ kernel g) := by
      apply biprod.hom_ext
      · simp [Category.assoc, hjp]
      · simp [Category.assoc, hjq]
    change biprod.desc (kernel.ι e) (kernel.ι g) ≫ e ≫ biprod.lift p q =
      (biprod.snd : kernel e ⊞ kernel g ⟶ kernel g) ≫ biprod.inr
    rw [← Category.assoc, hφ, Category.assoc, hjlift]

end CategoryTheory.Triangulated.TStructure
