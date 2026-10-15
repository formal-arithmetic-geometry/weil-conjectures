/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.CategoryTheory.ExactCoupleConvergence

import Sheaf.CategoryTheory.DerivedCoupleExact
import WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits

/-! # Finite-tail limiting subobjects

Source: Stacks Project, Tag 011T, exact-couple cycle and boundary formulas.
(blueprint: lem-sp-finite-cocone-limit-cycles)
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory.BigradedExactCouple

/-- An upper zero tail identifies the limiting cycles with the initial g image.
Source: Stacks Project, Tag 011T, formula for cycles; Tag 012W, upper-tail argument.
(blueprint: lem-sp-finite-cocone-limit-cycles).

Proof: Use the recursive image and mono inclusion families of pageCouple_image_prefix.
Induct on r to show that the finite cycle projection followed by page f and
its D inclusion equals the finite cycle inclusion followed by the original f.
The base is projection_zero. For the successor use projection_succ,
DerivedMaps.f_comm, cycleLift_comm and the preceding induction equation.
Choose r beyond the upper bound on total degree p+q+1 (and beyond a regularity
bound). The source of the original incoming r-fold alpha map at (p+2,q-1)
is zero. Its image, hence the image of the mono D inclusion, is zero; the
inclusion itself is zero. The projection equation now makes original f vanish
on Z_r. Since L.Z is below Z_r by its GLB property, original f vanishes on L.Z.
Exactness identifies ker f with image initialG, using the canonical type-zero
transport and naturality of f. Thus L.Z is contained in image initialG.
Conversely, g_factors_limitCycles places image initialG below L.Z. The two
inequalities prove equality without a general finite-cycle formula. -/
theorem finiteCocone_limitCycles
    {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0) (L : X.LimitSubobjects) (hreg : X.IsRegular)
    (hzero : ∀ n : ℤ, ∃ b : ℤ, ∀ P : ℤ, b ≤ P → IsZero (X.D P (n - P)))
    (p q : ℤ) : L.Z p q = imageSubobject (X.initialG p q) := by
  obtain ⟨α, I, _, _, hI0, hIs, hmono, himage, _⟩ := pageCouple_image_prefix X
  let T := X.cycleBoundaryTower
  have hcomm (r : ℕ) : T.projection r p q ≫ (X.pageCouple r).f p q ≫
      I r (p + 2) (q - 1) = (T.Z r p q).arrow ≫ X.f p q := by
    induction r with
    | zero => simp only [hI0, T.projection_zero, pageCouple, Category.comp_id]
    | succ r ih =>
      let Y := X.pageCouple r
      let M := Classical.choice Y.derivedMaps_exists
      have hf : Y.derivedEProjection p q ≫ (X.pageCouple (r + 1)).f p q ≫
          Y.derivedDInclusion (p + 2) (q - 1) = kernel.ι (Y.d p q) ≫ Y.f p q :=
        M.f_comm p q
      rw [T.projection_succ, hIs]
      calc
        (T.cycleLift r p q ≫ Y.derivedEProjection p q) ≫
            (X.pageCouple (r + 1)).f p q ≫
              Y.derivedDInclusion (p + 2) (q - 1) ≫ I r (p + 2) (q - 1) =
            T.cycleLift r p q ≫ (kernel.ι (Y.d p q) ≫ Y.f p q) ≫
              I r (p + 2) (q - 1) := by
          simpa only [Category.assoc] using congrArg
            (fun z ↦ T.cycleLift r p q ≫ z ≫ I r (p + 2) (q - 1)) hf
        _ = (T.Z (r + 1) p q).arrow ≫ X.f p q := by
          calc
            T.cycleLift r p q ≫ (kernel.ι (Y.d p q) ≫ Y.f p q) ≫
                I r (p + 2) (q - 1) =
                (T.cycleLift r p q ≫ kernel.ι (Y.d p q)) ≫
                  Y.f p q ≫ I r (p + 2) (q - 1) := by simp only [Category.assoc]
            _ = Subobject.ofLE _ _ (T.Z_decreasing r p q) ≫
                (T.projection r p q ≫ (X.pageCouple r).f p q ≫
                  I r (p + 2) (q - 1)) := by
              rw [T.cycleLift_comm]
              simp only [Category.assoc]
              rfl
            _ = (T.Z (r + 1) p q).arrow ≫ X.f p q := by
              rw [ih, Subobject.ofLE_arrow_assoc]
  obtain ⟨b, hb⟩ := hzero (p + q + 1)
  obtain ⟨r₀, _⟩ := hreg p q
  let r := max r₀ (b - p - 2).toNat
  have hr : b ≤ p + 2 + (r : ℤ) := by dsimp [r]; omega
  have hsrc : IsZero (X.D (p + 2 + (r : ℤ)) (q - 1 - (r : ℤ))) := by
    convert hb (p + 2 + r) hr using 1
    congr 1
    omega
  have := hmono r (p + 2) (q - 1)
  have hI : I r (p + 2) (q - 1) = 0 := by
    apply Subobject.mk_eq_bot_iff_zero.mp
    rw [← imageSubobject_mono, himage, hsrc.eq_zero_of_src (α r (p + 2) (q - 1)),
      imageSubobject_zero]
  have hZf : (T.Z r p q).arrow ≫ X.f p q = 0 := by
    rw [← hcomm r, hI, comp_zero, comp_zero]
  have hLf : (L.Z p q).arrow ≫ X.f p q = 0 := by
    rw [← Subobject.ofLE_arrow ((L.Z_glb p q).1 ⟨r, rfl⟩), Category.assoc,
      hZf, comp_zero]
  have hg : imageSubobject (X.initialG p q) = kernelSubobject (X.f p q) := by
    let e := eqToIso (show X.E (p + (0 : ℕ)) (q - (0 : ℕ)) = X.E p q by
      congr 1 <;> omega)
    have hn := eqToHom_naturality (fun pq : ℤ × ℤ ↦ X.f pq.1 pq.2)
      (show (p + (0 : ℕ), q - (0 : ℕ)) = (p, q) by ext <;> omega)
    change X.f (p + (0 : ℕ)) (q - (0 : ℕ)) ≫ eqToHom _ = e.hom ≫ X.f p q at hn
    have hk : (Subobject.pullback e.hom).obj (kernelSubobject (X.f p q)) =
        kernelSubobject (X.f (p + (0 : ℕ)) (q - (0 : ℕ))) := by
      apply le_antisymm
      · apply le_kernelSubobject
        have hw := (Subobject.isPullback e.hom (kernelSubobject (X.f p q))).w
        have hz : ((Subobject.pullback e.hom).obj (kernelSubobject (X.f p q))).arrow ≫
            e.hom ≫ X.f p q = 0 := by
          rw [← Category.assoc, ← hw, Category.assoc, kernelSubobject_arrow_comp, comp_zero]
        rw [← hn, ← Category.assoc] at hz
        exact (cancel_mono (eqToHom _)).mp (by simpa only [zero_comp] using hz)
      · apply Subobject.le_of_factors
        apply pullback_factors
        apply kernelSubobject_factors
        rw [Category.assoc, ← hn, ← Category.assoc, kernelSubobject_arrow_comp, zero_comp]
    have hm : imageSubobject (X.initialG p q) =
        (Subobject.«exists» e.hom).obj (imageSubobject (X.g p q)) := by
      rw [Subobject.exists_obj_eq_imageSubobject,
        ← imageSubobject_comp_of_epi (factorThruImageSubobject (X.g p q)),
        imageSubobject_arrow_comp_assoc]
      rfl
    rw [hm, X.exact_f, ← hk, Subobject.exists_obj_pullback_obj]
  apply le_antisymm
  · rw [hg]
    exact le_kernelSubobject _ _ hLf
  · exact (Subobject.imageSubobject_le_iff _ _).mpr (g_factors_limitCycles X L p q)

end CategoryTheory.BigradedExactCouple
