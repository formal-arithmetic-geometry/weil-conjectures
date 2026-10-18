/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.CategoryTheory.ExactCoupleConvergence

import WeilConjectures.CategoryTheory.DerivedCoupleExact
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
  obtain ⟨A, I, _, _, hI0, hIs, hImono, hIm, _⟩ := X.pageCouple_image_prefix
  let T := X.cycleBoundaryTower
  have hcomm : ∀ r : ℕ,
      T.projection r p q ≫ (X.pageCouple r).f p q ≫ I r (p + 2) (q - 1) =
        (T.Z r p q).arrow ≫ X.f p q := by
    intro r
    induction r with
    | zero =>
      simp only [hI0, T.projection_zero, pageCouple, Category.comp_id]
    | succ r ih =>
      let Y := X.pageCouple r
      let M := Classical.choice Y.derivedMaps_exists
      have hf : Y.derivedEProjection p q ≫ (X.pageCouple (r + 1)).f p q ≫
          Y.derivedDInclusion (p + 2) (q - 1) =
            kernel.ι (Y.d p q) ≫ Y.f p q := M.f_comm p q
      rw [T.projection_succ, hIs]
      calc
        _ = T.cycleLift r p q ≫ (kernel.ι (Y.d p q) ≫ Y.f p q) ≫
            I r (p + 2) (q - 1) := by
          simpa only [Category.assoc] using congrArg
            (fun z ↦ T.cycleLift r p q ≫ z ≫ I r (p + 2) (q - 1)) hf
        _ = Subobject.ofLE _ _ (T.Z_decreasing r p q) ≫
            (T.projection r p q ≫ (X.pageCouple r).f p q ≫
              I r (p + 2) (q - 1)) := by
          simpa only [Category.assoc] using congrArg
            (fun z ↦ z ≫ (X.pageCouple r).f p q ≫ I r (p + 2) (q - 1))
            (T.cycleLift_comm r p q)
        _ = _ := by rw [ih, Subobject.ofLE_arrow_assoc]
  obtain ⟨b, hb⟩ := hzero (p + q + 1)
  obtain ⟨s, _⟩ := hreg p q
  let r : ℕ := max s (b - (p + 2)).toNat
  have hr : b ≤ p + 2 + (r : ℤ) := by
    have h₁ := Nat.le_max_right s (b - (p + 2)).toNat
    dsimp only [r]
    omega
  have hz : IsZero (X.D (p + 2 + (r : ℤ)) (q - 1 - (r : ℤ))) := by
    convert hb (p + 2 + (r : ℤ)) hr using 1
    congr 1
    omega
  have hAz : A r (p + 2) (q - 1) = 0 := hz.eq_of_src _ _
  have := hImono r (p + 2) (q - 1)
  have hIz : I r (p + 2) (q - 1) = 0 := by
    apply Subobject.mk_eq_bot_iff_zero.mp
    rw [← imageSubobject_mono, hIm, hAz, imageSubobject_zero]
  have hfinite : (T.Z r p q).arrow ≫ X.f p q = 0 := by
    rw [← hcomm r, hIz, comp_zero, comp_zero]
  have hle : L.Z p q ≤ T.Z r p q := (L.Z_glb p q).1 ⟨r, rfl⟩
  have hlimit : (L.Z p q).arrow ≫ X.f p q = 0 := by
    rw [← Subobject.ofLE_arrow hle, Category.assoc, hfinite, comp_zero]
  have hexact : imageSubobject (X.initialG p q) = kernelSubobject (X.f p q) := by
    have aux (a b : ℤ) (ha : p + (0 : ℕ) = a) (hb : q - (0 : ℕ) = b) :
        imageSubobject (X.g p q ≫ eqToHom (congrArg₂ X.E ha hb)) =
          kernelSubobject (X.f a b) := by
      subst a b
      simpa only [eqToHom_refl, Category.comp_id] using X.exact_f p q
    exact aux p q (by omega) (by omega)
  apply le_antisymm
  · rw [hexact]
    exact le_kernelSubobject (X.f p q) _ hlimit
  · exact (Subobject.imageSubobject_le_iff _ _).mpr (X.g_factors_limitCycles L p q)

end CategoryTheory.BigradedExactCouple
