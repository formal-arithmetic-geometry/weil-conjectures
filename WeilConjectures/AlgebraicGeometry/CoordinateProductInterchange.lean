/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateProductPresentations
import WeilConjectures.AlgebraicGeometry.CoordinateShiftedLineSymmetry
import WeilConjectures.AlgebraicGeometry.CoordinateProductConsCompatibility
import WeilConjectures.AlgebraicGeometry.CoordinateProductHeadInterchange

/-! # Interchanging two coordinate factors -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

/-- Interchanging two labels in an enumerated coordinate product preserves its actual map.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, ordered exterior product of rank-one
classes; parent proof Step 10 (blueprint: lem-pur-coordinate-product-interchange).

Proof: use List.Perm induction on the two enumerations. Reflexivity and
transitivity are supplied by the normalized support comparisons. Prepending a
common coordinate preserves comparison; exchanging the first two coordinates
uses the local three-factor calculation and identity self-braiding of the
shifted Tate line. Both mapped finite ranges are permutations of finRange, so
the induction gives agreement on their literal supports. The unique support
isomorphisms over the zero section then give equality of the normalized maps. -/
theorem coordinate_product_interchange (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ)
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    (σ : Equiv.Perm (Fin c)) (i j : Fin c) (hij : i ≠ j) :
    permutedClass P n B aB c (Equiv.swap i j * σ) = permutedClass P n B aB c σ := by
  classical
  by_cases h : i = j
  · exact (hij h).elim
  have hb := coordinate_shifted_line_self_braiding P n (iteratedAffineLine B c)
    (towerBase aB c)
  have invariant {is js : List (Fin c)} (h : is.Perm js) :
      CoordinateProductsAgree P n B aB c is js := by
    induction h with
    | nil => exact CoordinateProductsAgree.refl P n B aB c []
    | cons i h ih => exact coordinate_product_cons_compatibility P n B aB c i ih
    | swap i j is => exact coordinate_product_head_interchange P n B aB c j i is hb
    | trans h₁ h₂ ih₁ ih₂ =>
      exact CoordinateProductsAgree.trans P n B aB c ih₁ ih₂
  exact CoordinateProductsAgree.permutedClass_eq P n B aB c _ _
    (invariant (((Equiv.swap i j * σ).map_finRange_perm).trans σ.map_finRange_perm.symm))

end AlgebraicGeometry.ProEtale.AffineZeroPurity
