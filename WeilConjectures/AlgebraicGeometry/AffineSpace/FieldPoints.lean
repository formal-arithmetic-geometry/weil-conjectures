/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Weil.Definitions

/-!
# Rational points of the affine line

For a field extension `L` of `k`, the `L`-rational points of the affine line `𝔸¹_k` are the
elements of `L`: a point `x : Spec L ⟶ 𝔸¹_k` over `k` is determined by the value of the
coordinate function at `x`.

## Main definitions

- `AlgebraicGeometry.AffineSpace.fieldPointsEquiv`: `𝔸¹_k(L) ≃ L`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.AffineSpace

variable (k : Type u) [Field k] (L : Type u) [Field L] [Algebra k L]

/-- The `L`-rational points of the affine line `𝔸¹_k` over `k` are the elements of `L`: a point
`x : Spec L ⟶ 𝔸¹_k` corresponds to the value `x^*(t) ∈ Γ(Spec L, 𝒪) = L` of the coordinate
`t`. -/
noncomputable def fieldPointsEquiv :
    (𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)).fieldPoints L ≃ L where
  toFun x := (Scheme.ΓSpecIso (.of L)).hom.hom (x.1.appTop (coord _ PUnit.unit))
  invFun a := ⟨homOfVector (Spec.map (CommRingCat.ofHom (algebraMap k L)))
    fun _ ↦ (Scheme.ΓSpecIso (.of L)).inv.hom a, homOfVector_over _ _⟩
  left_inv x := by
    refine Subtype.ext (hom_ext ?_ fun i ↦ ?_)
    · rw [homOfVector_over, x.2]
    · rw [homOfVector_appTop_coord, ← CommRingCat.comp_apply, Iso.hom_inv_id,
        CommRingCat.id_apply]
  right_inv a := by
    change (Scheme.ΓSpecIso (.of L)).hom.hom ((homOfVector _ _).appTop (coord _ _)) = a
    rw [homOfVector_appTop_coord, ← CommRingCat.comp_apply, Iso.inv_hom_id,
      CommRingCat.id_apply]

lemma fieldPointsEquiv_apply
    (x : (𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)).fieldPoints L) :
    fieldPointsEquiv k L x = (Scheme.ΓSpecIso (.of L)).hom.hom (x.1.appTop (coord _ PUnit.unit)) :=
  rfl

end AlgebraicGeometry.AffineSpace
