/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# The affine chart of the subscheme of an ideal sheaf

The square with the chart `Spec (Γ(X, U) ⧸ I(U)) ⟶ 𝒪ₓ/I` of the subscheme of a
quasi-coherent ideal `I` over an affine open `U` and `fromSpec` is a pullback.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The affine chart of the subscheme over an affine open is the fibre product: the
square with the chart `Spec (Γ(X, U) ⧸ I(U)) ⟶ 𝒪ₓ/I` and `fromSpec` is a pullback. -/
lemma isPullback_subschemeCover_f (I : X.IdealSheafData) (U : X.affineOpens) :
    IsPullback (I.subschemeCover.f U)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))))
      I.subschemeι U.2.fromSpec := by
  refine (IsOpenImmersion.isPullback _ _ _ _ ?_ ?_).flip
  · exact (I.subschemeCover_map_subschemeι U).trans (I.glueDataObjι_ι U)
  · rw [U.2.opensRange_fromSpec, Scheme.IdealSheafData.opensRange_subschemeCover_map]

end AlgebraicGeometry
