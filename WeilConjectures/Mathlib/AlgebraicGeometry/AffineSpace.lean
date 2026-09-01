/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Morphisms into the integral model of affine space

`AlgebraicGeometry.AffineSpace.toSpecMvPolyIntEquiv` identifies morphisms `Y ⟶ Spec ℤ[m]`
with families of global sections of `Y`. We record how it evaluates on a morphism that
factors through the spectrum of a ring:

- `AlgebraicGeometry.AffineSpace.toSpecMvPolyIntEquiv_comp_SpecMap`.
-/

@[expose] public section

universe u

open CategoryTheory MvPolynomial

namespace AlgebraicGeometry.AffineSpace

/-- The family of sections classifying a morphism `Y ⟶ Spec R ⟶ Spec ℤ[m]` is obtained by
evaluating the ring map `ℤ[m] ⟶ R` at the variables. -/
lemma toSpecMvPolyIntEquiv_comp_SpecMap {m : Type u} {Y : Scheme.{u}} {R : CommRingCat.{u}}
    (h : Y ⟶ Spec R) (ψ : CommRingCat.of (MvPolynomial m (ULift.{u} ℤ)) ⟶ R) (j : m) :
    toSpecMvPolyIntEquiv m (h ≫ Spec.map ψ) j =
      h.appTop ((Scheme.ΓSpecIso R).inv (ψ (MvPolynomial.X j))) := by
  rw [toSpecMvPolyIntEquiv_comp]
  congr 1
  rw [toSpecMvPolyIntEquiv_apply, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply]

end AlgebraicGeometry.AffineSpace
