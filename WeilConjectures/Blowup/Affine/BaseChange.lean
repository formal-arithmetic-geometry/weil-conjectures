/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Blowup.Affine.BaseChangeSurjectivity

/-!

# The blow-up of an extended ideal is a closed subscheme of the base change

Let `φ : A →+* B` be a ring homomorphism, `I ⊆ A` an ideal and `J = I·B` its extension.
The blow-up of `J` maps to the fibre product `Spec B ×_{Spec A} Bl_I(Spec A)` via its
structure morphism and the functoriality morphism `AlgebraicGeometry.AffineBlowup.hom`.
We show that this canonical morphism is a **closed immersion** (the affine core of
Stacks Project Tag 080E).

The proof is chart-local on the fibre product: over the standard chart of `Bl_I` at a
degree-one element `x`, the morphism restricts to the `Spec` of the canonical ring map
`B ⊗_A A[I/x] →+* B[J/φ(x)]`, which is surjective by
`AlgebraicGeometry.AffineBlowup.closure_range_awayAlgebraMap_union_range_awayMap`.

## Main results

- `AlgebraicGeometry.AffineBlowup.isClosedImmersion_pullbackLift`

## Blueprint

Part of `thm:nagata-strict-transform-is-blowup` (Stacks Project Tag 080E), affine case.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.AffineBlowup

variable {A B : Type u} [CommRing A] [CommRing B] {I : Ideal A} {J : Ideal B}

/-- **The blow-up of an extended ideal is a closed subscheme of the base-changed
blow-up**, affine case (Stacks Project Tag 080E; blueprint:
`thm:nagata-strict-transform-is-blowup`): for a ring homomorphism `φ : A →+* B` with
`I.map φ = J`, the canonical morphism
`Bl_J(Spec B) ⟶ Spec B ×_{Spec A} Bl_I(Spec A)`, whose components are the structure
morphism of the blow-up of `J` and the functoriality morphism
`AlgebraicGeometry.AffineBlowup.hom`, is a closed immersion. -/
theorem isClosedImmersion_pullbackLift (φ : A →+* B) (h : I.map φ = J) :
    IsClosedImmersion
      (pullback.lift (toSpec J) (hom φ h) (hom_toSpec φ h).symm :
        AffineBlowup J ⟶ pullback (Spec.map (CommRingCat.ofHom φ)) (toSpec I)) := by
  sorry

end AlgebraicGeometry.AffineBlowup
