/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# The internal hom out of a dualizable object is tensoring with the dual

For a closed object `Y` of a monoidal category with a left dual, we construct the canonical
natural isomorphism `tensorLeft (ᘁY) ≅ ihom Y` comparing the "tensor with the dual"
description coming from the exact pairing with the chosen internal hom; pointwise it reads
`ᘁY ⊗ X ≅ (Y ⟶[C] X)`. Mathlib's `closedOfHasLeftDual` builds a closed structure whose
internal hom is `tensorLeft (ᘁY)`, and its docstring notes that any other internal hom of
`Y` is naturally isomorphic to it without providing the isomorphism; this file records that
isomorphism (by uniqueness of right adjoints), together with the characterization of the
comparison against the evaluation of the exact pairing.

## Main declarations

- `CategoryTheory.leftDualTensorNatIsoIhom`: the natural isomorphism
  `tensorLeft (ᘁY) ≅ ihom Y`, by uniqueness of right adjoints applied to
  `tensorLeftAdjunction` and `ihom.adjunction`.
- `CategoryTheory.leftDualTensorIsoIhom`: the pointwise isomorphism `ᘁY ⊗ X ≅ (Y ⟶[C] X)`.
- `CategoryTheory.uncurry_leftDualTensorIsoIhom_hom`: uncurrying the comparison gives the
  evaluation of the exact pairing, pinning down the isomorphism.
-/

@[expose] public section

namespace CategoryTheory

open Category MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C]

variable (Y : C) [Closed Y] [HasLeftDual Y]

/-- For a closed object `Y` with a left dual, the chosen internal hom `ihom Y` is naturally
isomorphic to tensoring with the left dual, by uniqueness of right adjoints applied to
`tensorLeftAdjunction (ᘁY) Y` and `ihom.adjunction Y`. -/
def leftDualTensorNatIsoIhom : tensorLeft (ᘁY : C) ≅ ihom Y :=
  Adjunction.rightAdjointUniq (tensorLeftAdjunction (ᘁY) Y) (ihom.adjunction Y)

/-- For a closed object `Y` with a left dual, the internal hom `Y ⟶[C] X` is isomorphic to
`ᘁY ⊗ X`. -/
def leftDualTensorIsoIhom (X : C) : (ᘁY : C) ⊗ X ≅ (Y ⟶[C] X) :=
  (leftDualTensorNatIsoIhom Y).app X

@[simp]
theorem leftDualTensorNatIsoIhom_hom_app (X : C) :
    (leftDualTensorNatIsoIhom Y).hom.app X = (leftDualTensorIsoIhom Y X).hom :=
  rfl

@[simp]
theorem leftDualTensorNatIsoIhom_inv_app (X : C) :
    (leftDualTensorNatIsoIhom Y).inv.app X = (leftDualTensorIsoIhom Y X).inv :=
  rfl

/-- Uncurrying the comparison `ᘁY ⊗ X ≅ (Y ⟶[C] X)` gives the evaluation of the exact
pairing. -/
theorem uncurry_leftDualTensorIsoIhom_hom (X : C) :
    MonoidalClosed.uncurry (leftDualTensorIsoIhom Y X).hom =
      (α_ Y (ᘁY : C) X).inv ≫ ε_ (ᘁY : C) Y ▷ X ≫ (λ_ X).hom := by
  calc MonoidalClosed.uncurry (leftDualTensorIsoIhom Y X).hom
      = (tensorLeftAdjunction (ᘁY) Y).counit.app X :=
        Adjunction.homEquiv_symm_rightAdjointUniq_hom_app
          (tensorLeftAdjunction (ᘁY) Y) (ihom.adjunction Y) X
    _ = (α_ Y (ᘁY : C) X).inv ≫ ε_ (ᘁY : C) Y ▷ X ≫ (λ_ X).hom := by
        simp [tensorLeftAdjunction, tensorLeftHomEquiv]

end CategoryTheory
