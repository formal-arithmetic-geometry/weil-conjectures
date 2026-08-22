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

If a closed object `Y` of a monoidal category has a left dual `ᘁY`, then the internal
hom functor `ihom Y` is naturally isomorphic to `tensorLeft (ᘁY)`: both are right
adjoint to `tensorLeft Y`, the former by definition of `Closed` and the latter by
`CategoryTheory.tensorLeftAdjunction`. This is the comparison isomorphism promised in
the docstring of `CategoryTheory.closedOfHasLeftDual`; it reduces internal homs out of
dualizable objects to tensor computations.

## Main declarations

- `CategoryTheory.MonoidalClosed.leftDualTensorNatIsoIhom`: the natural isomorphism
  `tensorLeft (ᘁY) ≅ ihom Y` of right adjoints of `tensorLeft Y`.
- `CategoryTheory.MonoidalClosed.leftDualTensorIsoIhom`: its component
  `ᘁY ⊗ X ≅ (ihom Y).obj X` at an object `X`.
- `CategoryTheory.MonoidalClosed.uncurry_leftDualTensorIsoIhom_hom`: the comparison
  isomorphism is characterized by the fact that it uncurries to the evaluation of the
  duality pairing: `uncurry (leftDualTensorIsoIhom Y X).hom` is
  `(α_ Y (ᘁY) X).inv ≫ ε_ (ᘁY) Y ▷ X ≫ (λ_ X).hom`.
-/

@[expose] public section

namespace CategoryTheory.MonoidalClosed

open MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C]

/-- For a closed object `Y` with a left dual, tensoring on the left with the dual `ᘁY`
is naturally isomorphic to the internal hom functor `ihom Y`: both are right adjoint to
tensoring on the left with `Y`. -/
noncomputable def leftDualTensorNatIsoIhom (Y : C) [Closed Y] [HasLeftDual Y] :
    tensorLeft (ᘁY) ≅ ihom Y :=
  Adjunction.rightAdjointUniq (tensorLeftAdjunction (ᘁY) Y) (ihom.adjunction Y)

/-- The internal hom out of a closed object with a left dual is tensoring with the dual:
`[Y, X] ≅ ᘁY ⊗ X`. -/
noncomputable def leftDualTensorIsoIhom (Y X : C) [Closed Y] [HasLeftDual Y] :
    (ᘁY) ⊗ X ≅ (ihom Y).obj X :=
  (leftDualTensorNatIsoIhom Y).app X

/-- The comparison isomorphism `ᘁY ⊗ X ≅ (ihom Y).obj X` uncurries to the evaluation of
the duality pairing between `ᘁY` and `Y`. This characterizes the isomorphism: `uncurry`
is injective, being the inverse of an equivalence of hom-sets. -/
theorem uncurry_leftDualTensorIsoIhom_hom (Y X : C) [Closed Y] [HasLeftDual Y] :
    uncurry (leftDualTensorIsoIhom Y X).hom =
      (α_ Y (ᘁY) X).inv ≫ ε_ (ᘁY) Y ▷ X ≫ (λ_ X).hom := by
  have h := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app
    (tensorLeftAdjunction (ᘁY) Y) (ihom.adjunction Y) X
  rw [homEquiv_symm_apply_eq] at h
  refine h.trans ?_
  change Y ◁ 𝟙 ((ᘁY) ⊗ X) ≫ (α_ Y (ᘁY) X).inv ≫ ε_ (ᘁY) Y ▷ X ≫ (λ_ X).hom = _
  simp

end CategoryTheory.MonoidalClosed
