/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone

/-!
# Reduction modulo a scalar as a mapping cone, for a `DerivedCategory.TensorStructure`

The results of `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone` are
restated here for a `DerivedCategory.TensorStructure` `T` equal to
`DerivedCategory.tensorStructure A R`, the monoidal structure of `D(A)` being `T.monoidalCategory`.
This is the form in which the derived completion diagrams of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs` use the derived tensor product:
they are stated with `T = DerivedCategory.sheafTensorStructure J R`. The equation `T = …` is
substituted away in the proofs, so that no definitional unfolding of the monoidal structure of a
concrete derived category is needed (see the implementation notes of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs`).

## Main definitions

- `DerivedCategory.TensorStructure.reductionIso`: for a short exact sequence
  `0 ⟶ 𝟙 ⟶ 𝟙 ⟶ M ⟶ 0` whose first map is `r`, the isomorphism `Q X ⊗ᴸ M ≅ Q (cone(r : X ⟶ X))`.
-/

@[expose] public section

universe v u

open CategoryTheory Category Limits MonoidalCategory

namespace DerivedCategory.TensorStructure

open CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [HasDerivedCategory.{v} A]
  [MonoidalCategory A] [MonoidalClosed A] [MonoidalPreadditive A] [BraidedCategory A]
  [Abelian.HasFunctorialFlatResolution A]
  {R : Type*} [CommRing R] [Linear R A] [MonoidalLinear R A]
  (T : TensorStructure.{v} A R) (hT : T = tensorStructure.{v} A R)

section Reduction

variable {r : R} {M : A} {p : 𝟙_ A ⟶ M} (w : (r • 𝟙 (𝟙_ A)) ≫ p = 0)
  (hS : (ShortComplex.mk (r • 𝟙 (𝟙_ A)) p w).ShortExact)

end Reduction

section ChangeOfScalar

variable {r₁ r₂ s : R} (hr : r₂ * s = r₁)
  {M₁ M₂ : A} {p₁ : 𝟙_ A ⟶ M₁} {p₂ : 𝟙_ A ⟶ M₂} (w₁ : (r₁ • 𝟙 (𝟙_ A)) ≫ p₁ = 0)
  (w₂ : (r₂ • 𝟙 (𝟙_ A)) ≫ p₂ = 0)
  (hS₁ : (ShortComplex.mk (r₁ • 𝟙 (𝟙_ A)) p₁ w₁).ShortExact)
  (hS₂ : (ShortComplex.mk (r₂ • 𝟙 (𝟙_ A)) p₂ w₂).ShortExact)
  (q : M₁ ⟶ M₂) (hq : p₁ ≫ q = p₂)

end ChangeOfScalar

end DerivedCategory.TensorStructure
