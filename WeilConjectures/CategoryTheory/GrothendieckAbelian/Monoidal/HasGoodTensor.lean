/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!

# Good tensor products of graded objects in a closed braided category

The tensor product of `I`-graded objects of a monoidal category `C` is only partially
defined: the graded object `X₁ ⊗ X₂` is the coproduct of the `X₁ i₁ ⊗ X₂ i₂` with
`i₁ + i₂ = n` in each degree `n`, and its associativity and pentagon coherence need the
tensor product of `C` to commute with those coproducts. Mathlib records the three
resulting side conditions as

* `GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃`, for `(X₁ ⊗ X₂) ⊗ X₃`;
* `GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃`, for `X₁ ⊗ (X₂ ⊗ X₃)`;
* `GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄`, for the fourfold tensor product.

They are what the tensor product of cochain complexes, and hence the K-flat left
derivability structure of
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs`, asks of its
ambient category, where they appear as the three instance hypotheses

```
[∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
[∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
[∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
```

All three unfold to the preservation of a coproduct by `tensorLeft Z` or by
`tensorRight Z` for a fixed object `Z` of `C`. This file discharges them once and for all
from two hypotheses on `C` alone:

* `MonoidalClosed C`, which makes `tensorLeft Z` a left adjoint — of the internal hom
  `ihom Z` — and hence colimit preserving;
* `BraidedCategory C`, which carries this over to `tensorRight Z` through the natural
  isomorphism `BraidedCategory.tensorLeftIsoTensorRight`.

Nothing else about `C` is used: in particular there is no abelian, Grothendieck abelian
or sheaf-theoretic hypothesis, and the grading monoid `I` is arbitrary. Consumers such as
the étale sheaf categories of `WeilConjectures.SixFunctors.Etale.Derived` therefore only
have to exhibit `MonoidalClosed` and `BraidedCategory` for their own category — for the
small étale site this is
`AlgebraicGeometry.Etale.sheafMonoidalClosed` of the sibling file `TensorColimits`
(Day's reflection theorem) together with `AlgebraicGeometry.Etale.sheafBraidedCategory`
of the sibling file `Defs` — and the three conditions above follow.

## Main results

- `CategoryTheory.GradedObject.hasGoodTensor₁₂Tensor`
- `CategoryTheory.GradedObject.hasGoodTensorTensor₂₃`
- `CategoryTheory.GradedObject.hasTensor₄ObjExt`

## TODO

All three proofs are currently `sorry`. Each should follow from the single statement that
`tensorLeft Z` and `tensorRight Z` preserve colimits of shape `Discrete J` for `J` in the
universe of `I`: for `tensorLeft Z` this is the instance
`CategoryTheory.MonoidalClosed.instPreservesColimitsTensorLeft` (universe-polymorphically,
through `CategoryTheory.Functor.IsLeftAdjoint`), and for `tensorRight Z` it is obtained
from it by transport along `BraidedCategory.tensorLeftIsoTensorRight`.

-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.GradedObject

variable {I : Type w} [AddMonoid I] {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [MonoidalClosed C] [BraidedCategory C]

/-- In a closed braided monoidal category, `- ⊗ X₃ i₃` commutes with the coproducts
defining `X₁ ⊗ X₂` in each degree, so the tensor product `(X₁ ⊗ X₂) ⊗ X₃` of graded
objects is well behaved. -/
instance hasGoodTensor₁₂Tensor (X₁ X₂ X₃ : GradedObject I C) :
    HasGoodTensor₁₂Tensor X₁ X₂ X₃ :=
  sorry

/-- In a closed braided monoidal category, `X₁ i₁ ⊗ -` commutes with the coproducts
defining `X₂ ⊗ X₃` in each degree, so the tensor product `X₁ ⊗ (X₂ ⊗ X₃)` of graded
objects is well behaved. -/
instance hasGoodTensorTensor₂₃ (X₁ X₂ X₃ : GradedObject I C) :
    HasGoodTensorTensor₂₃ X₁ X₂ X₃ :=
  sorry

/-- In a closed braided monoidal category, `X₁ i₁ ⊗ -` commutes with the coproducts
defining `X₂ ⊗ (X₃ ⊗ X₄)` in each degree, so the fourfold tensor product of graded
objects is well behaved. -/
instance hasTensor₄ObjExt (X₁ X₂ X₃ X₄ : GradedObject I C) :
    HasTensor₄ObjExt X₁ X₂ X₃ X₄ :=
  sorry

end CategoryTheory.GradedObject
