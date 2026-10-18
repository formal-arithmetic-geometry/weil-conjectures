/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q136
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Sheaf.CategoryTheory.InvertibleFactorHomCancellation

/-!
# Evaluation-transpose cancellation of an invertible factor

Source: blueprint `main-20261015`, `sec-six-functors/sk-thm-sf-dual-perfect`, proof Step 5,
inverse twist in the double application of Step 3 (blueprint: lem-sf-invertible-hom-cancellation).

The comparison is defined using the specified associators, symmetry, evaluation and left unitor.
The statement records its invertibility and both naturality clauses.
-/

@[expose] public section

universe v u

namespace CategoryTheory.MonoidalClosed

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C]

/-- The specified map `i_{V,L}` is the transpose of evaluation after moving `L` past
`[V,𝟙]`, with the associators and left unitor written explicitly. Its definition needs no
invertibility choice. Source: blueprint `main-20261015`, proof of `thm-sf-dual-perfect`,
Step 5, inverse twist (blueprint: lem-sf-invertible-hom-cancellation). -/
def invertibleHomComparison (V L : C) :
    (ihom V).obj (𝟙_ C) ⟶ (ihom (V ⊗ L)).obj L :=
  curry
    ((α_ V L ((ihom V).obj (𝟙_ C))).hom ≫
      V ◁ (β_ L ((ihom V).obj (𝟙_ C))).hom ≫
      (α_ V ((ihom V).obj (𝟙_ C)) L).inv ≫
      (ihom.ev V).app (𝟙_ C) ▷ L ≫ (λ_ L).hom)

/-- The evaluation-transpose map `i_{V,L}` is invertible, contravariantly natural in `V`,
and compatible with every isomorphism of the invertible factor `L`. In the last equation the
inverse of that isomorphism acts on the contravariant argument of internal Hom.

Source: blueprint `main-20261015`, proof of `thm-sf-dual-perfect`, Step 5, inverse twist in
the double application of Step 3 (blueprint: lem-sf-invertible-hom-cancellation).

Proof plan: apply `lem-sf-invertible-factor-hom-cancellation` with `X = V`, `Y = 𝟙` and
`J = L`. The supplied isomorphism `L ⊗ I ≅ 𝟙` gives the first inverse-factor isomorphism;
compose the symmetry `I ⊗ L ≅ L ⊗ I` with it to obtain the second. Identify the resulting
map `s_{V,𝟙,L}`, followed by internal Hom applied to the left unitor, with the displayed
`invertibleHomComparison`: uncurrying both gives precisely evaluation after moving `L`
past `[V,𝟙]`, with the specified associators. The inverse-factor theorem proves this map
invertible, contravariantly natural in `V`, and compatible with isomorphisms of `L`.
Naturality of the left unitor gives exactly the last displayed equation after identifying
`𝟙 ⊗ L` with `L`. The identification of transposes uses `uncurry_curry`,
`uncurry_natural_left` and `uncurry_eq` from `lem-pod-closed-uncurry-laws`. -/
theorem invertibleHomCancellation (L I : C) (_e : L ⊗ I ≅ 𝟙_ C) :
    (∀ V : C, IsIso (invertibleHomComparison V L)) ∧
    (∀ (V W : C) (f : V ⟶ W),
      (pre f).app (𝟙_ C) ≫ invertibleHomComparison V L =
        invertibleHomComparison W L ≫ (pre (f ▷ L)).app L) ∧
    (∀ (L' : C) (a : L ≅ L') (V : C),
      invertibleHomComparison V L' =
        invertibleHomComparison V L ≫ (pre (V ◁ a.inv)).app L ≫
          (ihom (V ⊗ L')).map a.hom) := by
  sorry

end CategoryTheory.MonoidalClosed
