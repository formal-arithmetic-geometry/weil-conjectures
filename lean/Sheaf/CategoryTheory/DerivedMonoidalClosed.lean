/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-!
# Closedness of the derived tensor product

Source: Weil conjectures blueprint, main-20261015, sec-proetale-coefficients,
`sk-def-sfb-derived-tensor-hom`, lemma `lem-sfb-derived-monoidal-closed`
(blueprint: lem-sfb-derived-monoidal-closed).
-/

@[expose] public section

universe w v u

open CategoryTheory MonoidalCategory

namespace DerivedCategory

/-- In the situation of `lem-sfb-derived-monoidal`, tensoring on the left by any object
of the unbounded derived category has a right adjoint.

Source: Weil conjectures blueprint, main-20261015, sec-proetale-coefficients,
`sk-def-sfb-derived-tensor-hom`, lemma `lem-sfb-derived-monoidal-closed`
(blueprint: lem-sfb-derived-monoidal-closed).

Proof: First form the product internal-Hom complex and use evaluation and currying to
obtain the tensor-Hom adjunction on the homotopy category. Next, the binary derived
monoidal structure of `lem-sfb-derived-monoidal`, with one variable fixed, exhibits
`Qh.obj P ⊗ -` as the left derived functor of `P ⊗ -`. Grothendieck abelian categories
have K-injective resolutions by `lem-sfb-grothendieck-k-injective`, so derive the
right adjoint using those resolutions. Tensoring preserves quasi-isomorphisms between
K-flat complexes: use their acyclic K-flat cones and replace the other tensor factor
by a K-flat resolution. Apply the derived-adjunction argument of
`sk-def-sfb-derived-categories` to get a right adjoint for `Qh.obj P ⊗ -`.
Finally every derived object is isomorphic to some `Qh.obj P`; transport the
adjunction along the induced natural isomorphism of tensor-left functors. -/
theorem tensorLeft_isLeftAdjoint_of_hasFunctorialFlatResolution
    (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C]
    (K : DerivedCategory C) : (tensorLeft K).IsLeftAdjoint := by
  sorry

end DerivedCategory
