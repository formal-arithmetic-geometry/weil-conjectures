/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SmoothPurity.LinearScalarLocalization

/-!
# Scalar localization of a linear category

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-def-sf-operations`,
`def-weil-rationalization-karoubi`, displayed Hom formula
(blueprint: def-weil-linear-scalar-localization).

The scalar-first tensor order agrees with `LinearMap.baseChange`; `TensorProduct.comm`
identifies it with the Hom-first order in the source. Objects are wrapped only to keep
this category's instances separate from the original category's instances.
Composition is selected from the unique bilinear extension in
`exists_linear_scalarLocalization_category`, not from its unspecified category witness.
-/

@[expose] public section

universe r u v

open TensorProduct

namespace CategoryTheory

variable (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear R C] (p : R)

namespace ScalarLocalization

/-- The tensor Hom type, named before the category instance to share its reduction.
Source: the displayed Hom formula of `def-weil-rationalization-karoubi`
(blueprint: def-weil-linear-scalar-localization). -/
@[reducible] def tensorHom (K L : ScalarLocalization R C p) : Type (max r v) :=
  Localization.Away p ⊗[R] (K.obj ⟶ L.obj)

variable (T : C ⥤ C) [T.Additive] [T.Linear R]

end ScalarLocalization
end CategoryTheory
