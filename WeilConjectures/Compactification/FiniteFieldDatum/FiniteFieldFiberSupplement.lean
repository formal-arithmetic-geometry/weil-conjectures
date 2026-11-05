/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.FieldTheory.Finite.UniqueSubfieldOfClosure
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiber

/-!
# Global finite-field datum and geometric base change

Source: Weil conjectures blueprint, `sec-nagata-compactification`,
`sk-prop-nagata-sketch-comp-category/def-weil-finite-field-fiber.md`, order 411
(blueprint: def-weil-finite-field-fiber).

The global datum permits any field with the specified cardinality and any fixed algebraic
closure. Its inclusion is `algebraMap D.k₀ D.k`. Closed points and residue fields use the
existing `closedPoints S` and `S.residueField s`, without new definitions.

For a finite-type object `Y₀` over `Spec D.k₀`, `D.geometricFiber Y₀` is the geometric
base change as an object over `Spec D.k`; its `.hom` is the structure morphism `a_Y`.
`D.extensionPoints Y₀ n hn` and `D.pointCount Y₀ n hn` give the extension-valued points
and their number. Finiteness of the point set is a separate theorem, not assumed here.

For a prime `l` distinct from `D.p`, the coefficient conventions reuse `Padic l`,
`PadicInt l`, and a field `Qbar` with `[Algebra (Padic l) Qbar] [IsAlgClosure (Padic l) Qbar]`;
`AlgebraicClosure (Padic l)` is one possible fixed choice. For every finite-dimensional
extension `E` the ring, chosen uniformizer and quotients are exactly
`Padic.coefficientExtensionIntegers l E`, `Padic.coefficientExtensionUniformizer l E`,
and `Padic.coefficientExtensionRing l E n`. These notions are not defined again here.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures

attribute [instance] FiniteFieldDatum.field_base FiniteFieldDatum.finite_base
  FiniteFieldDatum.field_closure FiniteFieldDatum.algebra_closure FiniteFieldDatum.isAlgClosure

namespace FiniteFieldDatum

attribute [instance] CoefficientDatum.prime CoefficientDatum.field CoefficientDatum.algebra
  CoefficientDatum.isAlgClosure

end FiniteFieldDatum
end WeilConjectures
