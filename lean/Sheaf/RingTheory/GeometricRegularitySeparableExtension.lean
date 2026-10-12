/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.RingTheory.GRing
public import Mathlib.FieldTheory.Separable
import Sheaf.AlgebraicGeometry.FiniteSeparableMultiplicationEtale
import Sheaf.FieldTheory.SeparableTensorPurelyInseparable
import Sheaf.RingTheory.GeometricRegularitySubfields
import Sheaf.RingTheory.GeometricallyRegularFieldExtension
import Sheaf.RingTheory.GeometricallyRegularSmoothAscent

@[expose] public section

universe u v w

namespace Algebra

/-- Forward ascent along a separable algebraic extension. The proof follows the finite
intermediate-field reduction, smooth multiplication base change, and smooth ascent in
Stacks Project, Lemma 07QH.
(blueprint: lem-weil-pbc-geometric-regularity-separable-extension-forward) -/
theorem isGeometricallyRegular_of_isSeparable
    (k : Type u) (k' : Type v) (R : Type w)
    [Field k] [Field k'] [CommRing R]
    [Algebra k k'] [Algebra k' R] [Algebra k R] [IsScalarTower k k' R]
    [Algebra.IsSeparable k k'] [IsNoetherianRing R] :
    IsGeometricallyRegular k R → IsGeometricallyRegular k' R := by
  sorry

/-- Descent along a separable algebraic extension. The proof tensors finite purely inseparable
extensions with the separable extension and uses cancellation, as in Stacks Project,
Lemma 07QH. (blueprint: lem-weil-pbc-geometric-regularity-separable-extension-backward) -/
theorem isGeometricallyRegular_of_isSeparable_rev
    (k : Type u) (k' : Type v) (R : Type w)
    [Field k] [Field k'] [CommRing R]
    [Algebra k k'] [Algebra k' R] [Algebra k R] [IsScalarTower k k' R]
    [Algebra.IsSeparable k k'] [IsNoetherianRing R] :
    IsGeometricallyRegular k' R → IsGeometricallyRegular k R := by
  sorry

/-- Geometric regularity of a Noetherian algebra is unchanged when its base field is replaced
by a separable algebraic extension over which the algebra is already defined.
Source: Stacks Project, Algebra, Lemma 07QH and Definition 0382
(blueprint: lem-weil-pbc-geometric-regularity-separable-extension).
-/
theorem isGeometricallyRegular_iff_of_isSeparable
    (k : Type u) (k' : Type v) (R : Type w)
    [Field k] [Field k'] [CommRing R]
    [Algebra k k'] [Algebra k' R] [Algebra k R] [IsScalarTower k k' R]
    [Algebra.IsSeparable k k'] [IsNoetherianRing R] :
    IsGeometricallyRegular k R ↔ IsGeometricallyRegular k' R := by
  constructor
  · exact isGeometricallyRegular_of_isSeparable k k' R
  · exact isGeometricallyRegular_of_isSeparable_rev k k' R

end Algebra
