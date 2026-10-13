/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import WeilConjectures.ZetaSeries
import WeilConjectures.RingTheory.IsolatedPrimeResidueFinite
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.PropertyC

@[expose] public section

universe u

open CategoryTheory
namespace AlgebraicGeometry

/-- An isolated point of a scheme locally of finite type over a field has finite residue
field extension.

Source: Stacks Project, Algebra, Lemma 00PJ (algebra-lemma-isolated-point), implication
(1) => (6), in an affine open of a scheme locally of finite type over `Spec k`
(blueprint: lem-weil-pbc-lft-over-field-isolated-point-residue-finite).

Proof: choose an affine open neighbourhood `U = Spec B` of `y` and the corresponding
prime `p`. The affine characterization of locally finite type morphisms gives that
`k → B` is of finite type, while the open singleton hypothesis pulls back to an open
singleton `{p}`. Apply `lem-weil-pbc-isolated-prime-finite-type-algebra-residue-finite`
to obtain finite dimensionality of the affine residue field over `k`. The canonical
identifications of affine and scheme residue fields, together with
`lem-weil-pbc-spec-map-residue-field-naturality`, identify the induced `k`-actions
(the `k`-algebra structure on `κ(y)` is the source's `Scheme.Hom.residueFieldAlgebraMap`
of `g`).
Transport finite dimensionality across this `k`-linear residue-field isomorphism.
-/
theorem lft_over_field_isolated_point_residue_finite
    (k : Type u) [Field k] (Y : Scheme.{u})
    (g : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g] (y : Y)
    (hy : IsOpen ({y} : Set Y)) :
    (letI := (g.residueFieldAlgebraMap y).toAlgebra
    FiniteDimensional k (Y.residueField y)) := by
  sorry

end AlgebraicGeometry
