/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup

/-!
# The general linear group scheme

The general linear group `GL_n` over a commutative ring `k` is the affine group scheme
`Spec k[x_ij, det⁻¹]` over `Spec k`, the spectrum of the Hopf algebra
`Matrix.GeneralLinearGroup.CoordinateRing n k`. Mathlib's `instGrpObjSpecAsOverSpec` makes it a
group object in `Over (Spec k)`. Its points with values in a `k`-algebra `R` are the invertible
`n × n` matrices over `R`, as groups.

This is the scheme-theoretic model of `GL_n`. The point-set model of
`WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.MatrixGroup` is the group `GL n k` of
`k`-points with the Zariski topology `Matrix.GeneralLinearGroup.zariskiTopology`. Over an
algebraically closed field `k` the two agree: the `k`-points of `scheme n k` are `GL n k` by
`homMulEquiv`, and the regular functions of `Matrix.IsRegularOn` on `GL n k` are the elements of
`CoordinateRing n k`. This comparison is not formalised here.

## Main definitions

- `Matrix.GeneralLinearGroup.scheme`: `GL_n` as an affine group scheme of finite type over `k`.
- `Matrix.GeneralLinearGroup.homMulEquiv`: the `R`-points of the group scheme `GL_n` are the
  group `GL n R`.

## Blueprint

- `sk-d-geometry`: the ambient group `GL(V)` of the algebraic groups block, as a group scheme.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped MonObj

namespace Matrix.GeneralLinearGroup

variable (n : Type u) [Fintype n] [DecidableEq n] (k : Type u) [CommRing k]

/-- The general linear group `GL_n` as an affine group scheme over `k`: the spectrum of the Hopf
algebra `k[x_ij, det⁻¹]`. It is a group object by `instGrpObjSpecAsOverSpec`.
(blueprint: `sk-d-geometry`) -/
noncomputable abbrev scheme : Over (Spec (.of k)) :=
  (Spec (.of (CoordinateRing n k))).asOver (Spec (.of k))

noncomputable example : GrpObj (scheme n k) := inferInstance

instance : IsAffine (scheme n k).left :=
  inferInstanceAs (IsAffine (Spec (.of (CoordinateRing n k))))

instance : LocallyOfFiniteType (scheme n k).hom :=
  locallyOfFiniteType_specOverSpec

/-- The `R`-points of the group scheme `GL_n` are the invertible `n × n` matrices over `R`, as
groups. (blueprint: `sk-d-geometry`) -/
noncomputable def homMulEquiv (R : Type u) [CommRing R] [Algebra k R] :
    ((Spec (.of R)).asOver (Spec (.of k)) ⟶ scheme n k) ≃* GL n R :=
  Spec.mapMulEquiv.symm.trans (algHomMulEquiv n k R)

end Matrix.GeneralLinearGroup
