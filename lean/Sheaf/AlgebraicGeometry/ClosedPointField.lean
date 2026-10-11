/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.Topology.JacobsonSpace
import WeilConjectures.ZetaSeries

/-!
# Residue fields of closed points

Source: the blueprint of the Weil conjectures, chapter `sec-smooth-purity`, unit
`sk-prop-sf-kunneth-ordinary` (blueprint: lem-kun-closed-point-field).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Source: blueprint node `lem-kun-closed-point-field`, order 1694
(blueprint: lem-kun-closed-point-field). Let `X` be a scheme of finite type over a field `K`
(structure morphism `f`) and `x` a point, with `κ(x)` a `K`-algebra through `f`
(`Scheme.Hom.residueFieldAlgebraMap`). (a) `x` is closed iff `trdeg_K κ(x) = 0`, iff
`κ(x)` is finite over `K`. (b) If `K` is separably closed and `x` is closed, then
`κ(x)/K` is finite and purely inseparable and `κ(x)` is separably closed.

Proof. (1) On an affine open `Spec A ∋ x`, `A` is a finitely generated `K`-algebra, `x` is
a prime `p` with `κ(x) = Frac (A/p)`, and `x` is closed in it iff `p` is maximal; `x` is
closed in `X` iff it is closed in every affine open containing it, and finiteness of
`κ(x)` does not depend on the open. (2) If `p` is maximal, Zariski's lemma makes
`κ(x) = A/p` finite over `K`. Conversely, if `κ(x)` is finite, the domain `A/p` is a
finite-dimensional `K`-subspace, multiplication by a nonzero element is injective hence
surjective, so `A/p` is a field and `p` is maximal. (3) A finitely generated field extension
has a finite transcendence basis, and it is finite exactly when this basis is empty, i.e.
iff `trdeg = 0`. (4) If `K` is separably closed and `x` closed, `κ(x)/K` is finite by (a),
hence purely inseparable, and `κ(x)` is separably closed. -/
theorem closedPoint_iff_residueField_trdeg_zero_and_finite
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f] (x : X) :
    (letI := (f.residueFieldAlgebraMap x).toAlgebra;
      (x ∈ closedPoints X ↔ Algebra.trdeg K (X.residueField x) = 0) ∧
        (x ∈ closedPoints X ↔ Module.Finite K (X.residueField x)) ∧
        (IsSepClosed K → x ∈ closedPoints X →
          Module.Finite K (X.residueField x) ∧
          IsPurelyInseparable K (X.residueField x) ∧
          IsSepClosed (X.residueField x))) := sorry

end AlgebraicGeometry
