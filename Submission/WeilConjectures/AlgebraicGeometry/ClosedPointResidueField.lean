/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.PointCount
public import Submission.WeilConjectures.FieldTheory.SepClosedFiniteExtension

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Residue fields of closed points of schemes of finite type over a field

For a scheme `X` locally of finite type over a field `k`, a point is closed if and only if its
residue field is finite over `k` (Zariski's lemma). Over a separably closed field, residue
fields of closed points are finite purely inseparable and separably closed.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Blueprint `lem-kun-closed-point-field` (b): if `k` is separably closed and `x` is a closed
point of a scheme locally of finite type over `k`, then `κ(x)` is finite and purely
inseparable over `k`, and `κ(x)` is separably closed.

Proof: finiteness is part (a); a finite extension of a separably closed field is purely
inseparable (`lem-kun-sep-closed-finite-extension-purely-inseparable`) and separably closed
(`lem-kun-sep-closed-finite-extension-sep-closed`). -/
theorem Hom.residueField_of_isClosed_of_isSepClosed [IsSepClosed k] (f : X.Hom (Spec (.of k)))
    [LocallyOfFiniteType f] (x : X) (hx : IsClosed {x}) :
    letI := (f.residueFieldAlgebraMap x).toAlgebra
    Module.Finite k (X.residueField x) ∧ IsPurelyInseparable k (X.residueField x) ∧
      IsSepClosed (X.residueField x) := by
  let := (f.residueFieldAlgebraMap x).toAlgebra
  have := f.finite_residueField_of_isClosed x hx
  exact ⟨this, IsSepClosed.isPurelyInseparable_of_finite k _, IsSepClosed.of_finite k _⟩

end AlgebraicGeometry.Scheme
