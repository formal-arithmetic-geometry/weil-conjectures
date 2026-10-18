/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import Sheaf.AlgebraicGeometry.GeometricallyConnectedCheckAfterExtension

/-!
# Testing geometric connectedness on an algebraically closed extension

Source: Stacks Project, `varieties.tex`, Lemma 33.7.7 (Tag 0387), Lemma 33.7.3
(Tag 054N), and the remark after Definition 33.7.1
(blueprint: lem-weil-geometrically-connected-algebraic-closure).

## Main statements

- `AlgebraicGeometry.geometricallyConnected_iff_connectedSpace_of_isAlgClosed`:
  geometric connectedness is tested on one algebraically closed extension.
- `AlgebraicGeometry.GeometricallyConnected.nonempty_over_field`:
  a geometrically connected scheme over a field is nonempty.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A scheme over a field is geometrically connected if and only if its base change to
any fixed algebraically closed extension is connected.
Source: Stacks Project, `varieties.tex`, Tags 0387 and 054N
(blueprint: lem-weil-geometrically-connected-algebraic-closure).
Proof: Forward, apply the definition of geometric connectedness to the extension `Ω/k`
(def-pc-geometrically-irreducible, def-pc-base-change). Conversely, an algebraically
closed field is separably closed (def-weil-algebraic-closure, def-pc-separably-closed).
Thus connectedness of `X_Ω` implies its geometric connectedness over `Ω` by
lem-weil-separably-closed-geometrically-connected. Descend this to `k` using
lem-weil-geometrically-connected-check-after-extension: every extension of `k` has a
common extension with `Ω`, and connectedness descends along the surjective projection
from that common base change. -/
theorem geometricallyConnected_iff_connectedSpace_of_isAlgClosed
    {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] :
    GeometricallyConnected (X ↘ Spec (.of k)) ↔
      ConnectedSpace ↥(pullback (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) := by
  constructor
  · intro h
    exact pullback_of_geometrically GeometricallyConnected.geometrically_connectedSpace _ _
  · intro h
    exact (geometricallyConnected_iff_of_fieldExtension (k := k) (k' := Ω) X).mpr
      (GeometricallyConnected.of_connectedSpace_of_isSepClosed (pullback.snd _ _))

/-- A geometrically connected scheme over a field is nonempty.
Source: Stacks Project, `varieties.tex`, remark after Definition 33.7.1
(blueprint: lem-weil-geometrically-connected-algebraic-closure).
Proof: Apply geometric connectedness to the trivial extension `k/k`
(def-pc-geometrically-irreducible, def-pc-base-change). The resulting base change is
isomorphic to `X`, so `X` is connected. Connectedness includes nonemptiness
(def-weil-connected-scheme). -/
theorem GeometricallyConnected.nonempty_over_field
    {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [GeometricallyConnected (X ↘ Spec (.of k))] : Nonempty X := by
  have : ConnectedSpace X :=
    GeometricallyConnected.connectedSpace_of_subsingleton (X ↘ Spec (.of k))
  infer_instance

end AlgebraicGeometry
