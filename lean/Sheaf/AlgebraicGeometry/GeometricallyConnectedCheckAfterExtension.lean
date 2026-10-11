/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Over

/-!
# Geometric connectedness after a field extension

Source: Stacks Project, `varieties.tex`, Lemma 33.7.3, tag 054N
(blueprint: lem-weil-geometrically-connected-check-after-extension).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Geometric connectedness over a field is equivalent to geometric connectedness
of its base change along any field extension.

Source: Stacks Project, `varieties.tex`, Lemma 33.7.3, tag 054N
(blueprint: lem-weil-geometrically-connected-check-after-extension).
Proof: If `X` is geometrically connected, every field extension of `k` gives a
connected base change, and this applies to extensions of `k'` by associativity
of base change. Conversely, for an arbitrary extension `k''/k`, choose a common
extension of `k'` and `k''` over `k`; geometric connectedness after `k'` makes
the common base change connected. The map from the common base change to the
`k''`-base change is a surjective base change, so connectedness descends along
its continuous surjective map. These are the arguments of
`def-pc-geometrically-irreducible`, `def-pc-base-change`,
`lem-weil-common-extension-fields`, and `lem-weil-pbc-surjective-base-change`.
(blueprint: lem-weil-geometrically-connected-check-after-extension). -/
theorem geometricallyConnected_iff_of_fieldExtension
    {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (X : Scheme.{u}) [X.Over (Spec (.of k))] :
    GeometricallyConnected (X ↘ Spec (.of k)) ↔
      GeometricallyConnected
        (pullback.snd (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k k'))):
            pullback (X ↘ Spec (.of k))
              (Spec.map (CommRingCat.ofHom (algebraMap k k'))) ⟶
              Spec (.of k')) := by
  sorry

end AlgebraicGeometry
