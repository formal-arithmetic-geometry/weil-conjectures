/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

/-!
# Base change along a purely inseparable field extension

Let `k ⊆ k'` be a purely inseparable field extension and `X` a scheme over `k`. The projection
`X_{k'} = X ×_{Spec k} Spec k' ⟶ X` is a homeomorphism
(`AlgebraicGeometry.isHomeomorph_pullback_fst_of_isPurelyInseparable`). Its affine case is
`PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Purely inseparable base change is a homeomorphism.** Let `k ⊆ k'` be a purely inseparable
field extension and `X` a scheme over `k`. Then the projection `X_{k'} ⟶ X` is a homeomorphism
of underlying spaces. This is local on `X`, and for `X = Spec A` it is
`PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable`: `A → A ⊗_k k'` is injective and
every element of `A ⊗_k k'` has a `p^n`-th power in `A` (Stacks 0BRA).

(blueprint: `lem-pc-homeo-pure-insep`) -/
@[stacks 0BRA]
theorem isHomeomorph_pullback_fst_of_isPurelyInseparable {k k' : Type u} [Field k] [Field k']
    [Algebra k k'] [IsPurelyInseparable k k'] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    IsHomeomorph (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).base :=
  sorry

end AlgebraicGeometry
