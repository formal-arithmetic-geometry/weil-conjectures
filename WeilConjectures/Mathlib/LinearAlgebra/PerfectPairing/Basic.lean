/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Perfect pairings under a change of one variable

`LinearMap.IsPerfPair.compl₁₂` is an instance, so its hypothesis that `p` is perfect is found by
instance search. This file gives the versions with an explicit hypothesis that change a single
variable along a linear equivalence, so that they can be used with dot notation, as
`LinearMap.IsPerfPair.flip` is:

- `LinearMap.IsPerfPair.comp`: `p ∘ₗ e` is perfect if `p` is.
- `LinearMap.IsPerfPair.compl₂`: `p.compl₂ e` is perfect if `p` is.
-/

@[expose] public section

namespace LinearMap

variable {R M M' N N' : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N]
  [AddCommGroup N'] [Module R M] [Module R M'] [Module R N] [Module R N']
  {p : M →ₗ[R] N →ₗ[R] R}

/-- A perfect pairing stays perfect after precomposing its first variable with a linear
equivalence. -/
protected lemma IsPerfPair.comp (hp : p.IsPerfPair) (e : M' ≃ₗ[R] M) :
    (p ∘ₗ (e : M' →ₗ[R] M)).IsPerfPair :=
  IsPerfPair.compl₁₂ (p := p) e (LinearEquiv.refl R N)

/-- A perfect pairing stays perfect after precomposing its second variable with a linear
equivalence. -/
protected lemma IsPerfPair.compl₂ (hp : p.IsPerfPair) (e : N' ≃ₗ[R] N) :
    (p.compl₂ (e : N' →ₗ[R] N)).IsPerfPair :=
  IsPerfPair.compl₁₂ (p := p) (LinearEquiv.refl R M) e

end LinearMap
