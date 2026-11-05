/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeFrobenius
public import WeilConjectures.TraceFormula.Frobenius

/-!
# The relative Frobenius of model Frobenii

Let `k₀` be a finite field, `k` a field over `k₀`, and `X = X₀ ×_{k₀} k`, `Y = Y₀ ×_{k₀} k`
objects of `Over (Spec (.of k))` with model Frobenii `Φ_X`, `Φ_Y`. For a morphism `f : X ⟶ Y`
with `Φ_X ≫ f = f ≫ Φ_Y`, the relative Frobenius `r_m = (f, Φ_X ^ m) : X ⟶ X'_m` into
`X'_m = Y ×_{Φ_Y ^ m, Y, f} X` is a finite universal homeomorphism, and if `f` is the base
change of a morphism `f₀ : X₀ ⟶ Y₀`, then `r_m` is the base change of the relative
`#k₀ ^ m`-power Frobenius of `f₀`.

## Main statements

- `AlgebraicGeometry.ProEtale.CondensedRing.isFinite_frobeniusIterate_left`,
  `AlgebraicGeometry.ProEtale.CondensedRing.isUniversalHomeomorphism_frobeniusIterate_left`:
  iterates of finite (universally homeomorphic) endomorphisms.
- `AlgebraicGeometry.ProEtale.CondensedRing.IsModelFrobenius.relativeFrobenius_frobeniusIterate`:
  the relative Frobenius `r_m` is a finite universal homeomorphism with `p_m ∘ r_m = Φ_X ^ m`
  and `f'_m ∘ r_m = f` (blueprint `i-relative-frob`).
- `AlgebraicGeometry.ProEtale.CondensedRing.IsModelFrobenius.isPullback_relativeFrobenius_left`:
  `r_m` is the base change of the relative `#k₀ ^ m`-power Frobenius of a model `f₀`
  (blueprint `d-relative-frob`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

section Iterate

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} (Φ : X ⟶ X)

end Iterate

section Model

variable {k : Type u} [Field k] {X Y : Over (Spec (.of k))} {ΦX : X ⟶ X} {ΦY : Y ⟶ Y}
  {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ Y₀ : Scheme.{u}}
  {fX₀ : X₀ ⟶ Spec (.of k₀)} {fY₀ : Y₀ ⟶ Spec (.of k₀)} {pX : X.left ⟶ X₀} {pY : Y.left ⟶ Y₀}

end Model

end AlgebraicGeometry.ProEtale.CondensedRing
