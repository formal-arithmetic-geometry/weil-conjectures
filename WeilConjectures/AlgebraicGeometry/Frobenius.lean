/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# The `q`-power Frobenius of a scheme

For a scheme `X` over `𝐅_q`, the (absolute) `q`-power Frobenius `F : X ⟶ X` is the identity
on the underlying space and `f ↦ f ^ q` on the structure sheaf. This file characterises it by
its action on affine schemes over `X`.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.IsFrobenius`: `F : X ⟶ X` is the `q`-power Frobenius of `X`.

## Implementation notes

The construction of the Frobenius endomorphism is not available, so it enters as the
predicate `IsFrobenius F q` on an endomorphism: for every ring `R`, every `t : Spec R ⟶ X`
and every ring endomorphism `φ` of `R` with `φ r = r ^ q`, the square `t ≫ F = Spec φ ≫ t`
commutes. The `q`-power Frobenius of an `𝐅_q`-scheme satisfies it, since the absolute
Frobenius is natural and `r ↦ r ^ q` is the `q`-power Frobenius of `Spec R`. Since the affine
opens cover `X`, at most one endomorphism satisfies it.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- `F : X ⟶ X` is the `q`-power Frobenius of `X`: on every affine scheme `t : Spec R ⟶ X`
over `X` it acts as `r ↦ r ^ q`, that is, `t ≫ F = Spec φ ≫ t` for every ring endomorphism
`φ` of `R` with `φ r = r ^ q` for all `r`. -/
def IsFrobenius {X : Scheme.{u}} (F : X ⟶ X) (q : ℕ) : Prop :=
  ∀ ⦃R : CommRingCat.{u}⦄ (t : Spec R ⟶ X) (φ : R ⟶ R), (∀ r, φ.hom r = r ^ q) →
    t ≫ F = Spec.map φ ≫ t

end AlgebraicGeometry.Scheme.Hom
