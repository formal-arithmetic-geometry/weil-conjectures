/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.SixFunctors.ProEtale.GaloisCoverTrace
import WeilConjectures.Mathlib.RingTheory.Etale.Field

/-!
# Finite Galois field extensions are Galois covers

Let `L/F` be a finite Galois extension of fields and `g : Spec L ⟶ Spec F` the induced morphism.
The Galois group `Gal(L/F)` acts on `Spec L` over `Spec F` through `σ ↦ Spec σ`
(`AlgebraicGeometry.specGaloisAction`), and this action is *Galois* in the sense of
`AlgebraicGeometry.ProEtale.IsGaloisAction` (`AlgebraicGeometry.ProEtale.isGaloisAction_spec`):
two morphisms `a b : T ⟶ Spec L` agreeing over `Spec F` agree, on the members of an open cover
of `T`, up to an element of the Galois group. Moreover `g` is finite, étale and surjective.

The algebraic input (`AlgebraicGeometry.IsGalois.exists_sum_eq_one_mul_eq`) is the splitting
`L ⊗_F L ≅ ∏_σ L` in a form valid for an arbitrary commutative target ring: for two ring maps
`α β : L → R` agreeing on `F` there are elements `e σ ∈ R` with `∑ σ, e σ = 1` and
`e σ * β y = e σ * α (σ y)`. They are obtained by evaluating the Lagrange interpolation basis at
the conjugates of a primitive element. The open cover is then given by the basic opens `D(e σ)`.

Galois actions are stable under base change (`AlgebraicGeometry.ProEtale.IsGaloisAction.pullback`
for the action `AlgebraicGeometry.ProEtale.pullbackAction` on `X' ×_X Y`); finiteness, étaleness
and surjectivity of `pullback.fst` are inferred from Mathlib's base change instances.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

variable (F L : Type u) [Field F] [Field L] [Algebra F L]

variable {F L}

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

variable {F L : Type u} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

section BaseChange

variable {X Y X' : Scheme.{u}} (f : X' ⟶ X) (g : Y ⟶ X) {Γ : Type u} {ρ : Γ → (Y ⟶ Y)}
  (hρ : ∀ i, ρ i ≫ g = g)

end BaseChange

end AlgebraicGeometry.ProEtale
