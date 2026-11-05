/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Coextension of scalars along a Frobenius extension

Let `R ⟶ S` be a morphism of commutative rings making `S` a finite free `R`-module, and let
`φ : S → R` be a *Frobenius form*: an `R`-linear form such that every `R`-linear form on `S` is
`φ(s * -)` for a unique `s ∈ S`. Then coextension of scalars `M ↦ Hom_R(S, M)` is left adjoint
to restriction of scalars (`ModuleCat.coextendRestrictScalarsAdj`), besides being right adjoint
to it. So coextension of scalars is the extension of scalars `S ⊗_R -`.

## Construction

Let `(bᵢ)` be a basis of `S` over `R` and `(b'ᵢ)` the dual basis for `φ`, characterised by
`φ(b'ᵢ * x) = bᵢ^*(x)`. The unit `M ⟶ Hom_R(S, M)` sends `m` to `s ↦ φ(s) • m`, and the counit
`Hom_R(S, N) ⟶ N` sends `h` to `∑ᵢ b'ᵢ • h(bᵢ)`. Both triangle identities follow from
`∑ᵢ φ(bᵢ * x) • b'ᵢ = x` (`ModuleCat.CoextendScalars.sum_smul_frobeniusDual`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {ι : Type*} [Fintype ι]
  (b : Module.Basis ι R S) (φ : S →ₗ[R] R)
  (hφ : Function.Bijective fun s : S ↦ φ ∘ₗ LinearMap.mulLeft R s)

namespace CoextendScalars

end CoextendScalars

open CoextendScalars

end ModuleCat
