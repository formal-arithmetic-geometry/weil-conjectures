/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Module.AdicTowerLimit
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Lattices in limits of `ℓ`-adic towers

Let `Λ` be a discrete valuation ring, `ℓ` a nonzero nonunit of `Λ` and `L` a finitely generated
`Λ`-module whose `ℓ`-power torsion is killed by `ℓᶜ`. Then `ℓᶜ L` is a free `Λ`-module of finite
rank `r` (`Module.isTorsionFree_range_nsmul`), and for every `m` and every map `e : L ⟶ M` with
kernel `ℓᵐ⁺ᶜ L`, the image `e(ℓᶜ L) ≅ ℓᶜL / ℓᵐ⁺ᶜL ≅ ℓᶜL / ℓᵐ(ℓᶜL)` is isomorphic to
`(Λ / ℓᵐ)ʳ` (`Module.exists_linearEquiv_range_comp_nsmul`).

This applies to the limit `L` of a tower `(Mₙ)` with `ℓ`-adic long exact sequences
(`ModuleCat.AdicTowerSequence`): the `ℓ`-power torsion of `lim M'ₙ` is killed by `ℓᶜ` as soon as
the tower `(Mₙ)` satisfies the Artin-Rees condition with constant `c`
(`ModuleCat.AdicTowerSequence.pow_smul_eq_zero_of_exists_eval_eq`).
-/

@[expose] public section

universe u v w

namespace IsDiscreteValuationRing

end IsDiscreteValuationRing

namespace Module

variable {Λ : Type u} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] {L : Type v}
  [AddCommGroup L] [Module Λ L]

end Module

namespace ModuleCat.AdicTowerSequence

variable {R : Type u} [CommRing R] {ℓ : ℕ} {M M' : CategoryTheory.Functor ℕᵒᵖ (ModuleCat.{v} R)}

open Opposite

end ModuleCat.AdicTowerSequence
