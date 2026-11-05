/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.CofilteredSystem
public import WeilConjectures.Mathlib.RingTheory.AdicCompletion.Functoriality
public import WeilConjectures.Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Limits of towers of finite modules with `ℓ`-adic long exact sequences

Let `(Mₙ)` and `(M'ₙ)` be towers of finite `R`-modules (think `Mₙ = Hʲ(X, Fₙ)` and
`M'ₙ = Hʲ⁺¹(X, Fₙ)` for an `ℓ`-adic tower `(Fₙ)` of sheaves) equipped, for all `n` and `m`, with
pieces of long exact sequences
`Mₙ ⟶ Mₙ₊ₘ ⟶ Mₘ ⟶ M'ₙ ⟶ M'ₙ₊ₘ`
(the cohomology sequences of `0 ⟶ Fₙ ⟶ Fₙ₊ₘ ⟶ Fₘ ⟶ 0`), natural in `n`, whose first map
composed with the transition map is multiplication by `ℓᵐ`. Let `L = lim Mₙ` and `L' = lim M'ₙ`.
Passing to the limit in `n`, which is exact on towers of finite modules by Kőnig's lemma
(`CategoryTheory.Functor.exists_mem_sections_of_finite`), gives the exact sequences
`0 ⟶ L/ℓᵐL ⟶ Mₘ ⟶ L'[ℓᵐ] ⟶ 0`:

- `ModuleCat.AdicTowerSequence.eval_eq_zero_iff`: the kernel of `L ⟶ Mₘ` is `ℓᵐL`;
- `ModuleCat.AdicTowerSequence.exists_eval_eq_iff`: the image of `L ⟶ Mₘ` is the kernel of
  `δ : Mₘ ⟶ L'`;
- `ModuleCat.AdicTowerSequence.exists_limδ_eq_iff`: the image of `δ` is the `ℓᵐ`-torsion of `L'`.

If the `ℓ`-power torsion of `L'` is killed by `ℓᶜ`, the image of `Mₘ₊꜀ ⟶ Mₘ` is contained in
the image of `L` (`ModuleCat.AdicTowerSequence.exists_eval_eq_towerMap`): the tower `(Mₘ)` is
then Artin-Rees isomorphic to `(L/ℓᵐL)`. When `R` is noetherian and `ℓ`-adically precomplete,
`L` and `L'` are finitely generated (`ModuleCat.AdicTowerSequence.module_finite`, using
`Module.Finite.of_isHausdorff_span_singleton`), so such a `c` exists
(`ModuleCat.AdicTowerSequence.exists_pow_smul_eq_zero_of_pow_smul_eq_zero`); the result is
`ModuleCat.AdicTowerSequence.exists_artinRees`.
-/

@[expose] public section

universe u v w

open CategoryTheory Opposite

namespace CategoryTheory.Functor

end CategoryTheory.Functor

namespace ModuleCat

variable {R : Type u} [CommRing R]

end ModuleCat

namespace ModuleCat

variable {R : Type u} [CommRing R]

namespace AdicTowerSequence

variable {ℓ : ℕ} {M M' : ℕᵒᵖ ⥤ ModuleCat.{v} R}

end AdicTowerSequence

section

variable {ℓ : ℕ} {M : ℕᵒᵖ ⥤ ModuleCat.{v} R}

end

namespace AdicTowerSequence

variable {ℓ : ℕ} {M M' : ℕᵒᵖ ⥤ ModuleCat.{v} R}

end AdicTowerSequence

end ModuleCat
