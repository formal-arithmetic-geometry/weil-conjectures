/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Integral and rational Tate modules

Let `ℓ` be a prime and `M` an abelian group. Writing `M[ℓ ^ n]` for the `ℓ ^ n`-torsion of `M`,
the *(integral) Tate module* of `M` is the inverse limit

```
T_ℓ M = {(t n) ∈ ∏ n, M[ℓ ^ n] | ∀ n, ℓ • t (n + 1) = t n}
```

taken along multiplication by `ℓ`. It is realised here as an `AddSubgroup` of the product
`∀ n : ℕ, M`, cut out by the two conditions `ℓ ^ n • t n = 0` and `ℓ • t (n + 1) = t n`. It
carries a natural `ℤ_[ℓ]`-action, and the *rational Tate module* is the `ℚ_[ℓ]`-vector space
`V_ℓ M = ℚ_[ℓ] ⊗_{ℤ_[ℓ]} T_ℓ M`.

## Main definitions

- `AddCommGroup.tateModule`: the integral Tate module `T_ℓ M`.
- `AddCommGroup.tateModule.instModule`: its `ℤ_[ℓ]`-module structure.
- `AddCommGroup.rationalTateModule`: the rational Tate module `V_ℓ M`.
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace AddCommGroup

variable (ℓ : ℕ) [Fact ℓ.Prime] (M : Type u) [AddCommGroup M]

/-- Blueprint `sk-d-ab-tate`: Integral and rational Tate modules.

The *Tate module* `T_ℓ M` of an abelian group `M` at a prime `ℓ` is the subgroup of the product
`∀ n : ℕ, M` consisting of the compatible systems `t` of `ℓ ^ n`-torsion points, that is, those
`t` with `ℓ ^ n • t n = 0` for all `n` and `ℓ • t (n + 1) = t n` for all `n`. -/
def tateModule : AddSubgroup (∀ _ : ℕ, M) where
  carrier := {t | (∀ n, (ℓ : ℤ) ^ n • t n = 0) ∧ ∀ n, (ℓ : ℤ) • t (n + 1) = t n}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun n => ?_, fun n => ?_⟩
    · simp [smul_add, ha n, hb n]
    · simp [smul_add, ha' n, hb' n]
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨fun n => ?_, fun n => ?_⟩
    · simp [ha n]
    · simp [ha' n]

/-- Blueprint `sk-d-ab-tate`: Integral and rational Tate modules.

The Tate module `T_ℓ M` is a module over the ring `ℤ_[ℓ]` of `ℓ`-adic integers, acting
coordinatewise: an `ℓ`-adic integer acts on the `n`-th coordinate through its reduction modulo
`ℓ ^ n`. -/
-- TODO(unify): sk-d-ab-tate
noncomputable instance tateModule.instModule : Module ℤ_[ℓ] (tateModule ℓ M) := sorry

/-- Blueprint `sk-d-ab-tate`: Integral and rational Tate modules.

The *rational Tate module* `V_ℓ M = ℚ_[ℓ] ⊗_{ℤ_[ℓ]} T_ℓ M`. -/
def rationalTateModule : Type u :=
  ℚ_[ℓ] ⊗[ℤ_[ℓ]] (tateModule ℓ M)

namespace rationalTateModule

noncomputable instance : AddCommGroup (AddCommGroup.rationalTateModule ℓ M) :=
  inferInstanceAs (AddCommGroup (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (tateModule ℓ M)))

noncomputable instance : Module ℚ_[ℓ] (AddCommGroup.rationalTateModule ℓ M) :=
  inferInstanceAs (Module ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (tateModule ℓ M)))

end rationalTateModule

end AddCommGroup
