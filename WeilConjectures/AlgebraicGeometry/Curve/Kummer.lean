/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer

/-!
# `H¹` and `H²` of a curve via the Kummer sequence

For a curve `C` over a field `k` and `n` prime to the characteristic, the long exact cohomology
sequence of the Kummer sequence

```
  𝒪_C(C)ˣ ──n·──▶ 𝒪_C(C)ˣ ──▶ H¹(C, μₙ) ──▶ H¹(C, 𝔾ₘ) ──n·──▶ H¹(C, 𝔾ₘ) ──▶ H²(C, μₙ) ──▶
    H²(C, 𝔾ₘ)
```

computes the first two cohomology groups of `μₙ` in terms of `H¹(C, 𝔾ₘ) = Pic(C)`. The group
of units `𝒪_C(C)ˣ` is written additively, as `Additive Γ(C, ⊤)ˣ`, so that its `n`-th power map
is `n • ·`.

## Main statements

- `AlgebraicGeometry.exists_exact_sheafH_rootsOfUnitySheaf_one`: the short exact sequence
  `0 → 𝒪_C(C)ˣ/n → H¹(C, μₙ) → Pic(C)[n] → 0`.
- `AlgebraicGeometry.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_two`:
  `H²(C, μₙ) ≅ Pic(C)/n·Pic(C)` over an algebraically closed field.

## TODO

The maps of both statements are those of the Kummer long exact sequence. The long exact
sequence of a short exact sequence of sheaves is
`CategoryTheory.Abelian.Ext.covariantSequence_exact`; once its maps are connected to
`CategoryTheory.Sheaf.H`, the maps should be named rather than quantified.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]

-- The conclusions below do not mention `f`, so the structure morphism has to be included by hand.
include f

/-- **`H¹` via the Kummer sequence.** For a curve `C` over a field `k` and every `n ≥ 1` prime
to `char k` there is a short exact sequence

`0 ⟶ 𝒪_C(C)ˣ/(𝒪_C(C)ˣ)ⁿ ⟶ H¹(C, μₙ) ⟶ Pic(C)[n] ⟶ 0`,

recorded as the existence of an injection `α` and a map `β` with `ker β = im α` and
`im β = Pic(C)[n]`. It is read off the long exact sequence of the Kummer sequence
`AlgebraicGeometry.Scheme.kummerSequence`, with `H⁰(C, 𝔾ₘ) = 𝒪_C(C)ˣ` and
`H¹(C, 𝔾ₘ) = Pic(C)`. In particular `H¹(C, μₙ) ≅ Pic(C)[n]` when `𝒪_C(C)ˣ` is `n`-divisible,
for instance when `k` is algebraically closed and `C` is proper.
(blueprint: `sk-prop-h1`) -/
theorem exists_exact_sheafH_rootsOfUnitySheaf_one (n : ℕ) (hn : (n : k) ≠ 0) :
    ∃ (α : Additive Γ(C, ⊤)ˣ ⧸ (zsmulAddGroupHom (α := Additive Γ(C, ⊤)ˣ) (n : ℤ)).range →+
        Sheaf.H (C.rootsOfUnitySheaf n) 1)
      (β : Sheaf.H (C.rootsOfUnitySheaf n) 1 →+ C.CohomologicalPicardGroup),
      Function.Injective α ∧ Function.Exact α β ∧
        β.range = (zsmulAddGroupHom (α := C.CohomologicalPicardGroup) (n : ℤ)).ker :=
  sorry

/-- **`H²` via the Kummer sequence.** For a curve `C` over an algebraically closed field `k`
and every `n ≥ 1` prime to `char k`,

`H²(C, μₙ) ≅ Pic(C)/n·Pic(C)`.

In the long exact sequence of the Kummer sequence, `H²(C, μₙ)` is the cokernel of
`n : Pic(C) → Pic(C)` because the next term `H²(C, 𝔾ₘ) = Br(C)` vanishes; for a smooth curve
that is `AlgebraicGeometry.subsingleton_cohomologicalBrauerGroup`.
(blueprint: `sk-prop-h2`) -/
theorem nonempty_addEquiv_sheafH_rootsOfUnitySheaf_two [IsAlgClosed k] (n : ℕ)
    (hn : (n : k) ≠ 0) :
    Nonempty (Sheaf.H (C.rootsOfUnitySheaf n) 2 ≃+
      C.CohomologicalPicardGroup ⧸
        (zsmulAddGroupHom (α := C.CohomologicalPicardGroup) (n : ℤ)).range) :=
  sorry

end AlgebraicGeometry
