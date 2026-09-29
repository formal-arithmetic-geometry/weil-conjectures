/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.Gm

/-!
# The Kummer sequence

For a scheme `X` and `n ≥ 1` the *Kummer sequence* is the sequence of étale sheaves

```
  0 ──▶ μₙ ──kernel.ι──▶ 𝔾ₘ ──n • 𝟙──▶ 𝔾ₘ ──▶ 0
```

whose right hand map is the `n`-th power map (written additively as `n • 𝟙`) and whose sheaf
`μₙ` of `n`-th roots of unity is by definition its kernel. It is exact as soon as `n` is
invertible on `X`, by Hensel's lemma on the strictly henselian local rings. Its long exact
cohomology sequence

```
  Γ(X, 𝒪)ˣ ──(·)ⁿ──▶ Γ(X, 𝒪)ˣ ──▶ H¹(X, μₙ) ──▶ H¹(X, 𝔾ₘ) ──n·──▶ H¹(X, 𝔾ₘ)
           ──▶ H²(X, μₙ) ──▶ H²(X, 𝔾ₘ) ──n·──▶ H²(X, 𝔾ₘ)
```

computes `H¹` and `H²` of `μₙ` in terms of the Picard and Brauer groups of `X`. The group of
units `Γ(X, 𝒪)ˣ` is written additively, as `Additive Γ(X, ⊤)ˣ`, so that its `n`-th power map
is `n • ·`.

This file also defines the constant étale sheaf `ℤ/n`, which is `μₙ` after the choice of a
primitive `n`-th root of unity.

## Main definitions

- `AlgebraicGeometry.Scheme.rootsOfUnitySheaf`: the sheaf `μₙ` of `n`-th roots of unity.
- `AlgebraicGeometry.Scheme.kummerSequence`: the Kummer sequence, as a short complex.
- `AlgebraicGeometry.Scheme.constantZMod`: the constant étale sheaf `ℤ/n`.

## Main statements

- `AlgebraicGeometry.Scheme.kummerSequence_shortExact`: the Kummer sequence is short exact
  when `n` is invertible on `X`.
- `AlgebraicGeometry.Scheme.exists_exact_sheafH_rootsOfUnitySheaf_one`: the short exact
  sequence `0 → Γ(X, 𝒪)ˣ/n → H¹(X, μₙ) → H¹(X, 𝔾ₘ)[n] → 0`.
- `AlgebraicGeometry.Scheme.exists_exact_sheafH_rootsOfUnitySheaf_two`: the short exact
  sequence `0 → H¹(X, 𝔾ₘ)/n → H²(X, μₙ) → H²(X, 𝔾ₘ)[n] → 0`.
- `AlgebraicGeometry.Scheme.nonempty_addEquiv_sheafH_zero_constantZMod`:
  `H⁰(X, ℤ/n) ≅ ℤ/n` for a connected scheme `X`.

## TODO

The maps of the two Kummer statements are those of the long exact sequence. The long exact
sequence of a short exact sequence of sheaves is
`CategoryTheory.Abelian.Ext.covariantSequence_exact`; once its maps are connected to
`CategoryTheory.Sheaf.H`, the maps should be named rather than quantified.

## Blueprint references

The labels quoted below are labels of the *sketch* blueprint, which lives in the separate
repository `formal-arithmetic-geometry/weil-conjectures-blueprint`, not of `blueprint/src` in
this repository.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (n : ℕ)

/-- The sheaf `μₙ` of `n`-th roots of unity on the small étale site of `X`: the kernel of the
`n`-th power map `n • 𝟙` on `𝔾ₘ`. -/
noncomputable def rootsOfUnitySheaf : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  kernel (n • 𝟙 X.gmSheaf)

/-- The *Kummer sequence* of a scheme `X` and an integer `n`: the sequence of étale sheaves

```
  0 ──▶ μₙ ──kernel.ι──▶ 𝔾ₘ ──n • 𝟙──▶ 𝔾ₘ ──▶ 0
```

on `X`, the second map being `ω ↦ ωⁿ` and `μₙ = ker(n)` the sheaf of `n`-th roots of unity.
Its exactness is `AlgebraicGeometry.Scheme.kummerSequence_shortExact` and is *not* part of
the definition.
(blueprint: `def-sc-kummer-sequence`) -/
noncomputable def kummerSequence :
    ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk (kernel.ι (n • 𝟙 X.gmSheaf)) (n • 𝟙 X.gmSheaf) (kernel.condition _)

/-- **Exactness of the Kummer sequence.** Let `X` be a scheme and let `n ≥ 1` be invertible on
`X`. Then the Kummer sequence `AlgebraicGeometry.Scheme.kummerSequence` is a short exact
sequence of sheaves on `X_ét`.

Exactness is checked on stalks: on a strictly henselian local ring the polynomial `Tⁿ - a` is
separable for a unit `a`, so Hensel's lemma provides an `n`-th root. The hypothesis is
necessary: in characteristic `p` the `p`-th power map is not an epimorphism of étale sheaves,
and the correct replacement is the Artin–Schreier sequence. The proof is `sorry`.
(blueprint: `lem-sc-kummer-exact`) -/
theorem kummerSequence_shortExact (hn : IsUnit (n : Γ(X, ⊤))) :
    (X.kummerSequence n).ShortExact :=
  sorry

/-- **`H¹` via the Kummer sequence.** For a scheme `X` and `n` invertible on `X` there is an
exact sequence

```
  Γ(X, 𝒪)ˣ ──(·)ⁿ──▶ Γ(X, 𝒪)ˣ ──α──▶ H¹(X, μₙ) ──β──▶ H¹(X, 𝔾ₘ)[n] ⟶ 0,
```

that is, `0 → Γ(X, 𝒪)ˣ/n → H¹(X, μₙ) → H¹(X, 𝔾ₘ)[n] → 0`. It is recorded as the existence of
maps `α` and `β` with `ker α = (Γ(X, 𝒪)ˣ)ⁿ`, `ker β = im α` and `im β = H¹(X, 𝔾ₘ)[n]`.
(blueprint: `sk-prop-h1`) -/
theorem exists_exact_sheafH_rootsOfUnitySheaf_one (hn : IsUnit (n : Γ(X, ⊤))) :
    ∃ (α : Additive Γ(X, ⊤)ˣ →+ Sheaf.H (X.rootsOfUnitySheaf n) 1)
      (β : Sheaf.H (X.rootsOfUnitySheaf n) 1 →+ X.CohomologicalPicardGroup),
      α.ker = (zsmulAddGroupHom (α := Additive Γ(X, ⊤)ˣ) (n : ℤ)).range ∧
        Function.Exact α β ∧ β.range = AddSubgroup.torsionBy X.CohomologicalPicardGroup n :=
  -- Proof sketch: this is the start of the long exact sequence of
  -- `AlgebraicGeometry.Scheme.kummerSequence_shortExact`, with `H⁰(X, 𝔾ₘ) = Γ(X, 𝒪)ˣ`.
  sorry

/-- **`H²` via the Kummer sequence.** For a scheme `X` and `n` invertible on `X` there is an
exact sequence

```
  H¹(X, 𝔾ₘ) ──n·──▶ H¹(X, 𝔾ₘ) ──α──▶ H²(X, μₙ) ──β──▶ H²(X, 𝔾ₘ)[n] ⟶ 0,
```

that is, `0 → H¹(X, 𝔾ₘ)/n → H²(X, μₙ) → H²(X, 𝔾ₘ)[n] → 0`. It is recorded as the existence of
maps `α` and `β` with `ker α = n · H¹(X, 𝔾ₘ)`, `ker β = im α` and `im β = H²(X, 𝔾ₘ)[n]`.
(blueprint: `sk-prop-h2`) -/
theorem exists_exact_sheafH_rootsOfUnitySheaf_two (hn : IsUnit (n : Γ(X, ⊤))) :
    ∃ (α : X.CohomologicalPicardGroup →+ Sheaf.H (X.rootsOfUnitySheaf n) 2)
      (β : Sheaf.H (X.rootsOfUnitySheaf n) 2 →+ X.CohomologicalBrauerGroup),
      α.ker = (zsmulAddGroupHom (α := X.CohomologicalPicardGroup) (n : ℤ)).range ∧
        Function.Exact α β ∧ β.range = AddSubgroup.torsionBy X.CohomologicalBrauerGroup n :=
  -- Proof sketch: this is the middle part of the long exact sequence of
  -- `AlgebraicGeometry.Scheme.kummerSequence_shortExact`.
  sorry

/-- The constant étale sheaf `ℤ/n` on a scheme `X`, valued in abelian groups of the universe of
the small étale site. -/
noncomputable abbrev constantZMod : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))

/-- The global sections of the constant sheaf `ℤ/n` on a connected scheme are `ℤ/n`:
`H⁰(X_ét, ℤ/n) ≅ ℤ/n`.
(blueprint: `sk-thm-curveestimate`) -/
theorem nonempty_addEquiv_sheafH_zero_constantZMod [ConnectedSpace X] :
    Nonempty (Sheaf.H (X.constantZMod n) 0 ≃+ ZMod n) :=
  -- Proof sketch: the sections of a constant étale sheaf over `X` are the locally constant
  -- functions `X → ℤ/n`, and these are constant since `X` is connected.
  sorry

end AlgebraicGeometry.Scheme
