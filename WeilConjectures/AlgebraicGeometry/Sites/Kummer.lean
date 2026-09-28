/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.AlgebraicGeometry.Sites.Gm

/-!
# The Kummer sequence

For a scheme `X` and `n ≥ 1` the *Kummer sequence* is the sequence of étale sheaves

```
  0 ──▶ μₙ ──kernel.ι──▶ 𝔾ₘ ──n • 𝟙──▶ 𝔾ₘ ──▶ 0
```

whose right hand map is the `n`-th power map (written additively as `n • 𝟙`) and whose sheaf
`μₙ` of `n`-th roots of unity is by definition its kernel. It is exact as soon as `n` is
invertible on `X`, by Hensel's lemma on the strictly henselian local rings.

## Main definitions

- `AlgebraicGeometry.Scheme.rootsOfUnitySheaf`: the sheaf `μₙ` of `n`-th roots of unity.
- `AlgebraicGeometry.Scheme.kummerSequence`: the Kummer sequence, as a short complex.

## Main statements

- `AlgebraicGeometry.Scheme.kummerSequence_shortExact`: the Kummer sequence is short exact
  when `n` is invertible on `X`.

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

end AlgebraicGeometry.Scheme
