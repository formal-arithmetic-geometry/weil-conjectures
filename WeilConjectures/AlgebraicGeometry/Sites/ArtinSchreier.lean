/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer

/-!
# The `p`-cohomological dimension of an affine scheme in characteristic `p`

Let `X` be an affine scheme on which the prime `p` vanishes. The Artin–Schreier sequence
`0 → ℤ/p → 𝔾ₐ → 𝔾ₐ → 0`, with second map `F - 1`, is exact on the small étale site of `X`, and
`Hᵠ(X_ét, 𝔾ₐ) = Hᵠ(X, 𝒪_X) = 0` for `q ≥ 1` since `X` is affine. Its long exact sequence gives
`Hᵠ(X_ét, ℤ/p) = 0` for `q ≥ 2`.

## Main statements

- `AlgebraicGeometry.Scheme.subsingleton_sheafH_constantZMod_of_isAffine`: `Hᵠ(X_ét, ℤ/p) = 0`
  for `q ≥ 2` on an affine scheme `X` with `p = 0` in `Γ(X, 𝒪_X)`.

## TODO

The étale sheaf `𝔾ₐ`, the Artin–Schreier sequence and the comparison of étale and Zariski
cohomology of quasi-coherent sheaves are not yet available; the statement is recorded without
proof.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- **Vanishing of `ℤ/p`-cohomology of an affine scheme in characteristic `p`.** Let `X` be an
affine scheme with `p = 0` in `Γ(X, 𝒪_X)`. Then `Hᵠ(X_ét, ℤ/p) = 0` for `q ≥ 2`. This combines
the exactness of the Artin–Schreier sequence `0 → ℤ/p → 𝔾ₐ → 𝔾ₐ → 0` (blueprint
`lem-sc-as-sequence`) with the vanishing of `Hᵠ(X_ét, 𝔾ₐ) = Hᵠ(X, 𝒪_X)` for `q ≥ 1` on an affine
scheme (blueprint `lem-sc-etale-affine-qcoherent`). -/
theorem subsingleton_sheafH_constantZMod_of_isAffine (X : Scheme.{u}) [IsAffine X] (p : ℕ)
    [Fact p.Prime] (hp : (p : Γ(X, ⊤)) = 0) (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H (X.constantZMod p) q) :=
  sorry

end AlgebraicGeometry.Scheme
