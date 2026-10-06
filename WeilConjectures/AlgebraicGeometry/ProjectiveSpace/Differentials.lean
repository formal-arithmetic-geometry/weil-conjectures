/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# The sheaf of differentials of projective space

The sheaf of relative differentials `Ω¹_{ℙ/S}` of `ℙ = ℙ(n; S)` is locally free of rank `d`, where
`n` has `d + 1` elements: on the standard open `Uᵢ = D₊(xᵢ)`, the affine space with coordinates
`x_k / xᵢ` (`k ≠ i`), it is free on the differentials `d(x_k / xᵢ)`.

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.isFiniteLocallyFreeOfRank_relativeDifferentials`:
  `Ω¹_{ℙ(n; S)/S}` is finite locally free of rank `d`.

## TODO

- The canonical sheaf `ω_ℙ = Λᵈ Ω¹_{ℙ/S}` and the isomorphism `ω_ℙ ≅ 𝒪(-d-1)` sending the local
  bases `ηᵢ = (-1)ⁱ ⋀_{k ≠ i} d(x_k / xᵢ)` to the bases `eᵢ^{(-d-1)}` of the twist. This needs
  exterior powers of sheaves of modules, which are not available yet. For `d = 1`, where
  `ω = Ω¹`, it is `AlgebraicGeometry.ProjectiveLine.nonempty_relativeDifferentials_iso_twist`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (n : Type u) (S : Scheme.{u})

/-- **The differentials of projective space are locally free of rank `d`.** For `n` with
`Nat.card n = d + 1`, the sheaf of relative differentials `Ω¹_{ℙ(n; S)/S}` is finite locally
free of rank `d`: on the standard open `Uᵢ`, the affine space `𝔸({k // k ≠ i}; S)`, it is free
on the differentials `d(x_k / xᵢ)`, since Kähler differentials of a polynomial ring are free on
the differentials of the variables and commute with localization.

This is the first assertion of the blueprint lemma; its main assertion `ω_ℙ ≅ 𝒪(-d-1)` needs
the top exterior power `ω_ℙ = Λᵈ Ω¹_{ℙ/S}`, see the TODO in the module docstring.

(blueprint: `lem-pc-projective-space-canonical`) -/
theorem isFiniteLocallyFreeOfRank_relativeDifferentials {d : ℕ} (hn : Nat.card n = d + 1) :
    (ℙ(n; S) ↘ S).relativeDifferentials.IsFiniteLocallyFreeOfRank d :=
  sorry

end AlgebraicGeometry.ProjectiveSpace
