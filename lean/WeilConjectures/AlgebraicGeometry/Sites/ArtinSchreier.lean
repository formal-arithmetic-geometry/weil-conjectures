/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Sheaf.AlgebraicGeometry.ArtinSchreierSequenceScheme
import Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift

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
    Subsingleton (Sheaf.H (X.constantZMod p) q) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hq
  let G := (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
    (Modules.etaleTensorSectionsSheaf (Modules.unit X))
  obtain ⟨iota, wp, hzero, hS⟩ := X.exists_artinSchreier_shortExact p hp
  have hG (j : ℕ) (hj : 0 < j) : Subsingleton (Sheaf.H G j) :=
    Etale.etale_affine_qcoherent_ulift X (Modules.unit X) j hj
  have hprev : Subsingleton (Sheaf.H G (n + 1)) := hG _ (by omega)
  have hnext : Subsingleton (Sheaf.H G ((n + 1) + 1)) := hG _ (by omega)
  let := hprev
  let := hnext
  have hsurj := Sheaf.H.δSucc_surjective hS (n + 1)
  have hvan : Subsingleton (Sheaf.H (X.constantZMod p) ((n + 1) + 1)) :=
    Function.Surjective.subsingleton hsurj
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hvan

end AlgebraicGeometry.Scheme
