/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension

/-!
# Torsion cohomological dimension of a scheme of finite type over a field

Let `K` be a field whose torsion étale cohomological dimension is at most `c`, i.e.
`H^q(Spec K_ét, F) = 0` for every torsion abelian sheaf `F` and every `q > c`, and let `X` be a
`K`-scheme of finite type of dimension at most `d`. Then `H^q(X_ét, F) = 0` for every torsion
abelian sheaf `F` on `X_ét` and every `q > 2d + c`
(`AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_add_lt`). For `K` separably closed one may
take `c = 0` (`AlgebraicGeometry.Scheme.subsingleton_H_of_isSepClosed`), so that `H^q(X_ét, F) = 0`
for `q > 2d` (`AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_lt_of_isSepClosed`).

This is the cohomological-dimension bound of the blueprint statement `sk-prop-sf-finiteness`;
it is the node `lemma-uniform-bounds-pro-etale-affines` of the blueprint subsection
`sk-prop-sf-cbc`. The proof follows the blueprint: the Leray spectral sequence
`Hᵖ(X_Zar, Rᵠε_* F) ⟹ Hᵖ⁺ᵠ(X_ét, F)` for the comparison `ε_*` of the étale with the Zariski site has
`Hᵖ = 0` for `p > d` by Grothendieck vanishing, and `Rᵠε_* F = 0` for `q > d + c` since `Rᵠε_* F` is
the sheafification of `V ↦ Hᵠ(V_ét, F|_V)`, which vanishes on affine opens `V` by the affine bound
`AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_of_isAffine`
; see
`WeilConjectures.AlgebraicGeometry.Sites.EtaleZariskiComparison`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Torsion cohomological dimension of a
finite-type scheme.

Let `K` be a field with `cd_tor(K) ≤ c` and let `X` be a finite-type `K`-scheme of dimension at
most `d`. Then `cd_tor(X) ≤ 2d + c`: `H^q(X_ét, F) = 0` for every torsion abelian étale sheaf `F`
on `X` and every `q > 2d + c`. This is the cohomological-dimension bound of the blueprint
statement `sk-prop-sf-finiteness`; it is a node of the blueprint subsection `sk-prop-sf-cbc`.

The Leray spectral sequence for the comparison `ε_*` of the étale with the Zariski site
(`AlgebraicGeometry.Scheme.subsingleton_H_of_isZero_rightDerived_etaleToZariski`) reduces the
bound to Grothendieck vanishing on `X_Zar` and to `Rᵠε_* F = 0` for `q > d + c`; the latter holds
since `Hᵠ(V_ét, F|_V) = 0` for `q > d + c` on every affine open `V` of `X` by the affine bound
`AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_of_isAffine` -/
theorem subsingleton_H_of_two_mul_add_lt {K : Type u} [Field K] (c d : ℕ)
    (hK : ∀ F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}, F.IsTorsion →
      ∀ q : ℕ, c < q → Subsingleton (Sheaf.H F q))
    {X : Scheme.{u}} (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ)
    (hq : 2 * d + c < q) : Subsingleton (Sheaf.H F q) := by
  have := LocallyOfFiniteType.isLocallyNoetherian a
  have := QuasiCompact.compactSpace_of_compactSpace a
  have : IsNoetherian X := {}
  refine subsingleton_H_of_isZero_rightDerived_etaleToZariski (e := d + c) hX F
    (fun p hp ↦ isZero_rightDerived_etaleToZariski_of_subsingleton_H F p fun U hU ↦ ?_) q
    (by lia)
  have : IsAffine U := hU
  exact hasTorsionCohomologicalDimensionLE_of_isAffine hK (U.ι ≫ a)
    ((topologicalKrullDim_subspace_le X U).trans hX) _
    (Etale.isTorsion_upperStar U.ι hF) p hp

/-- Finiteness and constructibility, the
cohomological-dimension bound over a separably closed field.

Let `K` be a separably closed field and let `X` be a finite-type `K`-scheme of dimension at most
`d`. Then `cd_tor(X) ≤ 2d`: `H^q(X_ét, F) = 0` for every torsion abelian étale sheaf `F` on `X`
and every `q > 2d`. This is the bound `cd_tor(X) ≤ 2d + c` of
`AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_add_lt`
 with `c = 0`, which is allowed since `cd_tor(Spec K) = 0`
(`AlgebraicGeometry.Scheme.subsingleton_H_of_isSepClosed`,
`lemma-cohomological-dimension-base-field--1`). -/
theorem subsingleton_H_of_two_mul_lt_of_isSepClosed {K : Type u} [Field K] [IsSepClosed K]
    (d : ℕ) {X : Scheme.{u}} (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ)
    (hq : 2 * d < q) : Subsingleton (Sheaf.H F q) :=
  subsingleton_H_of_two_mul_add_lt 0 d
    (fun G _ q hq ↦ by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hq
      simpa using subsingleton_H_of_isSepClosed K G n)
    a hX F hF q hq

end AlgebraicGeometry.Scheme
