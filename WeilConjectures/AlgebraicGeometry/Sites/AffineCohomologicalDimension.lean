/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport

/-!
# Torsion cohomological dimension of an affine scheme of finite type over a field

Let `K` be a field whose torsion étale cohomological dimension is at most `c`, i.e.
`H^q(Spec K_ét, F) = 0` for every torsion abelian sheaf `F` and every `q > c`, and let `X` be an
affine `K`-scheme of finite type of dimension at most `d`. Then `H^q(X_ét, F) = 0` for every
torsion abelian sheaf `F` on `X_ét` and every `q > d + c`
(`AlgebraicGeometry.Scheme.subsingleton_H_of_add_lt_of_isAffine`, Artin's affine vanishing
theorem). For `K` separably closed one may take `c = 0`
(`AlgebraicGeometry.Scheme.subsingleton_H_of_lt_of_isAffine_of_isSepClosed`).

This is the node `thm-sc-affine-torsion-cd` of the blueprint subsection `sk-prop-sf-cbc`, where
it is proved (induction on the dimension through Noether normalisation, a local calculation at
the strict henselisations and the Leray spectral sequence); it is stated here with `sorry`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Blueprint `thm-sc-affine-torsion-cd`: The affine torsion cohomological dimension bound.

Let `K` be a field with `cd_tor(K) ≤ c` and let `X` be an affine finite-type `K`-scheme of
dimension at most `d`. Then `cd_tor(X) ≤ d + c`: `H^q(X_ét, F) = 0` for every torsion abelian
étale sheaf `F` on `X` and every `q > d + c`. It is a node of the blueprint subsection
`sk-prop-sf-cbc`, where it is proved. -/
theorem subsingleton_H_of_add_lt_of_isAffine {K : Type u} [Field K] (c d : ℕ)
    (hK : ∀ F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}, F.IsTorsion →
      ∀ q : ℕ, c < q → Subsingleton (Sheaf.H F q))
    {X : Scheme.{u}} [IsAffine X] (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a]
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ)
    (hq : d + c < q) : Subsingleton (Sheaf.H F q) :=
  sorry

/-- The affine torsion cohomological dimension bound over a separably closed field: for an
affine finite-type `K`-scheme `X` of dimension at most `d`, `H^q(X_ét, F) = 0` for every torsion
abelian étale sheaf `F` and every `q > d`. This is
`AlgebraicGeometry.Scheme.subsingleton_H_of_add_lt_of_isAffine` (`thm-sc-affine-torsion-cd`) with
`c = 0`, which is allowed since `cd_tor(Spec K) = 0`
(`AlgebraicGeometry.Scheme.subsingleton_H_of_isSepClosed`, `lem-kun-cd-sep-closed-point`). -/
theorem subsingleton_H_of_lt_of_isAffine_of_isSepClosed {K : Type u} [Field K] [IsSepClosed K]
    (d : ℕ) {X : Scheme.{u}} [IsAffine X] (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a]
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ)
    (hq : d < q) : Subsingleton (Sheaf.H F q) :=
  subsingleton_H_of_add_lt_of_isAffine 0 d
    (fun G _ q hq ↦ by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hq
      simpa using subsingleton_H_of_isSepClosed K G n)
    a hX F hF q hq

end AlgebraicGeometry.Scheme
