/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Sites.PointCohomology

/-!
# Torsion cohomological dimension of a scheme of finite type over a field

Let `K` be a field whose torsion étale cohomological dimension is at most `c`, i.e.
`H^q(Spec K_ét, F) = 0` for every torsion abelian sheaf `F` and every `q > c`, and let `X` be a
`K`-scheme of finite type of dimension at most `d`. Then `H^q(X_ét, F) = 0` for every torsion
abelian sheaf `F` on `X_ét` and every `q > 2d + c`
(`AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_add_lt`). For `K` separably closed one may
take `c = 0` (`AlgebraicGeometry.Scheme.subsingleton_H_of_isSepClosed`).

This is the cohomological-dimension bound of the blueprint statement `sk-prop-sf-finiteness`;
it is the node `thm-sc-finite-type-torsion-cd` of the blueprint subsection `sk-prop-sf-cbc`, where
it is proved (Leray spectral sequence for the comparison with the Zariski site, the affine
bound, and Grothendieck vanishing), and is stated here with `sorry`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Blueprint `thm-sc-finite-type-torsion-cd`: Torsion cohomological dimension of a finite-type
scheme.

Let `K` be a field with `cd_tor(K) ≤ c` and let `X` be a finite-type `K`-scheme of dimension at
most `d`. Then `cd_tor(X) ≤ 2d + c`: `H^q(X_ét, F) = 0` for every torsion abelian étale sheaf `F`
on `X` and every `q > 2d + c`. This is the cohomological-dimension bound of the blueprint
statement `sk-prop-sf-finiteness`; it is a node of the blueprint subsection `sk-prop-sf-cbc`,
where it is proved. -/
theorem subsingleton_H_of_two_mul_add_lt {K : Type u} [Field K] (c d : ℕ)
    (hK : ∀ F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}, F.IsTorsion →
      ∀ q : ℕ, c < q → Subsingleton (Sheaf.H F q))
    {X : Scheme.{u}} (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ)
    (hq : 2 * d + c < q) : Subsingleton (Sheaf.H F q) :=
  sorry

end AlgebraicGeometry.Scheme
