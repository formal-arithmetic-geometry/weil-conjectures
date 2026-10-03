/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

/-!
# The arithmetic genus and the cohomological degree of a sheaf of modules

Let `X` be a scheme over a field `k`. We define its arithmetic genus `dim_k H^1(X, 𝒪_X)` and the
degree `deg ℒ = χ(ℒ) - χ(𝒪_X)` of an invertible sheaf on it, both in terms of the cohomological
invariants `AlgebraicGeometry.Scheme.Modules.finrankH` and the Euler characteristic
`AlgebraicGeometry.Scheme.Modules.eulerChar`.

There is no group of Cartier or Weil divisors on a scheme in Mathlib. The degree is therefore
*defined* cohomologically, which is the standard alternative definition (Stacks 0AYQ). On a
smooth proper curve it agrees with the degree `dim_k Γ(D, 𝒪_D)` of divisors; this is part of
Riemann–Roch, stated in `WeilConjectures/AlgebraicGeometry/Curve/RiemannRoch.lean`.

## Main definitions

- `AlgebraicGeometry.Scheme.arithmeticGenus`: the arithmetic genus `dim_k H^1(X, 𝒪_X)`.
- `AlgebraicGeometry.Scheme.Modules.degree`: the degree `χ(ℒ) - χ(𝒪_X)` of an invertible sheaf.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_topologicalKrullDim_lt`: Grothendieck
  vanishing, which makes the `finsum` defining the Euler characteristic a finite sum on a
  noetherian scheme of finite dimension.
- `AlgebraicGeometry.Scheme.arithmeticGenus_pullback`: the arithmetic genus is invariant under
  base change along a field extension.
- `AlgebraicGeometry.Scheme.Modules.degree_congr`: the degree only depends on the isomorphism
  class of the sheaf.
- `AlgebraicGeometry.Scheme.Modules.degree_unit`: the structure sheaf has degree `0`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- **Grothendieck vanishing.** On a noetherian scheme `X` of dimension `n`, the cohomology of
every sheaf of modules vanishes in degrees `q > n`.

This is what makes the `finsum` defining `AlgebraicGeometry.Scheme.Modules.eulerChar` a finite
sum, hence makes `χ`, the genus and the degree meaningful, for instance on a curve, where
`n = 1`. -/
@[stacks 02UZ]
theorem Modules.subsingleton_H_of_topologicalKrullDim_lt {X : Scheme.{u}} [IsNoetherian X]
    (ℱ : X.Modules) {q : ℕ} (hq : topologicalKrullDim X < q) : Subsingleton (ℱ.H q) :=
  sorry

section Defs

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- The **arithmetic genus** `dim_k H^1(X, 𝒪_X)` of a `k`-scheme `X`.

When `X` is a smooth proper curve over `k` with `H⁰(X, 𝒪_X) = k`
(`AlgebraicGeometry.Scheme.GlobalSectionsBijective`) this is the genus of `X`; no hypotheses
are imposed on `X` here, so for other `X` the value carries no meaning.

For a smooth proper curve `X ↘ Spec k`, Serre duality identifies this with
`AlgebraicGeometry.Scheme.Hom.genus (X ↘ Spec k) = dim_k H^0(X, Ω¹_{X/k})`; see
`AlgebraicGeometry.Scheme.genus_eq_arithmeticGenus`. -/
noncomputable def arithmeticGenus : ℕ :=
  Modules.finrankH (X := X) k (SheafOfModules.unit X.ringCatSheaf) 1

end Defs

/-- **The genus is invariant under base change.** Let `X` be a quasi-compact quasi-separated
scheme over a field `k` and let `K/k` be a field extension. Then the base change
`X_K = X ×_{Spec k} Spec K` has `dim_K H¹(X_K, 𝒪_{X_K}) = dim_k H¹(X, 𝒪_X)`: by flat base change
`H¹(X_K, 𝒪_{X_K}) ≅ H¹(X, 𝒪_X) ⊗_k K` (Stacks 02KH).

(blueprint: `lem-pc-genus-base-change`) -/
theorem arithmeticGenus_pullback {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] (K : Type u) [Field K] [Algebra k K]
    [QuasiCompact (X ↘ Spec (.of k))] [QuasiSeparated (X ↘ Spec (.of k))] :
    arithmeticGenus K
        (Limits.pullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K)))) =
      arithmeticGenus k X :=
  sorry

section Degree

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- The **degree** `deg ℒ = χ(ℒ) - χ(𝒪_X)` of a sheaf of modules `ℒ` on a `k`-scheme `X`
(Stacks 0AYQ).

The value is the degree in the usual sense only for an invertible `ℒ` on a proper curve, where
it agrees with the degree of the associated divisor class; for other sheaves it is just a
difference of Euler characteristics. -/
noncomputable def Modules.degree (M : X.Modules) : ℤ :=
  M.eulerChar k - Modules.eulerChar (X := X) k (SheafOfModules.unit X.ringCatSheaf)

/-- The degree only depends on the isomorphism class of a sheaf of modules. -/
lemma Modules.degree_congr {M N : X.Modules} (e : M ≅ N) : M.degree k = N.degree k := by
  rw [degree, degree, eulerChar_congr k e]

@[simp]
lemma Modules.degree_unit :
    Modules.degree (X := X) k (SheafOfModules.unit X.ringCatSheaf) = 0 :=
  sub_self _

end Degree

end AlgebraicGeometry.Scheme
