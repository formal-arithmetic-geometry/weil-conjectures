/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
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
- `AlgebraicGeometry.Scheme.Modules.finiteDimensional_H_of_isProper`: the cohomology of a
  coherent sheaf on a proper scheme over a field is finite-dimensional.
- `AlgebraicGeometry.Scheme.Modules.degree_congr`: the degree only depends on the isomorphism
  class of the sheaf.
- `AlgebraicGeometry.Scheme.Modules.degree_unit`: the structure sheaf has degree `0`.
- `AlgebraicGeometry.Scheme.Modules.finrankH_eq_sum_of_pairwise_disjoint`: the cohomology of a
  finite disjoint union of open subschemes is the direct sum of the cohomologies of the pieces.
- `AlgebraicGeometry.Scheme.Modules.eulerChar_eq_sum_of_pairwise_disjoint`: the Euler
  characteristic is additive over a finite disjoint union of open subschemes.
-/

@[expose] public section

universe u

open CategoryTheory Function TopologicalSpace

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
`AlgebraicGeometry.Scheme.genus_eq_arithmeticGenus`.

(blueprint: `def-pc-genus`) -/
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

namespace Modules

section Additivity

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- **Cohomology of a finite disjoint union.** If `X` is the disjoint union of finitely many
open subschemes `U i`, then `H^q(X, M) ≅ ⊕ᵢ H^q(U i, M|_{U i})`; in particular, when
`H^q(X, M)` is finite-dimensional, `h^q(X, M) = ∑ᵢ h^q(U i, M|_{U i})`. Each `U i` is a scheme
over `k` through `X`.

This is used in the proof of blueprint `lem-sc-ample-positive-degree`. -/
theorem finrankH_eq_sum_of_pairwise_disjoint {ι : Type*} [Fintype ι] (U : ι → X.Opens)
    (hU : _root_.Pairwise (Disjoint on U)) (hcover : ⨆ i, U i = ⊤) (M : X.Modules) (q : ℕ)
    [FiniteDimensional k (M.H q)] :
    M.finrankH k q = ∑ i,
      letI : (U i).toScheme.Over (Spec (.of k)) := ⟨(U i).ι ≫ X ↘ Spec (.of k)⟩
      ((Scheme.Modules.pullback (U i).ι).obj M).finrankH k q :=
  sorry

/-- On a noetherian scheme, `h^q(X, M) = 0` above the dimension of `X`, by Grothendieck
vanishing. -/
theorem finrankH_eq_zero_of_topologicalKrullDim_lt [IsNoetherian X] (M : X.Modules) {q : ℕ}
    (hq : topologicalKrullDim X < q) : M.finrankH k q = 0 :=
  have := subsingleton_H_of_topologicalKrullDim_lt M hq
  Module.finrank_zero_of_subsingleton

/-- On a noetherian scheme of dimension at most `n`, the Euler characteristic is the finite sum
`∑_{q ≤ n} (-1)^q h^q(X, M)`. -/
theorem eulerChar_eq_sum_range [IsNoetherian X] (M : X.Modules) {n : ℕ}
    (hn : topologicalKrullDim X ≤ n) :
    M.eulerChar k = ∑ q ∈ Finset.range (n + 1), (-1) ^ q * (M.finrankH k q : ℤ) := by
  refine finsum_eq_sum_of_support_subset _ fun q hq ↦ ?_
  by_contra h
  refine hq ?_
  change (-1) ^ q * (M.finrankH k q : ℤ) = 0
  rw [finrankH_eq_zero_of_topologicalKrullDim_lt k M (hn.trans_lt ?_), Nat.cast_zero, mul_zero]
  simp only [Finset.coe_range, Set.mem_Iio, not_lt] at h
  exact_mod_cast Nat.lt_of_lt_of_le n.lt_succ_self h

/-- **The Euler characteristic is additive over a finite disjoint union.** If a noetherian
scheme `X` of finite dimension is the disjoint union of finitely many open subschemes `U i`,
and the cohomology of `M` is finite-dimensional, then `χ(X, M) = ∑ᵢ χ(U i, M|_{U i})`. -/
theorem eulerChar_eq_sum_of_pairwise_disjoint [IsNoetherian X] {n : ℕ}
    (hn : topologicalKrullDim X ≤ n) {ι : Type*}
    [Fintype ι] (U : ι → X.Opens) (hU : _root_.Pairwise (Disjoint on U)) (hcover : ⨆ i, U i = ⊤)
    (M : X.Modules) [∀ q, FiniteDimensional k (M.H q)] :
    M.eulerChar k = ∑ i,
      letI : (U i).toScheme.Over (Spec (.of k)) := ⟨(U i).ι ≫ X ↘ Spec (.of k)⟩
      ((Scheme.Modules.pullback (U i).ι).obj M).eulerChar k := by
  let (i : ι) : (U i).toScheme.Over (Spec (.of k)) := ⟨(U i).ι ≫ X ↘ Spec (.of k)⟩
  have (i : ι) : IsNoetherian (U i) :=
    { toCompactSpace := isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact _) }
  rw [eulerChar_eq_sum_range k M hn]
  simp_rw [finrankH_eq_sum_of_pairwise_disjoint k U hU hcover M, Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [eulerChar_eq_sum_range k _ ((topologicalKrullDim_subspace_le X (U i)).trans hn)]

end Additivity

end Modules

section Finiteness

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- **Finiteness of coherent cohomology.** On a scheme `X` proper over a field `k`, the
cohomology groups `H^q(X, ℱ)` of a coherent `𝒪_X`-module `ℱ` are finite-dimensional over `k`.
Coherence is spelled as quasi-coherence together with finite presentation. -/
@[stacks 02O5]
theorem Modules.finiteDimensional_H_of_isProper [IsProper (X ↘ Spec (.of k))] (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    FiniteDimensional k (ℱ.H q) :=
  sorry

end Finiteness

end AlgebraicGeometry.Scheme
