/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactificationRefinementLocalizing

/-!
# Invertibility of the integral refinement comparison

Source: Bhatt--Scholze, arXiv:1309.1198, Lemma 6.1.13 and Lemma 6.5.9(2),
with derived Nakayama from Stacks Tag 0G1U (blueprint:
lem-pur-integral-refinement-comparison-invertible).

The theorem states the integral comparison attached to a proper boundary refinement.
The object predicate in the theorem is the project's rendering of the full subcategory
`Dctf(X, Λ)`: bounded constructibility is `constantModelBoundedConstructible` and
finite Tor amplitude is `DerivedCategory.finiteTorAmplitude`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The integral refinement comparison is invertible on constructible finite-Tor objects.

Source: Bhatt--Scholze, arXiv:1309.1198, Lemma 6.1.13 (derived completeness of `j_!`),
Lemma 6.5.9(2) (derived direct image preserves completeness), and Stacks Tag 0G1U
(derived Nakayama); (blueprint: lem-pur-integral-refinement-comparison-invertible).

Here `c` is the compactification `j : X → Xbar`, `d` is `j' : X → Xbar'`, and the ambient
map of `r` is the proper map `h : Xbar' → Xbar` with `h j' = j` and `h⁻¹(X) = X`.

Proof (blueprint sk-thm-purity-transport, Step 3, expert re-plan #1267):
1. The refinement square is the case `Ybar = Xbar`, `U = X`, `Xbar = Xbar'`, `V = X`,
   `p = h`, `v = j'`, `u = j`, `p_V = id_X` of def-pur-integral-open-proper-exchange. It is
   Cartesian because `h⁻¹(X) = j'(X)`, and `p v = h j' = j = u p_V`. At `L = K` the exchange
   map `γ_h : j_! R(id_X)_* K → Rh_* j'_! K` is the adjunct under `j_! ⊣ j^*` of
   `R(id_X)_*(η_{j'})` followed by the inverse of the open restriction isomorphism
   `ρ : j^* Rh_* ≅ R(id_X)_* j'^*` of lem-pod-condensed-open-derived-calculus. The
   isomorphism `θ : j^* Rh_* j'_! K ≅ K` (`refinementTheta`) defining
   `localizingRefinementMap` is built from the same `ρ` and the same unit `η_{j'}`, using
   the identity normalization `ι : id ≅ R(id_X)_*` of
   lem-weil-derived-direct-image-composition. Hence `j^*` of `γ_h ∘ j_!(ι_K)`, followed
   by `θ`, is `1_K`. By the uniqueness clause of def-pur-integral-refinement-comparison,
   `localizingRefinementMap r K = γ_h ∘ j_!(ι_K)`. Since `j_!(ι_K)` is an isomorphism,
   the refinement map is invertible iff `γ_h` is invertible at `K`.
2. Part (a) of lem-pur-integral-open-proper-exchange-laws applies with `L = K` in
   `Dctf(X, O_E)`. The hypotheses are the same: `p`, `ℓ`, `k`, `E`, the condensed ring `O_E`,
   quasi-compact opens `j`, `j'`, proper `h` and a Cartesian square. It gives that `γ_h` is
   an isomorphism at `K`; by Step 1 the refinement map is an isomorphism. Part (a) is
   proved by the direct route: derived `ℓ`-completeness of `j_! K` and `Rh_* j'_! K`;
   reduction modulo `ℓ` commutes with `j_!` and `Rh_*` and carries the map to the torsion
   refinement map; torsion proper base change; derived Nakayama. Neither integral proper
   base change nor a compositor statement is used.
-/
theorem integralRefinementComparison_isIso
    (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (hp : 0 < p) (hpell : p ≠ ell)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    {f : X ⟶ Y} [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification.BoundaryCompactification f}
    (r : d ⟶ c)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ell E.1) X)))
    (hK : constantModelBoundedConstructible
        (Profinite.padicIntegersRingObj ell E.1) X K ∧
      DerivedCategory.finiteTorAmplitude _ K) :
    IsIso (localizingRefinementMap
      (Profinite.padicIntegersRingObj ell E.1) r K) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
