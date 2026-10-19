/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.Algebra.Homology.IdealPowerTorsionFunctor
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Local cohomology spectral sequence for a sum of ideals

Source: Stacks Project, dualizing.tex, Tags 0BJC and 0955(3)
(blueprint: lem-per-local-cohomology-sum-spectral).

The spectral sequence is in the abelian category of module endofunctors. Thus its
pages, differentials, page-to-homology identifications and finite abutment filtration
are natural in the module. Evaluating at any module gives the stated spectral sequence.
-/

@[expose] public section

universe u

open CategoryTheory

namespace ModuleCat

/-- The natural first-quadrant spectral sequence
`H_I^p(H_J^q(M)) => H_{I+J}^{p+q}(M)`, using right derived ideal-power torsion.
The abutment is a decreasing filtration with `F⁰ = Hⁿ`, `Fⁿ⁺¹ = 0`, and
`Fᵖ / Fᵖ⁺¹ ≅ E∞^{p,n-p}`. These are subfunctors and natural isomorphisms, so
both the spectral sequence and its convergence are natural in `M`.

Source: Stacks Project, dualizing.tex, Tag 0BJC (lemma-local-cohomology-ss),
specialized to a module in degree zero, and Tag 0955(3).

Proof:
1. Work in `Mod(A)`, Grothendieck abelian (lem-weil-pbc-ring-modules-grothendieck-abelian).
   For every ideal `K`, `Γ_K` (def-sbc-ideal-power-torsion-functor) is additive and left
   exact (def-sp-left-exact-additive): for `u : N → P`, the kernel of its restriction to
   `Γ_K(N)` is the set of elements of `ker u` killed by a power of `K`, i.e. `Γ_K(ker u)`;
   for a finite product a common exponent is the maximum of the finitely many exponents, so
   `Γ_K` preserves finite products. Its action on maps restricts the original linear map.
2. Identify `Γ_I(Γ_J(N))` with `Γ_{I+J}(N)` by the identity on elements. The former is the
   set of `x` killed by `I^a` and `J^b` for some `a, b ≥ 1`; `(I+J)^{a+b}` is the sum of the
   `I^u J^v` with `u + v = a + b`, and each kills `x` since `u ≥ a` or `v ≥ b`. Conversely
   `(I+J)^c x = 0` gives `I^c x = J^c x = 0` by inclusion of ideals. These identifications
   commute with every module map, since all maps are restrictions; this is a natural
   isomorphism `Γ_I ∘ Γ_J ≅ Γ_{I+J}`, without a separate composition lemma.
3. For every injective `E`, `Γ_J(E)` is injective by lem-per-ideal-torsion-preserves-injectives
   with `K = J` (the Noetherian hypothesis). Resolving it by itself in degree zero
   (def-sp-injective-resolutions), `Γ_I` gives zero cohomology in positive degrees, so
   `Γ_J(E)` is `Γ_I`-acyclic (def-sp-acyclic). With Step 1 this verifies every condition of
   the composable pair (def-sp-composite-acyclicity) with `F = Γ_J`, `G = Γ_I`, and all three
   categories equal to `Mod(A)`.
4. Apply thm-sp-grothendieck to this pair and `M`: its functorial first-quadrant spectral
   sequence has `E₂^{p,q} = RᵖΓ_I(RᑫΓ_J(M)) = H_I^p(H_J^q(M))` and converges to
   `R^{p+q}(Γ_I ∘ Γ_J)(M)`. To identify this with `H_{I+J}^{p+q}(M)`, choose the same
   injective resolution `M → E•` for both functors; Step 2 gives an isomorphism of complexes
   `Γ_I(Γ_J(E•)) ≅ Γ_{I+J}(E•)` commuting with the differentials, and taking cohomology
   identifies the derived functors. The identification is natural: on a map of resolutions
   each component is the identity on the same torsion elements, and independence of
   resolutions is lem-sp-derived-well-defined.
5. Unpack the convergence (def-sp-convergence, def-sp-filtration): for each `n ≥ 0` the
   abutment has an exhaustive separated decreasing filtration `FᵖHⁿ` with
   `FᵖHⁿ / Fᵖ⁺¹Hⁿ ≅ E∞^{p,n-p}`. The first quadrant forces these quotients to vanish for
   `p < 0` and `p > n`, so the filtration is constant for `p ≤ 0` and for `p ≥ n + 1`;
   exhaustivity makes the first value `Hⁿ` and separatedness makes the second zero. Thus
   `Hⁿ = F⁰Hⁿ ⊇ ⋯ ⊇ Fⁿ⁺¹Hⁿ = 0`, transported along the natural abutment identification of
   Step 4. The spectral sequence and its filtration keep the functoriality in `M` of the
   Grothendieck construction, giving the same data in the module endofunctor category
   (`SpectralSequence.AbutsTo`, `E∞` at page `p + q + 2`).
(blueprint: lem-per-local-cohomology-sum-spectral) -/
theorem idealPowerTorsion_sum_spectralSequence
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I J : Ideal A) (_hI : I.FG) (_hJ : J.FG) :
    ∃ E : E₂CohomologicalSpectralSequenceNat (ModuleCat.{u} A ⥤ ModuleCat.{u} A),
      (∀ p q : ℕ, Nonempty ((E.page 2).X (p, q) ≅
        (idealPowerTorsion J).rightDerived q ⋙ (idealPowerTorsion I).rightDerived p)) ∧
      E.AbutsTo (fun n : ℕ ↦ (idealPowerTorsion (I ⊔ J)).rightDerived n) := by
  sorry

end ModuleCat
