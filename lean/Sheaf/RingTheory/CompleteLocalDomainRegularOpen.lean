/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q90
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegular
import Sheaf.RingTheory.RegularLocalLocalization
import Sheaf.RingTheory.NonemptyRegularOpenSeparableAscent
import WeilConjectures.FieldTheory.PurelyInseparablePthRootTower
import Sheaf.RingTheory.Derivation.DetectNonPthPower
import Sheaf.RingTheory.Derivation.CompletionAndLocalization
import Sheaf.AlgebraicGeometry.DegreePExtensionRegular
import Sheaf.RingTheory.LocalizationOfRegularRing

/-!
# A complete Noetherian local domain has a nonempty regular open

Source: Stacks Project, More on Algebra, Tag 07PI, lemma-complete-Noetherian-domain-J-0,
with J-0 expanded by Tag 07P7, definition-J (blueprint: lem-per-complete-local-domain-regular-open).
-/

@[expose] public section

set_option autoImplicit false

universe u

open Set AlgebraicGeometry

/-- A complete Noetherian local domain has a nonempty open regular locus.

Source: Stacks Project, More on Algebra, Tag 07PI, lemma-complete-Noetherian-domain-J-0,
with J-0 expanded by Tag 07P7, definition-J (blueprint: lem-per-complete-local-domain-regular-open).

Proof (the node's ten steps).
1. By `IsLocalRing.complete_local_domain_finite_over_regular` choose a complete regular local
   subring `A₀ ⊆ R` with `R` finite over `A₀`; by
   `IsRegularLocalRing.localization_at_prime_and_isRegularRing` all of `Spec A₀` is a nonempty
   regular open (it contains `(0)`). `K = Frac R` is finite over `K₀ = Frac A₀`.
2. For an intermediate field `K₀ ⊆ M ⊆ K` put `B(M) = R ∩ M`; it is a finite `A₀`-module
   (a submodule of the Noetherian module `R`), hence Noetherian and of finite type over `A₀`.
3. Every `a ≠ 0` in `R` is integral over `A₀`; cancelling powers of `a` in a monic relation
   with nonzero constant term inverts `a` in `(A₀ \ 0)⁻¹ R`, so this localization is `K`,
   `Frac B(M) = M`, and each `x ∈ M` has `0 ≠ s ∈ A₀` with `s x ∈ B(M)`.
4. Let `M₀` be the separable closure of `K₀` in `K`. By
   `Algebra.exists_nonempty_open_regular_of_separable_fractionRing` applied to `A₀ → B(M₀)`,
   `Spec B(M₀)` has a nonempty regular open; if `M₀ = K` (e.g. characteristic zero) we are done.
5. In characteristic `p`, `IsPurelyInseparable.exists_pth_root_tower` gives
   `M₀ ⊂ M₁ ⊂ ⋯ ⊂ Mₙ = K`, `Mᵢ = Mᵢ₋₁(αᵢ)` of degree `p` with `αᵢ^p` not a `p`th power in
   `Mᵢ₋₁`. Induct on `i` for `Bᵢ = B(Mᵢ)`; write `B = Bᵢ₋₁`, `E = Bᵢ`, `M = Mᵢ₋₁`.
6. Choose `0 ≠ s ∈ A₀` with `z = s αᵢ ∈ E`; `b = z^p ∈ B` is not a `p`th power in `M`, and
   `B[T]/(T^p - b) ≅ C := B[z] ⊆ E` (degree `p` argument), so `Frac C = Frac E = Mᵢ`.
7. `Derivation.exists_apply_ne_zero_of_not_pth_power` gives a derivation `D` of `B` with
   `D b ≠ 0`; choose `h ≠ 0` with the principal open `D(h)` inside the regular open of `B`,
   and put `g = h · D b`, `S = B_g`.
8. `S` is Noetherian and regular (its local rings are those of `B` on `D(g)`); by
   `Derivation.exists_completion_and_unique_localization` `D` extends to `S` with `D b` a unit,
   so `Algebra.isRegularRing_quotient_X_pow_sub_of_isUnit_derivation` (with `n = p`) makes
   `S[T]/(T^p - b) ≅ C_g` regular.
9. Writing `A₀`-module generators `eⱼ = uⱼ / vⱼ` of `E` with `uⱼ, vⱼ ∈ C` and
   `c = ∏ vⱼ ≠ 0` (empty product `1`) gives `E_c = C_c`, hence `E_{gc} = C_{gc}`.
10. By `RingTheory.isRegularRing_of_localization` `E_{gc}` is regular; the principal open
   `D_E(gc)` is nonempty (it contains `(0)`, as `E` is a domain) and is the image of
   `Spec E_{gc}` (`AlgebraicGeometry.Scheme.isOpenImmersion_SpecMap_localizationAway`), its
   local rings being those of `E_{gc}`. At `i = n`, `Bₙ = R`, giving `U`.
These are Tags 07PI, 07PB, 09HI, 07PH, 07PE and 07PG, with the regular and localization notions
recorded by the cited dependencies.
-/
theorem IsLocalRing.exists_nonempty_open_regular_of_complete_domain
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
    ∃ U : Set (PrimeSpectrum R),
      IsOpen U ∧ U.Nonempty ∧
        ∀ p ∈ U, IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
  sorry
