/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q140
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Universal injectivity from closed-fibre associated-prime coverage

Source: Stacks Project, More on Flatness, Tag 05DG,
`lemma-base-change-universally-flat-local` in `flat.tex`
(blueprint: lem-sfb-assassin-cover-universal-section-injection-local).
-/

@[expose] public section

set_option autoImplicit false

universe u v p w z t

open scoped TensorProduct

namespace Algebra

/-- A flat extension covering all element-annihilator associated primes of the closed fibre
of a relatively flat finitely presented module induces a universally injective map over the
local base. The algebra `B` and submonoid `W` give the specified localization presentation
of `S`; their scalar tower makes this presentation compatible with the original base map.
The quotient in `hcover` is the closed fibre, viewed as an `S`-module. The map in the
conclusion sends `n ⊗ l` to `(n ⊗ 1) ⊗ l`.

Source: Stacks Project, More on Flatness, Tag 05DG,
`lemma-base-change-universally-flat-local`
(blueprint: lem-sfb-assassin-cover-universal-section-injection-local).

Proof:
1. Write `k = R / m_R`, `C = S / m_R S`, and `Nbar = N / m_R N`. Reducing the
   localization presentation gives `C = Wbar⁻¹(B / m_R B)`. The latter quotient is a
   finite type algebra over the field `k`, hence Noetherian by
   lem-weil-pbc-finite-type-algebra-noetherian. Localization preserves this by
   lem-weil-pbc-localization-noetherian. The images of finite generators of `N` generate
   `Nbar` over `C`, so the hypotheses of Tag 05DE hold without Noetherian hypotheses on
   either original local ring.
2. Let `Sigma` be the scalars acting injectively on `Nbar`, and put `T = Sigma⁻¹S` and
   `T' = Sigma⁻¹S'`. By lem-sfb-fibre-regular-localization-spectrum (05DE), every maximal
   ideal of `T` contracts to an associated prime `q` of `Nbar`. Since `m_R` annihilates
   `Nbar`, this prime lies over `m_R`. Coverage supplies a prime of `S'` over `q`.
   It avoids `Sigma`, so lem-weil-pbc-localization-spectrum-embedding gives a prime of
   `T'` contracting to the given maximal ideal of `T`. Contractions agree by the
   fraction membership criterion. Thus every extended maximal ideal is proper.
3. The fraction maps identify `T'` with `T ⊗[S] S'`. By
   lem-weil-pbc-flat-module-base-change it is flat over `T`. Step 2 and
   lem-weil-pbc-flat-faithfully-flat-maximal-ideals make it faithfully flat, including
   the case `T = 0` where the maximal-ideal condition is empty.
4. By lem-sfb-fibre-regular-localization-universal-injection (05DF), the map from `N`
   to `Sigma⁻¹N` stays injective after tensoring over `R` with every module `L`.
5. Apply lem-weil-pbc-faithfully-flat-universally-injective to the `T`-module
   `X = (Sigma⁻¹N) ⊗[R] L` to get `X → X ⊗[T] T'` injective. Identify the target with
   `(Sigma⁻¹(N ⊗[S] S')) ⊗[R] L`: send `((n/s) ⊗ l) ⊗ (b/t)` to
   `((n ⊗ b)/(s*t)) ⊗ l`. The inverse sends `((n ⊗ b)/s) ⊗ l` to
   `((n/s) ⊗ l) ⊗ (b/1)`. Balancing and the fraction relation prove well-definedness;
   the composites are identities on the displayed generators.
6. Compose steps 4 and 5. The resulting injection sends `n ⊗ l` to
   `((n ⊗ 1)/1) ⊗ l`, so it factors through the map in the conclusion followed by
   localization. Injectivity of the composite gives injectivity of that map for every
   `L`, as required. The source proof's `N ⊗[R] S'` is a typo for `N ⊗[S] S'`.
-/
theorem universallyInjective_of_local_assassinCover
    {R : Type u} {S : Type v} {B : Type p} {S' : Type w} {N : Type z}
    [CommRing R] [CommRing S] [CommRing B] [CommRing S']
    [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra R B] [Algebra B S] [IsScalarTower R B S]
    [Algebra.FinitePresentation R B] (W : Submonoid B) [IsLocalization W S]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.FinitePresentation S N] [Module.Flat R N]
    [Algebra S S'] (hflat : (algebraMap S S').Flat)
    (hcover : ∀ q : PrimeSpectrum S,
      q.asIdeal.comap (algebraMap R S) = IsLocalRing.maximalIdeal R →
      q.asIdeal ∈ RingTheory.annihilatorAssociatedPrimes S
        (N ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) •
          (⊤ : Submodule S N))) →
      ∃ q' : PrimeSpectrum S', PrimeSpectrum.comap (algebraMap S S') q' = q) :
    ∀ (L : Type (max u v p w z t)) [AddCommGroup L] [Module R L],
      Function.Injective
        ((((TensorProduct.mk S N S').flip (1 : S')).restrictScalars R).rTensor L) := by
  sorry

end Algebra
