/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.FieldTheory.Perfect
import WeilConjectures.RingTheory.CohenRingsExist
import WeilConjectures.RingTheory.CohenRing
import WeilConjectures.RingTheory.CohenRingModPowFormallySmooth
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Sheaf.RingTheory.NormalDomainPrincipalQuotientAssociatedHeight
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.RingTheory.CompleteLocalExcellent
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import WeilConjectures.RingTheory.CompleteLocalQuotient
import Mathlib.RingTheory.Localization.Integral
import Sheaf.RingTheory.NagataOfCompleteLocal
import WeilConjectures.RingTheory.NagataRing
import WeilConjectures.RingTheory.JapaneseDomain
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Sheaf.RingTheory.FiniteOverCompleteLocalProduct
import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Localization.Basic
import WeilConjectures.RingTheory.InjectivePiLocalizationAssociatedPrimes
import Sheaf.RingTheory.ExcellentRing
import Sheaf.RingTheory.EppFiniteFamilyTraits
import Sheaf.RingTheory.EppPerfectCoreCompleteLocal

/-!
# A finite mixed-characteristic cover with reduced equidimensional special fibre

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé IV, 4.2.3, Lemma 4.2.4,
and the beginning of 4.2.5 (blueprint: lem-per-mixed-reduced-special-fibre-cover).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace IsLocalRing

/-- A complete Noetherian normal mixed-characteristic local domain admits a finite
injective local extension with reduced equidimensional special fibre over a complete
DVR with perfect residue field. Here `k₀` is `ResidueField W`, `k'` is `ResidueField C`,
and its specified inclusion is the canonical `ResidueField.map γ` induced by the
local map `γ`. The finite residue extension of `ResidueField A` is along
`ResidueField.map ι`. Equidimensionality is expressed using minimal primes of the
special-fibre ring itself.

Source: ILO, Travaux de Gabber, Exposé IV, 4.2.3, Lemma 4.2.4 and the first sentence
and special-fibre dimension assertion of 4.2.5.
(blueprint: lem-per-mixed-reduced-special-fibre-cover).

Proof (the ten steps of the DAG):
1. Put k = A/m and let k_* be the intersection of its p-power images. This is a
   perfect field. Choose its Cohen ring W₀ using lem-weil-pbc-cohen-rings-exist
   and def-weil-pbc-cohen-ring. Lift its residue inclusion successively modulo
   powers of m by lem-weil-pbc-cohen-ring-mod-pn-formally-smooth. Completeness
   gives W₀ → A. It is local on residues and injective, since every nonzero
   element of W₀ is a unit times a power of p, by
   lem-weil-pbc-dvr-unit-times-uniformizer-power, and A has characteristic zero.
2. There are finitely many minimal primes Pᵢ over pA by
   lem-sc-finite-minimal-primes-over-ideal. By
   lem-weil-pbc-minimal-support-prime-associated and
   lem-weil-pbc-normal-domain-principal-quotient-associated-height they have
   height one. The localization lemmas lem-weil-pbc-localization-noetherian and
   lem-weil-pbc-localization-normal-domain, then lem-sc-normal-dim1-dvr, make
   Tᵢ = A localized at Pᵢ a DVR. Its W₀-map is injective and local. Excellence
   follows from lem-per-complete-local-excellence and
   lem-exc-finite-type-localization-excellent.
3. By lem-weil-pbc-complete-local-quotient, A/Pᵢ is complete local of residue k.
   The coefficient inclusion of k_* in it and lem-per-epp-perfect-core-complete-local
   verify Epp's residue hypothesis for Frac(A/Pᵢ). Apply
   lem-per-epp-finite-family-traits simultaneously to the Tᵢ, obtaining W, π,
   its fraction field K and perfect residue field k₀.
4. Choose a field factor L of Frac(A) tensor K over Frac(W₀). It is a finite
   extension of Frac(A). Let C be the integral closure of A in L, a normal domain
   with fraction field L by lem-weil-pbc-integral-closure-finite-extension-normal.
   It is finite by lem-weil-pbc-complete-local-nagata, def-weil-pbc-nagata-ring and
   def-weil-pbc-japanese-domain. W embeds in C because its elements are integral
   over W₀, hence over A, using lem-weil-pbc-finite-algebra-is-integral.
5. By lem-weil-pbc-finite-over-complete-local-product, C is Noetherian complete
   local with maximal ideal over m. Thus A → C is local. Reducing finite module
   generators proves its residue extension finite. By
   lem-weil-pbc-finite-algebra-is-integral and
   lem-weil-pbc-integral-injective-dimension-equal, dim C = d. In W write
   p = unit times π^e with e > 0 by lem-weil-pbc-dvr-unit-times-uniformizer-power.
   Since p is in the maximal ideal of C, so is π, proving W → C local. Reduction
   supplies the specified inclusion k₀ → k'.
6. A height-one prime Q of C containing π contracts to a height-one prime P of A
   containing p: lem-weil-pbc-going-down-normal-integral excludes a two-step
   chain under P, and p is nonzero. Hence P is one of the Pᵢ.
7. Localize C at A minus Pᵢ. By
   lem-weil-pbc-integral-closure-commutes-localization this is the integral
   closure of Tᵢ in L. The image Dᵢ of Tᵢ tensor W is finite over Tᵢ, hence
   integral by lem-weil-pbc-finite-algebra-is-integral. Monic equations and
   lem-weil-pbc-integral-transitive identify the integral closures of Dᵢ and Tᵢ
   in L. Thus lem-per-epp-finite-family-traits gives reducedness modulo π there.
8. C localized at Q modulo π is a localization of that reduced special fibre.
   It is reduced: if (x/s)^n = 0, some inverted t kills x^n; then tx is nilpotent,
   hence zero, and x/s = 0. This applies to every height-one Q containing π.
9. For M = C/πC, lem-weil-pbc-normal-domain-principal-quotient-associated-height
   puts every associated prime at height one. By
   lem-weil-pbc-localization-at-prime-of-quotient its localized ring is the
   reduced ring of step 8. Every nilpotent is zero in all these localizations,
   hence zero by lem-weil-pbc-module-injects-localizations-associated-primes.
10. By lem-per-complete-local-excellence and def-exc-excellent-ring, C is catenary.
    The minimal-support and associated-height lemmas put every minimal prime Q
    over π at height one. A saturated chain from Q to the maximal ideal, preceded
    by (0) < Q, has length d. Thus dim(C/Q) = d-1, proving the asserted
    equidimensionality and dimension of the special fibre. -/
theorem exists_mixed_reduced_special_fibre_cover
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] [IsIntegrallyClosed A] [IsAdicComplete (maximalIdeal A) A]
    [CharZero A] (p : ℕ) (hp : p.Prime) (hres : ringChar (ResidueField A) = p)
    (d : ℕ) (hd : 2 ≤ d) (hdim : ringKrullDim A = (d : WithBot ℕ∞)) :
    ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (_ : CharZero W),
      ringChar (ResidueField W) = p ∧ PerfectField (ResidueField W) ∧
      ∃ π : W, maximalIdeal W = Ideal.span {π} ∧
      ∃ (C : Type u) (_ : CommRing C) (_ : IsNoetherianRing C) (_ : IsLocalRing C)
        (_ : IsDomain C) (_ : IsIntegrallyClosed C)
        (_ : IsAdicComplete (maximalIdeal C) C)
        (ι : A →+* C) (_ : IsLocalHom ι) (γ : W →+* C) (_ : IsLocalHom γ),
        Function.Injective ι ∧ ι.Finite ∧ Function.Injective γ ∧
        IsReduced (C ⧸ Ideal.span {γ π}) ∧
        ringKrullDim (C ⧸ Ideal.span {γ π}) = ((d - 1 : ℕ) : WithBot ℕ∞) ∧
        (∀ Q : Ideal (C ⧸ Ideal.span {γ π}),
          Q ∈ minimalPrimes (C ⧸ Ideal.span {γ π}) →
          ringKrullDim ((C ⧸ Ideal.span {γ π}) ⧸ Q) = ((d - 1 : ℕ) : WithBot ℕ∞)) ∧
        (ResidueField.map ι).Finite ∧ ringKrullDim C = (d : WithBot ℕ∞) := by
  sorry

end IsLocalRing
