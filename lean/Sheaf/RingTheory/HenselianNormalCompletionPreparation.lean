/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.RingTheory.GeneralizedHenselizationAtPrime
public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Topology.Sober
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import WeilConjectures.RingTheory.PairHenselization
import Sheaf.RingTheory.HenselizationUniversalProperty
import Sheaf.RingTheory.HenselianFactorizationCriterion
import Sheaf.RingTheory.PairHenselizationNoetherianCompletion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.RingTheory.CompletionDimension
import Sheaf.TraceFormula.HenselizationPrimeIndEtale
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.RingTheory.QuasiExcellentNagata
import Sheaf.RingTheory.GRingOfWeaklyEtale
import Sheaf.RingTheory.NagataJTwoOfWeaklyEtale
import Sheaf.RingTheory.NagataRing
import Sheaf.RingTheory.JapaneseDomain
import Sheaf.AlgebraicGeometry.ComponentwiseNormalizationAffineCharts
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import Sheaf.RingTheory.FiniteTypeGRing
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Sheaf.RingTheory.GRing
import Sheaf.RingTheory.RegularRingNormal
import Sheaf.RingTheory.NormalOfFlatNormalFibers
import Mathlib.RingTheory.RingHom.Flat
import Sheaf.RingTheory.CompletionFiniteExtension
import Sheaf.RingTheory.LocalCompletionQuotient
import Sheaf.RingTheory.RatliffFormalCatenarity
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.AlgebraicGeometry.ExcellentNormalizationPreparation
import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp

import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Henselian normalization and normal completion

Source: Travaux de Gabber, Expose I, Proposition 6.2, Corollary 6.3(ii), Theorem 8.1,
and Expose III, Proposition 6.2, first reductions (pp. 14--16, 43--44);
Stacks Project, Tags 06DH, 06LK and 0C23
(blueprint: lem-per-henselian-normal-completion-preparation).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Henselian normalization preparation, including arbitrary normal excellent local completion.
Source: Travaux de Gabber, I 6.2, 6.3(ii), 8.1 and III 6.2 (pp. 14--16, 43--44);
Stacks Project, Tags 06DH, 06LK and 0C23
(blueprint: lem-per-henselian-normal-completion-preparation).

Proof plan:
1. Identify $R_{\mathfrak m}=R$, since all denominators outside $\mathfrak m$ are units. First
   identify ordinary henselization with the henselization of the pair $(R,\mathfrak m)$. Write
   $(C,J)$ for the latter. The pair-henselization theorem gives $J=\mathfrak mC$, $C/J=R/\mathfrak
   m$ and a henselian pair. The henselian factorization criterion puts $J$ in the Jacobson
   radical. Since $C/J$ is a field, $J$ is the unique maximal ideal of $C$. Thus $C$ is henselian
   local and $R\to C$ is local. For a local map $R\to T$ with $T$ henselian local, the pair
   universal property gives a unique $R$-map $C\to T$; it is local because it carries $J=\mathfrak
   mC$ into the maximal ideal of $T$. Hence $C$ and $H$ have the same ordinary local universal
   property. The unique local maps between them compose to the identities by uniqueness,
   identifying $C=H$, $J=\mathfrak mH$, and $H/\mathfrak mH=R/\mathfrak m$. Uses:
   lem-weil-pbc-pair-henselization, lem-weil-pbc-henselization-universal-property,
   lem-weil-pbc-henselian-factorization-criterion, def-weil-pbc-henselization-at-prime.
2. The Noetherian pair-henselization theorem applied with $I=\mathfrak m$ now gives that $H$ is
   Noetherian, $R\to H$ is flat, and $\widehat R\cong\widehat H$. It also identifies $H$ with a
   filtered colimit of etale $R$-algebras. Each such algebra is reduced by etale preservation of
   reducedness, using the reducedness criterion on affine sections. This implies that $H$ is
   reduced: if $x^n=0$ in the colimit, represent $x$ at a stage and pass to a later stage at which
   its $n$th power is zero; reducedness at that stage makes its image, and therefore $x$, zero.
   Uses: lem-weil-pbc-henselization-noetherian-completion, lem-weil-pbc-pair-henselization,
   etale-proposition-etale-reduced, def-pc-reduced-scheme.
3. Apply invariance of dimension under completion to the two Noetherian local rings $R$ and $H$.
   The completion isomorphism in Step 2 gives $\dim R=\dim\widehat R=\dim\widehat H=\dim H$. Uses:
   lem-weil-pbc-completion-dimension, lem-weil-pbc-henselization-noetherian-completion.
4. The ordinary henselization map is ind-etale, hence weakly etale. Quasi-excellence of $R$
   supplies the G-ring and J-2 properties and, by quasi-excellent implies Nagata, the Nagata
   property. The weakly etale G-ring ascent theorem and the weakly etale Nagata/J-2 ascent theorem
   apply to the Noetherian rings $R,H$. They give that $H$ is a G-ring and J-2, hence
   quasi-excellent. Universal catenarity is proved below, rather than assumed here. Uses:
   lem-trf-henselization-prime-ind-etale, lem-weil-pbc-ind-etale-stability,
   def-exc-excellent-ring, lem-exc-quasi-excellent-nagata, lem-exc-weakly-etale-g-ring,
   lem-exc-weakly-etale-nagata-j2.
5. Apply quasi-excellent implies Nagata to $H$. Enumerate its finitely many minimal primes
   $\mathfrak p_a$ and set $A_a=H/\mathfrak p_a$, $K_a=\operatorname{Frac}(A_a)$ and $B_a$ equal
   to the integral closure of $A_a$ in $K_a$. The normalization affine-chart theorem identifies
   the componentwise normalization of $\operatorname{Spec}H$ with $\operatorname{Spec}(\prod_a
   B_a)$, with structural map $h\mapsto(h\bmod\mathfrak p_a)_a$. By the Nagata definition each
   $A_a$ is Japanese; taking the degree-one extension $K_a/K_a$ in that definition makes $B_a$
   finite over $A_a$, and therefore finite over $H$. The integral-closure theorem makes each $B_a$
   a normal domain. Uses: lem-exc-quasi-excellent-nagata, def-weil-pbc-nagata-ring,
   def-weil-pbc-japanese-domain, lem-per-componentwise-normalization-affine-charts,
   lem-weil-pbc-integral-closure-finite-extension-normal.
6. Apply finite-over-henselian decomposition to each finite $H$-algebra $B_a$. Since $B_a$ is a
   nonzero domain, the product can have only one nonzero local factor: two would give an
   idempotent different from $0$ and $1$. Thus each $B_a$ is henselian local and $H\to B_a$ is
   local. A finite module algebra is of finite type, so the finite-type Noetherian and G-ring
   ascent theorems give that $B_a$ is Noetherian and a G-ring. Normal-domain localization shows it
   is also a normal ring in the local-at-every-prime sense. Uses:
   lem-weil-pbc-finite-over-henselian-local-product, lem-weil-pbc-finite-type-algebra-noetherian,
   lem-weil-pbc-finite-type-over-g-ring, lem-weil-pbc-localization-normal-domain.
7. For each $B_a$, its completion is Noetherian and local by the completion theorems. As $B_a$ is
   a local G-ring, the definition makes $B_a\to\widehat B_a$ regular. Its fibres are regular
   rings, hence normal rings by regular implies normal. Apply flat ascent of normality with normal
   fibres: the source and target are Noetherian, the map is flat, all its fibres are normal, and
   its source is normal by Step 6. It follows that $\widehat B_a$ is a normal ring. A normal local
   ring is a normal domain: its localization at its maximal ideal is a normal domain by the
   definition, and that localization is the ring itself since every element outside the maximal
   ideal is a unit. The completion map is faithfully flat by the local-completion theorem. Uses:
   lem-weil-pbc-adic-completion-noetherian, lem-weil-pbc-local-completion-local-ring,
   def-weil-pbc-g-ring, lem-weil-pbc-regular-ring-normal,
   lem-weil-pbc-flat-normal-fibres-noetherian-normal, def-weil-pbc-normal-ring,
   lem-weil-pbc-local-completion-faithfully-flat.
8. Fix $a$. The quotient $A_a$ is Noetherian local, and $A_a\hookrightarrow B_a$ is injective and
   finite; the maximal ideal of $B_a$ contracts to that of $A_a$ by Step 6. The completion
   $\widehat A_a$ is flat over $A_a$, so tensoring this injection gives an injection $\widehat
   A_a\hookrightarrow\widehat A_a\otimes_{A_a}B_a$ by the definition of flatness. The
   finite-extension completion theorem identifies the latter ring with $\widehat B_a$: there is
   just one prime over the maximal ideal, because $B_a$ is local and integral over $A_a$ (a prime
   over a maximal ideal in an integral extension is maximal). Consequently $\widehat A_a$ is a
   domain, as it embeds in the domain $\widehat B_a$. Uses:
   lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-local-completion-faithfully-flat,
   def-weil-pbc-flat-ring-map, lem-weil-pbc-completion-finite-extension,
   lem-weil-pbc-integral-prime-over-maximal-maximal.
9. Completion of the quotient $H\twoheadrightarrow A_a$ identifies $\widehat H/\mathfrak
   p_a\widehat H$ with $\widehat A_a$. Step 8 shows this is a domain; its spectrum has a single
   irreducible component, and so is equidimensional. Apply the formal catenarity criterion to $H$:
   these assertions hold for every minimal prime $\mathfrak p_a$, and hence $H$ is universally
   catenary. Together with Step 4 this proves that $H$ is excellent. Each $B_a$ is a finite type
   $H$-algebra, so excellence of finite type algebras makes each $B_a$ excellent. Uses:
   lem-weil-pbc-local-completion-quotient, lem-per-ratliff-formal-catenarity,
   def-exc-excellent-ring, lem-exc-finite-type-localization-excellent.
10. Now apply excellent-normalization preparation to $X=\operatorname{Spec}H$. Steps 2 and 9
   verify that it is reduced Noetherian excellent. Its normalization is the one identified in Step
   5. The cited theorem gives that $\coprod_a\operatorname{Spec}B_a\to\operatorname{Spec}H$ is
   finite and surjective and is an isomorphism over a dense open containing every generic point.
   This uses the already proved excellence, so there is no use of normalization finiteness to
   assume universal catenarity in Step 9. Uses: lem-per-excellent-normalization-preparation,
   lem-per-componentwise-normalization-affine-charts.
11. The map $A_a\hookrightarrow B_a$ is integral and injective, so $\dim B_a=\dim A_a$. The
   quotient spectrum $\operatorname{Spec}A_a$ is the closed subspace $V(\mathfrak
   p_a)\subseteq\operatorname{Spec}H$. Equivalently, lifting a strict chain of primes along the
   quotient gives a strict chain in $H$; hence $\dim A_a\leq\dim H$. This proves the required
   bound for every factor, without assuming the components of $H$ have equal dimensions. Uses:
   lem-weil-pbc-integral-injective-dimension-equal,
   lem-weil-pbc-spec-quotient-homeomorphism-zero-locus, def-weil-pbc-krull-dimension-ring.
12. For the separately quantified normal excellent Noetherian local domain $B$, apply the same
   completion argument as in Step 7: excellence supplies the G-ring property; normal-domain
   localization gives normality at every prime; regular formal fibres are normal by regular
   implies normal; and the Noetherian flat-normal-fibre ascent theorem gives normality of
   $\widehat B$. The completion-locality and Noetherianity theorems apply to $B$, so this normal
   ring is a local domain by localization at its maximal ideal. Local-completion faithful flatness
   gives the asserted $B\to\widehat B$. No henselian hypothesis on this arbitrary $B$ is used.
   Uses: def-exc-excellent-ring, def-weil-pbc-g-ring, lem-weil-pbc-localization-normal-domain,
   lem-weil-pbc-regular-ring-normal, lem-weil-pbc-flat-normal-fibres-noetherian-normal,
   lem-weil-pbc-adic-completion-noetherian, lem-weil-pbc-local-completion-local-ring,
   def-weil-pbc-normal-ring, lem-weil-pbc-local-completion-faithfully-flat.
13. Let $Z\subseteq\operatorname{Spec}R$ be nowhere dense and closed. In a Noetherian spectrum
   this means it contains no minimal prime: irreducible components are the closures of their
   generic minimal primes. Any nonempty open contains one of these generic points. Conversely, if
   a closed set contains a component, deleting the other finitely many components exhibits a
   nonempty ambient open in that closed set. These observations give the equivalence. Flat going
   down for $R\to H$ shows that every minimal prime $\mathfrak q$ of $H$ contracts to a minimal
   prime of $R$: a strictly smaller prime below its contraction would lift to a prime strictly
   below $\mathfrak q$. Thus $Z_H$ contains no minimal prime of $H$, and is nowhere dense. The
   generic prime $(0)$ of each $B_a$ contracts to $\mathfrak p_a$ in $H$ by its embedding
   $H/\mathfrak p_a\hookrightarrow B_a$; hence the inverse image $Z_a$ misses that generic point.
   Being a proper closed subset of an irreducible spectrum it is nowhere dense. Finally apply flat
   going down to $B_a\to\widehat B_a$: its minimal prime contracts to the unique minimal prime
   $(0)$ of $B_a$. Therefore the closed inverse image of $Z_a$ misses the generic point of
   $\operatorname{Spec}\widehat B_a$ and is nowhere dense as well. Uses: lem-sc-flat-going-down,
   lem-weil-pbc-henselization-noetherian-completion,
   lem-weil-pbc-spec-irreducible-components-minimal-primes,
   lem-weil-pbc-noetherian-finitely-many-components,
   lem-weil-pbc-local-completion-faithfully-flat.
-/
theorem henselian_normal_completion_preparation
    (R : Type u) [CommRing R] [IsLocalRing R] [_root_.IsReduced R]
    [IsNoetherianRing R] (hR : IsQuasiExcellent R)
    (H : Type v) [CommRing H] [HenselianLocalRing H]
    [Algebra (Localization.AtPrime (IsLocalRing.maximalIdeal R)) H]
    (hH : Algebra.IsHenselizationAtPrime' R (IsLocalRing.maximalIdeal R) H) :
    (_root_.IsReduced H ∧ IsNoetherianRing H ∧ IsExcellent H ∧
      HenselianLocalRing H ∧ ringKrullDim H = ringKrullDim R ∧
      ∃ (r : ℕ) (B : Fin r → CommRingCat.{v}) (f : ∀ a, H →+* B a),
        (∀ a, IsDomain (B a) ∧ IsIntegrallyClosed (B a) ∧
          IsExcellent (B a) ∧ IsNoetherianRing (B a) ∧ HenselianLocalRing (B a) ∧
          (f a).Finite ∧ ringKrullDim (B a) ≤ ringKrullDim H) ∧
        (∃ e : Spec (.of (∀ a, B a)) ≅ (Spec (.of H)).reducedNormalization,
          sigmaSpec B ≫ e.hom ≫ (Spec (.of H)).fromReducedNormalization =
            Sigma.desc (fun a ↦ Spec.map (CommRingCat.ofHom (f a)))) ∧
        IsFinite (Sigma.desc (fun a ↦ Spec.map (CommRingCat.ofHom (f a)))) ∧
        Surjective (Sigma.desc (fun a ↦ Spec.map (CommRingCat.ofHom (f a)))) ∧
        (∃ U : (Spec (.of H)).Opens, Dense (U : Set (Spec (.of H))) ∧
          (∀ Z : irreducibleComponents (Spec (.of H)), ∀ x : Spec (.of H),
            IsGenericPoint x Z.1 → x ∈ U) ∧
          IsIso ((Sigma.desc (fun a ↦ Spec.map (CommRingCat.ofHom (f a)))) ∣_ U)) ∧
        (∀ Z : Set (PrimeSpectrum R), IsClosed Z → IsNowhereDense Z →
          IsNowhereDense (PrimeSpectrum.comap
            ((algebraMap (Localization.AtPrime (IsLocalRing.maximalIdeal R)) H).comp
              (algebraMap R (Localization.AtPrime (IsLocalRing.maximalIdeal R)))) ⁻¹' Z) ∧
          ∀ a, IsNowhereDense (PrimeSpectrum.comap ((f a).comp
            ((algebraMap (Localization.AtPrime (IsLocalRing.maximalIdeal R)) H).comp
              (algebraMap R (Localization.AtPrime (IsLocalRing.maximalIdeal R))))) ⁻¹' Z) ∧
            ∀ [IsLocalRing (B a)], IsNowhereDense (PrimeSpectrum.comap
              ((algebraMap (B a) (AdicCompletion (IsLocalRing.maximalIdeal (B a)) (B a))).comp
                ((f a).comp
                  ((algebraMap (Localization.AtPrime (IsLocalRing.maximalIdeal R)) H).comp
                    (algebraMap R (Localization.AtPrime (IsLocalRing.maximalIdeal R)))))) ⁻¹'
                      Z))) ∧
    (∀ (A : Type w) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A],
      IsIntegrallyClosed A → IsExcellent A →
      IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal A) A) ∧
        IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) ∧
        IsLocalRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) ∧
        IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A) ∧
        Module.FaithfullyFlat A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := by
  sorry

end AlgebraicGeometry
