/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q116
-/
module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

import WeilConjectures.AlgebraicGeometry.Morphisms.StrictLocalRootsOfUnity
import WeilConjectures.AlgebraicGeometry.Morphisms.GaloisCoverBaseChange
import WeilConjectures.AlgebraicGeometry.Morphisms.FieldTorsorGaloisComponents
import Sheaf.RingTheory.RegularLocalLocalization
import Sheaf.RingTheory.RegularRingNormal
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleOpenGenericAlgebra
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.RingTheory.EtaleNormalRing
import WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.StrictlyHenselianQuotient
import WeilConjectures.RingTheory.RegularPrincipalPrimeLocalizationDvr
import WeilConjectures.RingTheory.DvrGaloisNormalizationRamificationDvd
import WeilConjectures.RingTheory.DvrTameTensorFactorUnramified
import Sheaf.AlgebraicGeometry.FinitePresentationOfFiniteLocallyNoetherian
import Sheaf.AlgebraicGeometry.EtaleAtPrimeFlatUnramifiedCriterion
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteStrictHenselianAlgebraEtaleSection

/-!
# Splitting punctured torsors after simultaneous parameter roots

Source: ILO, Travaux de Gabber, Exposé IX, Proposition 2.1, pp. 133--134,
specialized as in IX 2.2; Stacks Tags 0BRM and 0BMB
(blueprint: lem-per-snc-root-punctured-torsor-splitting).

The root algebra is written directly as the specified multivariate polynomial quotient.
This avoids importing the downstream parameter-root quotient theorem merely for its alias.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Adjoining the group-order roots of all boundary parameters splits the given torsor.
The isomorphism commutes with the maps to the root base; no equivariance is asserted.
Source: ILO IX Proposition 2.1, pp. 133--134, and IX 2.2; Stacks Tags 0BRM, 0BMB
(blueprint: lem-per-snc-root-punctured-torsor-splitting).

Proof. (1) The finite group has positive order. Strict-local roots of unity
[lem-sbc-strict-local-roots-of-unity] and the simultaneous-root structure theorem
[lem-per-snc-root-algebra-structure] give a strictly henselian regular Noetherian domain B,
finite free over R, with finite separable fraction-field extension E/K.
(2) Pull back the torsor [lem-sbc-galois-cover-base-change]. Decompose its actual generic
fibres into finite Galois field factors L_j/K of degrees dividing n, then into finite
separable factors F_a/E [lem-sbc-field-torsor-galois-components].
(3) B is normal by regular localization and regular normality
[lem-weil-pbc-regular-local-localization, lem-weil-pbc-regular-ring-normal]. Its integral
closure C_a in each F_a is finite by separability and Noetherian normality
[lem-weil-pbc-noetherian-normal-separable-integral-closure-finite]; set C = product C_a.
(4) The punctured cover algebra T embeds into its generic algebra D
[lem-sbc-finite-etale-open-generic-algebra]. This D is its total quotient algebra: nonzero
base elements are nonzerodivisors, and a zero field coordinate produces an annihilator
after clearing denominators. Etale ascent makes T normal
[lem-weil-pbc-etale-over-normal-ring-normal], hence integrally closed in D
[lem-weil-pbc-normal-ring-integrally-closed-total]. Finiteness makes T integral over the
punctured base [lem-weil-pbc-finite-algebra-is-integral]. Integral-closure localization
[lem-weil-pbc-integral-closure-commutes-localization] identifies C[1/f] with T.
(5) Quotienting by a parameter preserves regularity and strict henselianity
[lem-weil-pbc-regular-local-generators-regular-sequence,
lem-weil-pbc-strictly-henselian-quotient]. The root structure theorem on this quotient
shows that (t_i) and (x_i) are prime and contracted to one another.
(6) Their localizations are DVRs [lem-sbc-regular-principal-prime-localization-dvr].
The base change to R_(t_i) is already local, since its quotient by x_i is a field.
The ramification index is n, and these are all height-one primes containing f.
(7) Galois degree divisibility bounds ramification and residue degrees by divisors of n
[lem-sbc-dvr-galois-normalization-ramification-dvd]. Integral closures are finite as above.
(8) The DVR tame tensor-factor theorem [lem-sbc-dvr-tame-tensor-factor-unramified]
gives zero relative differentials at all boundary height-one primes. Identify these
local integral closures using integral-closure localization.
(9) Away from the boundary C[1/f] is already etale. Finite presentation over the
Noetherian base [pqf-lem-finite-fp-locnoeth] and the pointwise etale criterion
[lem-sc-etale-at-prime-flat-unramified-criterion] give the remaining differential
vanishings. Codimension-one purity [lem-per-finite-normalization-codimension-one-purity]
and finite-product etaleness [lem-weil-pbc-etale-algebra-finite-product] make Spec C
finite etale over Spec B.
(10) Its finite closed image [lem-weil-pbc-finite-closed-map-finite-fibres] contains the
generic point, hence is the whole base. Strict henselianity supplies a section
[lem-sbc-finite-strict-henselian-algebra-etale-section], which restricts to the torsor.
(11) Pull the torsor identity back along this section in its second factor
[def-sbc-normal-dominant-galois]. This gives the required disjoint union, with summand
map u ↦ g s(u), and preserves the structural maps. No connectedness is used. For r = 0,
the boundary-prime steps are empty, B is canonically R, f = 1, and the section argument
applies directly. For n = 1 this is the identity case. -/
theorem snc_root_punctured_torsor_splitting
    (R : Type u) [CommRing R] [IsRegularLocalRing R] [IsStrictlyHenselianLocalRing R]
    (r : ℕ) (t : Fin r → R)
    (_ht : ∀ i, t i ∈ IsLocalRing.maximalIdeal R)
    (_hparameters : ∃ s : List R,
      IsLocalRing.IsRegularSystemOfParameters (List.ofFn t ++ s))
    (G : Type v) [Group G] [Finite G]
    (_hn : IsUnit (Nat.card G : R))
    (cover : Scheme.GaloisCoverAction G (Spec (.of (Localization.Away (∏ i, t i))))) :
    ∃ e :
      pullback cover.π
        (Spec.map (CommRingCat.ofHom (Localization.awayMap
          (algebraMap R (MvPolynomial (Fin r) R ⧸ Ideal.span
            (Set.range (fun i ↦ MvPolynomial.X i ^ Nat.card G - MvPolynomial.C (t i)))))
          (∏ i, t i)))) ≅
      ∐ fun _ : G ↦ Spec (.of (Localization.Away
        (algebraMap R (MvPolynomial (Fin r) R ⧸ Ideal.span
          (Set.range (fun i ↦ MvPolynomial.X i ^ Nat.card G - MvPolynomial.C (t i))))
          (∏ i, t i)))),
      e.hom ≫ Sigma.desc (fun _ ↦ 𝟙 _) = pullback.snd _ _ := by
  sorry

end AlgebraicGeometry
