/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q92
-/
module

public import Sheaf.AlgebraicGeometry.CartierFractionCover
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

import Sheaf.AlgebraicGeometry.NormalEtaleComponentsClopen
import Sheaf.RingTheory.FlatBaseChangeReflexive
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import WeilConjectures.RingTheory.StrictHenselizationNoetherian
import WeilConjectures.RingTheory.EtaleColimitNormalLocalDomain
import WeilConjectures.RingTheory.EtaleNormalRing
import Sheaf.RingTheory.FiniteSeparableFibersOfEtaleColimit
import WeilConjectures.RingTheory.StrictHenselizationTriples

/-! # Cartierness of a fixed Weil divisor tested on strict local rings

Source: Stacks Project, Divisors, Tags 0EBM, 0AY6 and 0BE8; Algebra, Tag 00O1;
Etale, Tag 025P; ILO, Travaux de Gabber, VIII 5.3.8, printed p.125
(blueprint: lem-per-weil-divisor-strict-local-cartier-test).

The declarations include normality of the strict local ring, the finite coefficient
pullback, its etale compatibility, the fixed-multiple equivalence, and all effective clauses.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Strict local rings are Noetherian normal local domains, and the contracted
coefficients of a Weil divisor have finite support.
Source: Stacks, Tags 06LJ, 06DI, 07QM and 0AH1
(blueprint: lem-per-weil-divisor-strict-local-cartier-test).

Proof: write the strict henselization as the filtered pointed-etale colimit
(lem-weil-pbc-strict-henselization-triples). Noetherianity follows from
lem-sc-strict-henselization-noetherian and normal-domain localness from
lem-weil-pbc-etale-colimit-normal-local-domain. The strict local map is faithfully flat
by lem-sc-strict-henselization-faithfully-flat. Height-one primes contract to height-one
primes with unchanged valuations by lem-per-ind-etale-height-one-valuation. Only finitely
many downstairs coefficients are nonzero: E is locally finite and Y is quasi-compact.
Each has finitely many primes above it by
lem-weil-pbc-henselization-finite-separable-fibres. This proves finite support. -/
theorem strictLocalWeil_normal_finite (Y : Scheme.{u}) [IsNoetherian Y]
    (hnormal : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
      IsIntegrallyClosed (Y.presheaf.stalk y))
    (E : AlgebraicCycle Y ℤ)
    (hE : ∀ z : Y, E z ≠ 0 → ringKrullDim (Y.presheaf.stalk z) = 1)
    (y : Y) (K H : Type (max u v)) [Field K]
    [Algebra (IsLocalRing.ResidueField (Y.presheaf.stalk y)) K]
    [IsSepClosure (IsLocalRing.ResidueField (Y.presheaf.stalk y)) K]
    [Algebra (Y.presheaf.stalk y) K]
    [IsScalarTower (Y.presheaf.stalk y)
      (IsLocalRing.ResidueField (Y.presheaf.stalk y)) K]
    [CommRing H] [Algebra (Y.presheaf.stalk y) H]
    (P : Algebra.StrictHenselizationPresentationIn.{u, v} (Y.presheaf.stalk y) K H) :
    IsNoetherianRing H ∧ IsLocalRing H ∧ IsDomain H ∧ IsIntegrallyClosed H ∧
      Set.Finite {q : Ring.WeilHeightOnePrime H |
        localWeilCoefficient E y (algebraMap (Y.presheaf.stalk y) H) q ≠ 0} := by
  sorry

/-- The coefficient rule defines pullback to an etale neighborhood and commutes
with strict localization on that neighborhood.
Source: Stacks, Tags 025P and 0AH1
(blueprint: lem-per-weil-divisor-strict-local-cartier-test).

Proof: work on integral affine components, which are open by
lem-a1-normal-etale-components-clopen. Their rings are Noetherian normal by
lem-weil-pbc-etale-over-normal-ring-normal and lem-weil-pbc-finite-type-algebra-noetherian.
Apply lem-per-ind-etale-height-one-valuation on these components. Pull back a coefficient
by contraction of height-one primes; the finite-fiber result
lem-weil-pbc-henselization-finite-separable-fibres gives locally finite support. Prime
contraction is transitive, so pulling these coefficients further to any strict local
ring agrees with their direct contraction to Y. Zero coefficients remain zero. -/
theorem exists_etaleWeilPullback_strictLocal_compatible
    (Y : Scheme.{u}) [IsNoetherian Y]
    (hnormal : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
      IsIntegrallyClosed (Y.presheaf.stalk y))
    (E : AlgebraicCycle Y ℤ)
    (hE : ∀ z : Y, E z ≠ 0 → ringKrullDim (Y.presheaf.stalk z) = 1)
    (V : Scheme.{u}) (f : V ⟶ Y) [Etale f] :
    ∃ F : AlgebraicCycle V ℤ,
      (∀ z : V, F z = etaleWeilCoefficient f E z) ∧
      ∀ (z : V) (K H : Type (max u v)) [Field K]
        [Algebra (IsLocalRing.ResidueField (V.presheaf.stalk z)) K]
        [IsSepClosure (IsLocalRing.ResidueField (V.presheaf.stalk z)) K]
        [Algebra (V.presheaf.stalk z) K]
        [IsScalarTower (V.presheaf.stalk z)
          (IsLocalRing.ResidueField (V.presheaf.stalk z)) K]
        [CommRing H] [Algebra (V.presheaf.stalk z) H],
        Algebra.StrictHenselizationPresentationIn.{u, v} (V.presheaf.stalk z) K H →
        ∀ q : Ring.WeilHeightOnePrime H,
          localWeilCoefficient F z (algebraMap (V.presheaf.stalk z) H) q =
            localWeilCoefficient E (f z)
              ((algebraMap (V.presheaf.stalk z) H).comp (f.stalkMap z).hom) q := by
  sorry

/-- Cartierness of this fixed positive multiple is equivalent to a nonzero fraction
with exactly the prescribed normalized orders at every strict local ring.
Source: Stacks, Tags 0EBM, 0AY6, 0BE8, 0EB9, 0AVB, 00O1 and 0B8J;
ILO VIII 5.3.8, p.125 (blueprint: lem-per-weil-divisor-strict-local-cartier-test).

Proof:
1. Put D=aE. Cover Y componentwise by integral normal Noetherian affines using
lem-a1-normal-etale-components-clopen. The concrete lattices I_A(D) from
lem-per-divisorial-fractional-module-lattices glue by their localization formula to
one coherent finitely presented rank-one reflexive fractional sheaf I(D).
2. Present each strict local ring as the pointed-etale colimit using
lem-weil-pbc-strict-henselization-triples. The strict ring is Noetherian normal and the
stalk map is faithfully flat by lem-sc-strict-henselization-noetherian,
lem-weil-pbc-etale-colimit-normal-local-domain and
lem-sc-strict-henselization-faithfully-flat.
3. The height-one valuation comparison lem-per-ind-etale-height-one-valuation and the
finite-fiber lemma lem-weil-pbc-henselization-finite-separable-fibres give D_R=aE_R,
with the stated coefficient rule. Etale normality and finite-type Noetherianity give
the same calculation on etale neighborhoods; contraction is compatible in towers.
4. Flat base change preserves reflexivity by lem-per-flat-base-change-reflexive-modules.
Compare all height-one lattices using lem-per-divisorial-fractional-module-lattices
and the unchanged normalized valuations. Intersecting gives I(D)_y tensor R=I_R(D_R).
The same intersection formula gives I_R(div(c))=cR.
5. A Cartier equation restricts to the required fraction c, proving the forward
implication. Conversely the prescribed c makes the base-changed lattice free of rank
one. Descend finite projectivity along the faithfully flat local map using
lem-weil-pbc-finite-projective-descends-flat-local; its generic rank is one. Spread
a stalk basis by lem-trf-finite-presentation-stalk-basis-spread. Its orders are exactly
D by the height-one lattice formula. On overlaps the generated fractional modules
are equal, so the ratios are regular units. These are the Cartier fraction equations.
6. The empty scheme requires no equations. The zero divisor uses equation one. -/
theorem isCartierWeilMultiple_iff_strictLocal
    (Y : Scheme.{u}) [IsNoetherian Y]
    (hnormal : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
      IsIntegrallyClosed (Y.presheaf.stalk y))
    (E : AlgebraicCycle Y ℤ)
    (hE : ∀ z : Y, E z ≠ 0 → ringKrullDim (Y.presheaf.stalk z) = 1)
    (a : ℤ) (ha : 0 < a) :
    IsCartierWeilMultiple Y E a ↔ IsStrictLocallyPrincipalWeilMultiple.{u, v} Y E a := by
  sorry

/-- For an effective E the strict-local equations are regular nonzero elements;
the Cartier divisor is effective with the same support and has a single equation
on a pointed etale neighborhood of every geometric point.
Source: Stacks, Tags 0EBM, 0BE8 and 01WQ; ILO VIII 5.3.8, p.125
(blueprint: lem-per-weil-divisor-strict-local-cartier-test).

Proof: under the equivalent Cartier conditions the lattice I(aE) is an ideal, since
all coefficients are nonnegative (lem-per-divisorial-fractional-module-lattices).
Thus each strict-local generator belongs to R and is nonzero, and the spread bases
are regular non-zero-divisor equations. The ideal radical on an affine chart is the
intersection of the supported prime ideals. Since a>0 its support is the union of
the closures of the nonzero coefficients of E. A chart with a regular equation is
already an etale neighborhood via its open immersion, and a geometric point in it
lifts through that open immersion. For E=0 use equation one and empty support. -/
theorem effectiveWeilMultiple_strictLocal_equations
    (Y : Scheme.{u}) [IsNoetherian Y]
    (hnormal : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
      IsIntegrallyClosed (Y.presheaf.stalk y))
    (E : AlgebraicCycle Y ℤ)
    (hE : ∀ z : Y, E z ≠ 0 → ringKrullDim (Y.presheaf.stalk z) = 1)
    (a : ℤ) (ha : 0 < a) (hcartier : IsCartierWeilMultiple Y E a)
    (heffective : ∀ z : Y, 0 ≤ E z) :
    (∃ C : CartierFractionCover Y,
      C.HasCoefficients (fun z ↦ a * E z) ∧ C.IsEffective ∧
      C.support = {y | ∃ z : Y, E z ≠ 0 ∧ y ∈ closure ({z} : Set Y)}) ∧
    (∀ (y : Y) (K H : Type (max u v)) [Field K]
      [Algebra (IsLocalRing.ResidueField (Y.presheaf.stalk y)) K]
      [IsSepClosure (IsLocalRing.ResidueField (Y.presheaf.stalk y)) K]
      [Algebra (Y.presheaf.stalk y) K]
      [IsScalarTower (Y.presheaf.stalk y)
        (IsLocalRing.ResidueField (Y.presheaf.stalk y)) K]
      [CommRing H] [Algebra (Y.presheaf.stalk y) H],
      Algebra.StrictHenselizationPresentationIn.{u, v} (Y.presheaf.stalk y) K H →
      ∃ r : H, r ≠ 0 ∧ ∀ q : Ring.WeilHeightOnePrime H,
        Ring.weilOrder q r =
          a * localWeilCoefficient E y (algebraMap (Y.presheaf.stalk y) H) q) ∧
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (ybar : Spec (.of Ω) ⟶ Y),
      ∃ (V : Scheme.{u}) (f : V ⟶ Y) (_ : Etale f)
        (vbar : Spec (.of Ω) ⟶ V) (s : V.presheaf.obj (op ⊤)),
        vbar ≫ f = ybar ∧
        (∀ z : V, V.presheaf.germ ⊤ z trivial s ∈ nonZeroDivisors (V.presheaf.stalk z)) ∧
        ∀ z : V, ringKrullDim (V.presheaf.stalk z) = 1 →
          ((Ring.ord (V.presheaf.stalk z) (V.presheaf.germ ⊤ z trivial s)).toNat : ℤ) =
            a * E (f z) := by
  sorry

end AlgebraicGeometry.Scheme
