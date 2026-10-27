/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.RingTheory.SharpMonoidFacetForms
public import Sheaf.RingTheory.CompleteToricModel
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.RingTheory.CohenRing
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Sheaf.RingTheory.CompletedMonoidSupportProjection

/-!
# Facet lattice and supported-series coordinate cover

Source: ILO, Travaux de Gabber, Exposé VI 1.4 and 1.6(i)--(ii), printed pp. 69--70,
for the complete local models only. The coordinate-cover argument is the agent-formulated
auxiliary argument extracted from complete toric boundary-class injectivity
(blueprint: lem-trf-facet-lattice-supported-coordinate-cover).

The variables are indexed by `Fin r ⊕ Fin n`, with the two summands representing the
facet coordinates and the free parameters. The two exponent helpers and the retraction
predicate spell out the notation and assertions of this node; they choose no maps.
-/

@[expose] public section

universe u v

set_option autoImplicit false

noncomputable section

namespace ToricMonoid

/-- The natural exponent vector `ν(q)` for an enumeration of the primitive facet forms.
Its entries are nonnegative by `MonoidFacetForm`; `Int.toNat` expresses those entries
as natural numbers, without choosing any extra embedding.
Source: the agent coordinate-cover argument, in the notation of ILO VI 1.6(i)--(ii)
(blueprint: lem-trf-facet-lattice-supported-coordinate-cover). -/
def facetCoordinateExponent {P : Type u} [AddCommMonoid P] {r : ℕ}
    (facets : Fin r ≃ Algebra.MonoidFacetForm P) (q : P) : Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    (fun i : Fin r ↦ Int.toNat ((facets i).1 (Algebra.GrothendieckAddGroup.of q)))

/-- The combined exponent `(v,a)` of `X^v t^a`; this also defines `X^v` by taking `a=0`.
Source: the agent coordinate-cover argument, in the notation of ILO VI 1.6(i)--(ii)
(blueprint: lem-trf-facet-lattice-supported-coordinate-cover). -/
def facetParameterExponent {r n : ℕ} (v : Fin r →₀ ℕ) (a : Fin n →₀ ℕ) :
    (Fin r ⊕ Fin n) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Sum.elim v a)

open Classical in
/-- The prequotient assertions for the coordinate embedding and its coefficient-deletion
retraction: polynomial extension, injectivity, exact support, deletion of the other
coefficients, `B`-linearity through `ι`, and `ρι=1`.
Source: agent coordinate-cover argument, ILO VI 1.6(i)--(ii) for model notation only
(blueprint: lem-trf-facet-lattice-supported-coordinate-cover). -/
def IsFacetSupportedCoordinateRetraction
    {P : Type u} [AddCommMonoid P] {r n : ℕ}
    (facets : Fin r ≃ Algebra.MonoidFacetForm P)
    (L : Type v) [CommRing L] [IsLocalRing L]
    (ι : Complete L P n →ₐ[L] MvPowerSeries (Fin r ⊕ Fin n) L)
    (ρ : MvPowerSeries (Fin r ⊕ Fin n) L →+ Complete L P n) : Prop :=
  Function.Injective ι ∧
  (∀ (q : P) (a : Fin n →₀ ℕ) (c : L),
    ι (algebraMap (PolynomialRing L P n) (Complete L P n)
      (MvPolynomial.monomial a (AddMonoidAlgebra.single q c))) =
        MvPowerSeries.monomial (facetParameterExponent (facetCoordinateExponent facets q) a) c) ∧
  (∀ f : MvPowerSeries (Fin r ⊕ Fin n) L,
    (∃ b : Complete L P n, ι b = f) ↔
      ∀ e : (Fin r ⊕ Fin n) →₀ ℕ,
        (fun i : Fin r ↦ (e (Sum.inl i) : ℤ)) ∉ (Algebra.monoidFacetVector facets).range →
          MvPowerSeries.coeff e f = 0) ∧
  (∀ (f : MvPowerSeries (Fin r ⊕ Fin n) L) (e : (Fin r ⊕ Fin n) →₀ ℕ),
    MvPowerSeries.coeff e (ι (ρ f)) =
      if (fun i : Fin r ↦ (e (Sum.inl i) : ℤ)) ∈ (Algebra.monoidFacetVector facets).range
      then MvPowerSeries.coeff e f else 0) ∧
  (∀ (b : Complete L P n) (f : MvPowerSeries (Fin r ⊕ Fin n) L),
    ρ (ι b * f) = b * ρ f) ∧
  ∀ b : Complete L P n, ρ (ι b) = b

/-- The facets are finite and their primitive forms give the asserted lattice embedding
and the split coordinate cover, in both the field and the Cohen-parameter cases.
Normality and the Cohen congruence are retained, although the retraction argument does
not need them. Multiplication identities express linearity for the induced ring actions;
no unrelated module structures are assumed.

Source: ILO VI 1.4 and 1.6(i)--(ii), printed pp. 69--70, gives context and models only.
The following auxiliary proof is agent-formulated
(blueprint: lem-trf-facet-lattice-supported-coordinate-cover).

Proof: (1) Apply lem-trf-sharp-cone-primitive-facet-preparation to the fs sharp monoid.
It gives finitely many primitive normals, `G ↪ G ⊗ ℚ`, pointedness, `P=σ∩G`, and the
facet half-space description. The normals agree with def-trf-sharp-monoid-facet-forms
by uniqueness. (2) If `ν(g)=0`, both `g` and `-g` lie in the pointed cone, hence `g=0`.
The half-space description also gives `ν(P)=ν(G)∩ℕ^r`.
(3) Sum finite monoid generators to obtain `c`. For each facet some generator has
positive valuation, since otherwise its surjective normal vanishes on all of `G`.
All generator valuations are nonnegative, so every coordinate of `ν(c)` is positive.
(4) Put `M'=ν(G)×ℤ^n` and `Q'=M'∩ℕ^(r+n)`. The monoid isomorphism
`P×ℕ^n ≃ Q'` identifies the polynomial rings, the displayed monomial formulas,
the completion ideals, their powers, quotients and compatible sequences. `Q'` is
finitely generated. A field is complete for its zero maximal ideal. A Cohen ring has
finitely generated maximal ideal `(p)` and is complete by def-weil-pbc-cohen-ring.
Apply lem-trf-completed-monoid-support-projection to get `ι`, its exact supported image,
and the coefficient-deletion `B`-linear retraction `ρ`.
(5) In the Cohen case, if `ι(b)=ι(θ)a`, apply `ρ` to get `b=θρ(a)`; the converse
inclusion is multiplicativity of `ι`. Thus the contraction of `(ι(θ))` is `(θ)`,
and the induced quotient map is injective. If representatives differ by `ι(θ)h`,
their images under `ρ` differ by `θρ(h)`. This defines `ρ̄([a])=[ρ(a)]`.
The identities `ρ(ι(b)a)=bρ(a)` and `ρ(ι(b))=b` descend to `R`-linearity and the
retraction law. In the field case `D=A` and `ρ̄=ρ`.
(6) Coefficient deletion kills `X^v` outside `ν(G)` and fixes `X^{ν(q)}`. Descend
these equations to the quotient. If `P={0}`, there are no facets and the construction
is the identity power-series presentation. If `n=0`, omit the parameter coordinates;
if both vanish, `A=L`. Positivity is required only when `P` is nontrivial. -/
theorem exists_facetLattice_supportedCoordinateCover
    (P : Type u) [AddCommMonoid P]
    (hfs : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative P))
    (hsharp : ∀ a b : P, a + b = 0 → a = 0 ∧ b = 0) (n : ℕ) :
    Finite (Algebra.MonoidFacetForm P) ∧
    ∀ (r : ℕ) (facets : Fin r ≃ Algebra.MonoidFacetForm P),
      Function.Injective (Algebra.monoidFacetVector facets) ∧
      (∀ v : Fin r → ℤ,
        (∃ q : P, Algebra.monoidFacetVector facets (Algebra.GrothendieckAddGroup.of q) = v) ↔
          v ∈ (Algebra.monoidFacetVector facets).range ∧ ∀ i : Fin r, 0 ≤ v i) ∧
      (¬ Subsingleton P → ∃ c : P, ∀ i : Fin r,
        0 < Algebra.monoidFacetVector facets (Algebra.GrothendieckAddGroup.of c) i) ∧
      (∀ (k : Type v) [Field k],
        IsDomain (Complete k P n) → IsIntegrallyClosed (Complete k P n) →
        ∃ (ι : Complete k P n →ₐ[k] MvPowerSeries (Fin r ⊕ Fin n) k)
          (ρ : MvPowerSeries (Fin r ⊕ Fin n) k →+ Complete k P n),
          IsFacetSupportedCoordinateRetraction facets k ι ρ ∧
          (∀ v : Fin r →₀ ℕ,
            (fun i : Fin r ↦ (v i : ℤ)) ∉ (Algebra.monoidFacetVector facets).range →
              ρ (MvPowerSeries.monomial (facetParameterExponent v (0 : Fin n →₀ ℕ)) 1) = 0) ∧
          ∀ q : P,
            ρ (MvPowerSeries.monomial
              (facetParameterExponent (facetCoordinateExponent facets q) (0 : Fin n →₀ ℕ)) 1) =
                monomial k P n q) ∧
      (∀ (C : Type v) [CommRing C] [IsLocalRing C] (p : ℕ), IsCohenRing p C →
        ∀ θ : Complete C P n,
          θ - (p : Complete C P n) ∈ completedChartIdeal C P n →
          IsDomain (Complete C P n ⧸ Ideal.span {θ}) →
          IsIntegrallyClosed (Complete C P n ⧸ Ideal.span {θ}) →
          ∃ (ι : Complete C P n →ₐ[C] MvPowerSeries (Fin r ⊕ Fin n) C)
            (ρ : MvPowerSeries (Fin r ⊕ Fin n) C →+ Complete C P n),
            IsFacetSupportedCoordinateRetraction facets C ι ρ ∧
            (Ideal.span {ι θ}).comap ι.toRingHom = Ideal.span {θ} ∧
            ∃ (j : (Complete C P n ⧸ Ideal.span {θ}) →+*
                (MvPowerSeries (Fin r ⊕ Fin n) C ⧸ Ideal.span {ι θ}))
              (ρbar : (MvPowerSeries (Fin r ⊕ Fin n) C ⧸ Ideal.span {ι θ}) →+
                (Complete C P n ⧸ Ideal.span {θ})),
              (∀ b : Complete C P n,
                j (Ideal.Quotient.mk (Ideal.span {θ}) b) =
                  Ideal.Quotient.mk (Ideal.span {ι θ}) (ι b)) ∧
              Function.Injective j ∧
              (∀ a : MvPowerSeries (Fin r ⊕ Fin n) C,
                ρbar (Ideal.Quotient.mk (Ideal.span {ι θ}) a) =
                  Ideal.Quotient.mk (Ideal.span {θ}) (ρ a)) ∧
              (∀ (b : Complete C P n ⧸ Ideal.span {θ})
                (d : MvPowerSeries (Fin r ⊕ Fin n) C ⧸ Ideal.span {ι θ}),
                ρbar (j b * d) = b * ρbar d) ∧
              (∀ b : Complete C P n ⧸ Ideal.span {θ}, ρbar (j b) = b) ∧
              (∀ v : Fin r →₀ ℕ,
                (fun i : Fin r ↦ (v i : ℤ)) ∉ (Algebra.monoidFacetVector facets).range →
                  ρbar (Ideal.Quotient.mk (Ideal.span {ι θ})
                    (MvPowerSeries.monomial (facetParameterExponent v (0 : Fin n →₀ ℕ)) 1)) =
                      0) ∧
              ∀ q : P,
                ρbar (Ideal.Quotient.mk (Ideal.span {ι θ})
                  (MvPowerSeries.monomial
                    (facetParameterExponent (facetCoordinateExponent facets q)
                      (0 : Fin n →₀ ℕ)) 1)) =
                    Ideal.Quotient.mk (Ideal.span {θ}) (monomial C P n q)) := by
  sorry

end ToricMonoid
