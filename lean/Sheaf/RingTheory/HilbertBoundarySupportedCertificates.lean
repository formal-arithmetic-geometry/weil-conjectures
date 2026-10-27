module

public import Sheaf.RingTheory.SupportedHomogeneousDivision
public import Sheaf.AlgebraicGeometry.RegularHilbertCoefficientDatum
public import Sheaf.AlgebraicGeometry.HilbertSamuelInvariant
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.Ideal.Colon
public import Sheaf.AlgebraicGeometry.MarkedIdealOrder
import Sheaf.RingTheory.HomogeneousDivisionExtraVariables

/-! # Hilbert comparison from supported boundary certificates

Source: ILO VIII 2.3.11--2.3.13, pp.93--94; Bierstone--Milman, Invent. Math.
128 (1997), (7.2), Lemmas 7.3--7.7 and Theorem 7.21(2), pp.262--269;
BMT arXiv:0905.3580, sections 5.2, 6.1--6.3 and 6.5--6.6.
(blueprint: lem-per-hilbert-boundary-supported-certificates)
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

namespace AlgebraicGeometry.HilbertCoefficient

/-- The coefficient of `Z^γ`, as a whole series in `W`.
Source: BM 1997, (7.2); BMT section 6.2.
(blueprint: lem-per-hilbert-boundary-supported-certificates). -/
def transverseCoefficient {L : Type u} [CommRing L] {m r : ℕ}
    (f : MvPowerSeries (Fin m ⊕ Fin r) L) (γ : Fin r →₀ ℕ) :
    MvPowerSeries (Fin m) L :=
  fun μ ↦ MvPowerSeries.coeff (Finsupp.mapDomain Sum.inl μ + fullVertex m γ) f

/-- The coefficient-order condition, expressed by powers of the coefficient-variable ideal.
Zero coefficients satisfy every power condition.
Source: BM 1997, (7.2); BMT sections 5.1 and 6.2.
(blueprint: lem-per-hilbert-boundary-supported-certificates). -/
def BoundaryOrderCondition {L : Type u} [Field L] {m r s : ℕ}
    (α : Fin s → Fin r →₀ ℕ) (f : Fin s → MvPowerSeries (Fin m ⊕ Fin r) L) : Prop :=
  ∀ (i : Fin s) (γ : Fin r →₀ ℕ), γ.degree < (α i).degree →
    transverseCoefficient (f i) γ ∈
      (Ideal.span (Set.range (MvPowerSeries.X (σ := Fin m) (R := L)))) ^
        ((α i).degree - γ.degree)

/-- The cumulative dimension of the actual truncated quotient.
Source: BM 1997, Corollary 3.20; BMT sections 6.1 and 6.5.
(blueprint: lem-per-hilbert-boundary-supported-certificates). -/
def boundaryHilbert {L : Type u} [Field L] {m r : ℕ}
    (I : Ideal (MvPowerSeries (Fin m ⊕ Fin r) L)) (t : ℕ) : ℕ :=
  Module.finrank L (MvPowerSeries (Fin m ⊕ Fin r) L ⧸
    (I ⊔ (Ideal.span (Set.range MvPowerSeries.X)) ^ (t + 1)))

/-- Saturation by a coefficient coordinate, constructed as the supremum of its power colons.
The colons form an increasing chain, so this is the ideal of series whose product with
some nonnegative power of that coordinate belongs to `I`.
Source: BM 1997, Lemmas 7.3 and 7.5, applied to coefficient-coordinate multiplication.
(blueprint: lem-per-hilbert-boundary-supported-certificates). -/
def boundarySaturation {L : Type u} [Field L] {m r : ℕ}
    (I : Ideal (MvPowerSeries (Fin m ⊕ Fin r) L)) (j : Fin m) :
    Ideal (MvPowerSeries (Fin m ⊕ Fin r) L) :=
  ⨆ v : ℕ, Submodule.colon I {(MvPowerSeries.X (Sum.inl j)) ^ v}

/-- The constant transverse Jacobian on a degree prefix's essential variables.
Source: BM 1997, (7.2)(4); BMT section 6.6.
(blueprint: lem-per-hilbert-boundary-supported-certificates). -/
def boundaryBlockJacobian {L : Type u} [Field L] {m r s : ℕ}
    (α : Fin s → Fin r →₀ ℕ) (pick : MonomialDiagram.EssentialVariables α → Fin s)
    (β : MonomialDiagram.EssentialVariables α → Fin r →₀ ℕ)
    (f : Fin s → MvPowerSeries (Fin m ⊕ Fin r) L) (q : ℕ) : L := by
  classical
  letI : Fintype (MonomialDiagram.EssentialVariables α) :=
    inferInstanceAs (Fintype {j : Fin r // ∃ i : Fin s, α i j ≠ 0})
  letI : Fintype {j : MonomialDiagram.EssentialVariables α // essential α q j.val} :=
    Fintype.ofFinite _
  exact Matrix.det (fun j l : {j : MonomialDiagram.EssentialVariables α //
      essential α q j.val} ↦
    MvPowerSeries.constantCoeff (MvPowerSeries.pderiv L (Sum.inr l.val.val)
      (iteratedPartial (fullVertex m (β j.val)) (f (pick j.val)))))

/-- The whole-series certificates outside the coefficient-order locus.
Only essential transverse variables require derivative choices, including when `s = 0`.
Source: BM 1997, (7.2)(2)--(5), Lemmas 7.3--7.7; BMT sections 6.2 and 6.5--6.6.
(blueprint: lem-per-hilbert-boundary-supported-certificates). -/
structure SupportedBoundaryCertificates {L : Type u} [Field L] {m r s : ℕ}
    (α : Fin s → Fin r →₀ ℕ) (A : Fin s → MvPolynomial (Fin r) L)
    (f : Fin s → MvPowerSeries (Fin m ⊕ Fin r) L) (Q : ℕ) where
  positive : ∀ i : Fin s, 0 < (α i).degree
  ordered : MonomialDiagram.IsOrderedVertexFamily (MonomialDiagram.generated α) α
  homogeneous : ∀ i : Fin s, (A i).IsHomogeneous (α i).degree
  pureDivision : ∀ q t : ℕ,
    MonomialDiagram.HasUniqueDivision
      (MonomialDiagram.generated (MonomialDiagram.prefixVertices α q))
      (MonomialDiagram.prefixVertices α q) (fun i ↦ A i.val) t
  transverseJet : ∀ (i : Fin s) (γ : Fin r →₀ ℕ), γ.degree ≤ (α i).degree →
    MvPowerSeries.coeff (fullVertex m γ) (f i) = (A i).coeff γ
  bound : ∀ i : Fin s, (α i).degree - 1 ≤ Q
  multiplication : ∀ (i : Fin s) (γ : Fin r →₀ ℕ),
    ∃ q : Fin s → MvPowerSeries (Fin m ⊕ Fin r) L,
      MvPowerSeries.monomial (fullVertex m γ) 1 * f i = ∑ h : Fin s, q h * f h ∧
      ∀ h : Fin s, supported (q h)
        (fun b ↦ b ∈ MonomialDiagram.quotientSupport (fun k ↦ fullVertex m (α k)) h)
  pick : MonomialDiagram.EssentialVariables α → Fin s
  beta : MonomialDiagram.EssentialVariables α → Fin r →₀ ℕ
  pick_vertex : ∀ j : MonomialDiagram.EssentialVariables α,
    α (pick j) = beta j + Finsupp.single j.val 1
  pick_prefix : ∀ (q : ℕ) (j : MonomialDiagram.EssentialVariables α),
    essential α q j.val → (α (pick j)).degree ≤ q
  block_membership : ∀ q : ℕ, (∃ i : Fin s, (α i).degree = q) →
    ∀ j : MonomialDiagram.EssentialVariables α, essential α q j.val →
      iteratedPartial (fullVertex m (beta j)) (f (pick j)) ∈ transverseIdeal α q
  block_jacobian : ∀ q : ℕ, (∃ i : Fin s, (α i).degree = q) →
    IsUnit (boundaryBlockJacobian α pick beta f q)
  later_derivatives : ∀ q : ℕ, (∃ i : Fin s, (α i).degree = q) →
    ∀ i : Fin s, q < (α i).degree → ∀ δ : Fin r →₀ ℕ,
      δ.degree ≤ Q → (∀ j : Fin r, δ j ≠ 0 → essential α q j) →
      inDiagram α q δ → iteratedPartial (fullVertex m δ) (f i) ∈ transverseIdeal α q

/-- The asserted Hilbert comparison, equality test, supported generation and saturation.
This predicate records conclusions and does not assume them in the certificates.
Source: BM 1997, (7.2), Lemmas 7.3--7.7; BMT sections 6.1--6.6.
(blueprint: lem-per-hilbert-boundary-supported-certificates). -/
def SupportedBoundaryConclusions {L : Type u} [Field L] {m r s : ℕ}
    (α : Fin s → Fin r →₀ ℕ) (f : Fin s → MvPowerSeries (Fin m ⊕ Fin r) L) : Prop :=
  HilbertSamuel.le (boundaryHilbert (Ideal.span (Set.range f)))
      (fun t ↦ {η : (Fin m ⊕ Fin r) →₀ ℕ |
        η ∉ MonomialDiagram.generated (fun i ↦ fullVertex m (α i)) ∧ η.degree ≤ t}.ncard) ∧
  ((∀ t : ℕ, boundaryHilbert (Ideal.span (Set.range f)) t =
      {η : (Fin m ⊕ Fin r) →₀ ℕ |
        η ∉ MonomialDiagram.generated (fun i ↦ fullVertex m (α i)) ∧ η.degree ≤ t}.ncard) ↔
    BoundaryOrderCondition α f) ∧
  (BoundaryOrderCondition α f →
    (∀ i : Fin s, (f i).order = ((α i).degree : ℕ∞)) ∧
    (∀ q t : ℕ, MonomialDiagram.HasUniqueDivision
      (MonomialDiagram.generated
        (fun i ↦ fullVertex m (MonomialDiagram.prefixVertices α q i)))
      (fun i ↦ fullVertex m (MonomialDiagram.prefixVertices α q i))
      (fun i ↦ MvPowerSeries.truncTotal ((α i.val).degree + 1)
        (MvPowerSeries.homogeneousComponent (α i.val).degree (f i.val))) t) ∧
    (∀ h ∈ Ideal.span (Set.range f),
      ∃ q : Fin s → MvPowerSeries (Fin m ⊕ Fin r) L,
        h = ∑ i : Fin s, q i * f i ∧ ∀ i : Fin s, supported (q i)
          (fun b ↦ b ∈ MonomialDiagram.quotientSupport (fun k ↦ fullVertex m (α k)) i)) ∧
    ∀ j : Fin m, boundarySaturation (Ideal.span (Set.range f)) j =
      Ideal.span (Set.range f)) ∧
  (∀ (j : Fin m) (h : MvPowerSeries (Fin m ⊕ Fin r) L),
    h ∈ boundarySaturation (Ideal.span (Set.range f)) j ↔
      ∃ v : ℕ, (MvPowerSeries.X (Sum.inl j)) ^ v * h ∈ Ideal.span (Set.range f)) ∧
  ∀ j : Fin m,
    (∀ t : ℕ, boundaryHilbert (boundarySaturation (Ideal.span (Set.range f)) j) t ≤
      boundaryHilbert (Ideal.span (Set.range f)) t) ∧
    (HilbertSamuel.lt (boundaryHilbert (Ideal.span (Set.range f)))
        (fun t ↦ {η : (Fin m ⊕ Fin r) →₀ ℕ |
          η ∉ MonomialDiagram.generated (fun i ↦ fullVertex m (α i)) ∧ η.degree ≤ t}.ncard) →
      HilbertSamuel.lt (boundaryHilbert (boundarySaturation (Ideal.span (Set.range f)) j))
        (fun t ↦ {η : (Fin m ⊕ Fin r) →₀ ℕ |
          η ∉ MonomialDiagram.generated (fun i ↦ fullVertex m (α i)) ∧ η.degree ≤ t}.ncard))

/-- Coordinate substitution in an exceptional-intersection chart. The two old boundary
coordinates become `e` and `e (ξ + V)`; every transverse variable is unchanged.
Source: BM 1997, Theorem 7.21(2), p.269; BMT section 5.2.
(blueprint: lem-per-hilbert-boundary-supported-certificates). -/
def boundaryChartVariables {L : Type u} [Field L] {m r : ℕ}
    (u v : Fin m) (ξ : L) : (Fin m ⊕ Fin r) → MvPowerSeries (Fin m ⊕ Fin r) L :=
  Sum.elim (fun j ↦ if j = u then MvPowerSeries.X (Sum.inl u)
    else if j = v then MvPowerSeries.X (Sum.inl u) *
      (MvPowerSeries.C ξ + MvPowerSeries.X (Sum.inl v))
    else MvPowerSeries.X (Sum.inl j)) (fun j ↦ MvPowerSeries.X (Sum.inr j))



/-- Whole-series certificates give the Hilbert comparison and its exact coefficient-order test.
The hypotheses are the actual supported identities, rather than an equality-locus-only basis.

Source: BM 1997, (7.2), Lemmas 7.3--7.7; BMT sections 6.1--6.6;
ILO VIII 2.3.11--2.3.13.
(blueprint: lem-per-hilbert-boundary-supported-certificates)

Proof:
1. Under the coefficient-order condition, every term of `f i` has degree at least `d_i`.
Its degree-`d_i` part restricts to `A i`, which is nonzero by pure supported division.
Thus its order is exactly `d_i`. Apply `hasUniqueDivision_extraVariables_iff` to every
prefix, adjoining the coefficient variables, and then the continuous formal division
lemma `lem-trf-homogeneous-continuous-formal-division`. This gives unique continuous
formal quotients and remainder, with the supported-sum space closed and equal to the
remainder kernel.
2. The whole-series multiplication identities put every transverse monomial multiple
of each generator in that closed space. Coefficient-variable monomials preserve quotient
supports, since the vertices have zero coefficient components. Truncate an arbitrary
series multiplier and pass to the adic limit. The generated ideal is therefore exactly
the supported-sum space and the remainder kernel. Formal division now gives the Hilbert
function equality and supported generation of the whole ideal.
3. If the coefficient-order condition fails, minimize the order `k` of a generator
whose order is below its vertex degree. Every vertex in the degree prefix at `k` then
has its prescribed order. Apply extra-variable homogeneous division and continuous
formal division to that prefix and to the ideal generated by all generators. The
prefix and full diagrams agree through degree `k`, so the ideal's Hilbert function is
at most the full diagram's function through that degree, even for an empty prefix.
4. Take a failing generator of order `k`. For a nonempty prefix, its derivative
memberships, evaluated at zero in the prefix essential variables, kill every coefficient
indexed by the restricted prefix diagram through degree `k`. The bound on `Q` applies
because `k < d_i`; factorials are invertible in characteristic zero. Its nonzero initial
form is therefore supported outside the prefix diagram. It adds an independent relation
to the independent prefix columns in the degree-`k` truncation, making the dimension
strictly smaller there. Together with Step 3, this gives strict lexicographic decrease.
5. Under the order condition, uniqueness of formal division implies that multiplying
by a coefficient coordinate commutes with the remainder. Coordinate multiplication is
injective on series, so a series whose coordinate-power multiple lies in the ideal has
zero remainder itself. This proves saturation equality. In general the original ideal
is contained in its saturation, hence every saturated truncated quotient is a quotient
of the original one. Its dimension can only decrease, and strict lexicographic decrease
from the diagram cannot be undone. The increasing power-colon construction has exactly
the stated existential membership criterion, including exponent zero.
6. An ordinary boundary substitution preserves the supported multiplication identities
because it fixes transverse variables and quotient supports restrict only those variables.
It commutes with transverse derivatives and preserves the essential-variable ideals;
local Taylor maps preserve Jacobian units. At each Taylor model retaining the pure forms
and whole-series certificates, Steps 1--5 apply to the substituted family itself. There
is no exceptional-power division and no assertion about other model points.
7. Under a field embedding, finite homogeneous basis matrices and their inverses map to
inverse matrices. Whole-series identities and derivative memberships map coefficientwise;
nonzero coefficients and Jacobian units stay nonzero or invertible. Coefficient orders
are unchanged. Apply Steps 1--6 over the extension field. With no vertices, the ideal and
diagram are empty, ordinary monomials form every truncated basis, and the coefficient
condition is vacuous. With no coefficient variables the saturation assertions are vacuous.
-/
theorem hilbert_boundary_supported_certificates
    {L : Type u} [Field L] [CharZero L] {m r s : ℕ}
    (α : Fin s → Fin r →₀ ℕ) (A : Fin s → MvPolynomial (Fin r) L)
    (f : Fin s → MvPowerSeries (Fin m ⊕ Fin r) L) (Q : ℕ)
    (cert : SupportedBoundaryCertificates α A f Q) :
    SupportedBoundaryConclusions α f := by
  sorry

/-- The same conclusions after an arbitrary coefficient-field embedding, with the same
coefficient-order test. The two coefficient universes are independent.

Source: BM 1997, section 7; BMT sections 6.1--6.2; ILO VIII 2.3.11--2.3.13.
(blueprint: lem-per-hilbert-boundary-supported-certificates)

Proof: Map every finite-degree supported basis and its inverse coefficientwise along
`φ`, using `hasUniqueDivision_extraVariables_map`. Map the whole-series multiplication
identities, the derivative identities and Jacobian units. A field homomorphism is
injective, so the first nonzero coefficient of every coefficient series stays nonzero;
its order is unchanged. Apply `hilbert_boundary_supported_certificates` to the mapped
certificates. This includes empty families, as in Step 7 of the main proof. -/
theorem hilbert_boundary_supported_certificates_map
    {L : Type u} [Field L] [CharZero L] {E : Type v} [Field E] [CharZero E]
    (φ : L →+* E) {m r s : ℕ}
    (α : Fin s → Fin r →₀ ℕ) (A : Fin s → MvPolynomial (Fin r) L)
    (f : Fin s → MvPowerSeries (Fin m ⊕ Fin r) L) (Q : ℕ)
    (cert : SupportedBoundaryCertificates α A f Q) :
    SupportedBoundaryConclusions α (fun i ↦ MvPowerSeries.map φ (f i)) ∧
      (BoundaryOrderCondition α (fun i ↦ MvPowerSeries.map φ (f i)) ↔
        BoundaryOrderCondition α f) := by
  sorry

/-- Conditional application to the actual ordinary pullback in a boundary Taylor chart.
The retained-certificate hypothesis is on the substituted whole series over the model's
coefficient field. It does not follow from an equality-locus-only standard basis.

Source: BM 1997, Theorem 7.21(2), p.269; BMT section 5.2;
ILO VIII 2.3.11--2.3.13.
(blueprint: lem-per-hilbert-boundary-supported-certificates)

Proof: In the chart `W_u = e`, `W_v = e (ξ + V)`, ordinary continuous substitution
fixes `Z` and substitutes the coefficient series. It sends each displayed multiplication
identity to the corresponding identity with supported quotients, commutes with transverse
derivatives, and preserves the essential-variable ideals. A local Taylor map preserves
the Jacobian units. At a point where the mapped pure forms and all certificates are
retained, apply the main theorem to those actual substituted series. This is precisely
Step 6, also allowing the coefficient-field extension of Step 7. -/
theorem hilbert_boundary_supported_certificates_chart
    {L : Type u} [Field L] [CharZero L] {E : Type v} [Field E] [CharZero E]
    (φ : L →+* E) {m r s : ℕ}
    (α : Fin s → Fin r →₀ ℕ) (A : Fin s → MvPolynomial (Fin r) L)
    (f : Fin s → MvPowerSeries (Fin m ⊕ Fin r) L) (Q : ℕ)
    (cert : SupportedBoundaryCertificates α A f Q)
    (u v : Fin m) (huv : u ≠ v) (ξ : E)
    (retained : SupportedBoundaryCertificates α (fun i ↦ MvPolynomial.map φ (A i))
      (fun i ↦ MvPowerSeries.subst (boundaryChartVariables u v ξ) (MvPowerSeries.map φ (f i)))
      Q) :
    SupportedBoundaryConclusions α
      (fun i ↦ MvPowerSeries.subst (boundaryChartVariables u v ξ)
        (MvPowerSeries.map φ (f i))) := by
  sorry

end AlgebraicGeometry.HilbertCoefficient
