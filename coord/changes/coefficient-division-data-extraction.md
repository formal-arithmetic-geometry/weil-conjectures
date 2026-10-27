# AlgebraicGeometry.HilbertCoefficient.coefficientDivisionMatrix

## Reason

Move the seven existing concrete definitions and the finite-instance declaration into
`Sheaf.AlgebraicGeometry.CoefficientDivisionData`, publicly reexported by the item.
The bodies, names, types and attributes are unchanged; only their source module and
blueprint docstring tags change. This allows three independent algebraic subarguments
and the proved order-locus bound to import the concrete objects without importing the
upper theorem and creating an import cycle. There is no new choice of data from a theorem.

The original public imports of RegularHilbertCoefficientDatum and SupportedHomogeneousDivision
are reexported through the data module. FiniteType and Trunc remain public imports of the item.
The unused public LinearAlgebra.Determinant import is removed. No target meaning changes.

## Old

In `Sheaf.AlgebraicGeometry.CoefficientLocusUniformDivision`:

```lean
/-- Essential variables form an actual subtype of the original finite variable set.
Source: BM 1997, Theorem 8.1 and its application on p.282
(blueprint: lem-trf-coefficient-locus-uniform-division). -/
instance coefficientEssentialFinite {σ ι : Type} [Finite σ] (α : ι → σ →₀ ℕ) :
    Finite (EssentialVariables α) :=
  inferInstanceAs (Finite {j : σ // ∃ i : ι, α i j ≠ 0})

/-- The series with coefficient `[W^δ Z^γ] fᵢ = [W^δ] T(cᵢγ)`.
Source: BM 1997, Theorem 9.6, p.282
(blueprint: lem-trf-coefficient-locus-uniform-division). -/
def coefficientFamilySeries {m n s : ℕ} {A L : Type u} [CommRing A] [Field L]
    (T : A →+* MvPowerSeries (Fin m) L) (c : Fin s → (Fin n →₀ ℕ) → A)
    (i : Fin s) : MvPowerSeries (Fin m ⊕ Fin n) L :=
  fun e ↦ MvPowerSeries.coeff (Finsupp.comapDomain.addMonoidHom Sum.inl_injective e)
    (T (c i (Finsupp.comapDomain.addMonoidHom Sum.inr_injective e)))

open Classical in
/-- The finite set of monomials of exactly the given degree, including degree zero.
Source: BM 1997, Theorem 8.1, p.274
(blueprint: lem-trf-coefficient-locus-uniform-division). -/
def coefficientDegreeExponents (σ : Type) [Finite σ] (t : ℕ) : Finset (σ →₀ ℕ) :=
  (Finsupp.finite_of_degree_le (σ := σ) t).toFinset.filter (fun e ↦ e.degree = t)

/-- The monomial assigned to a generator column or a remainder column.
Source: BM 1997, Theorem 8.1, pp.274--275
(blueprint: lem-trf-coefficient-locus-uniform-division). -/
def coefficientColumnExponent {σ ι : Type} [LinearOrder ι]
    {D : Set (σ →₀ ℕ)} {α : ι → σ →₀ ℕ} {t : ℕ} :
    DivisionIndex D α t → σ →₀ ℕ
  | .inl p => α p.val.1 + p.val.2
  | .inr e => e.val

open Classical in
/-- Square coefficient matrix of supported division, reindexed by assigned monomials.
The selected index is unique for an ordered vertex family; the zero fallback makes
this a total construction even for other inputs, without any postponed proof.
Source: BM 1997, Theorem 8.1, pp.274--275
(blueprint: lem-trf-coefficient-locus-uniform-division). -/
def coefficientDivisionMatrix {σ ι : Type} [Finite σ] [LinearOrder ι]
    {A : Type u} [CommRing A] (α : ι → σ →₀ ℕ)
    (H : ι → MvPolynomial σ A) (t : ℕ) :
    Matrix ↥(coefficientDegreeExponents σ t) ↥(coefficientDegreeExponents σ t) A :=
  fun row col ↦ if h : ∃ p : DivisionIndex (generated α) α t,
      coefficientColumnExponent p = col.val then
    MvPolynomial.coeff row.val (divisionFamily (generated α) α H t (Classical.choose h))
  else 0

open Classical in
/-- Initial forms restricted to the essential Z variables of a degree prefix.
All W variables and all other Z variables have been set to zero. Coefficients
are the original regular functions, namely their derivatives of order zero / 0!.
Source: BM 1997, Lemma 7.7 and completion of Theorem 9.6, p.282
(blueprint: lem-trf-coefficient-locus-uniform-division). -/
def restrictedCoefficientForms {n s : ℕ} {A : Type u} [CommRing A]
    (α : Fin s → Fin n →₀ ℕ) (c : Fin s → (Fin n →₀ ℕ) → A) (q : ℕ) :
    {i : Fin s // (α i).degree ≤ q} →
      MvPolynomial (EssentialVariables (prefixVertices α q)) A :=
  fun i ↦ ∑ e ∈ coefficientDegreeExponents
      (EssentialVariables (prefixVertices α q)) (α i.val).degree,
    MvPolynomial.monomial e (c i.val (Finsupp.mapDomain Subtype.val e))

open Classical in
/-- Exactly the order witnesses and the restricted determinants in bounded degrees.
Only prefixes through the largest vertex degree occur; all later prefixes coincide.
Source: BM 1997, completion of Theorem 9.6, p.282
(blueprint: lem-trf-coefficient-locus-uniform-division). -/
def coefficientDivisionTests {n s : ℕ} {A : Type u} [CommRing A]
    (α : Fin s → Fin n →₀ ℕ) (c : Fin s → (Fin n →₀ ℕ) → A)
    (B : ℕ → ℕ) : Finset A :=
  Finset.univ.image (fun i ↦ c i (α i)) ∪
    (Finset.range (Finset.univ.sup (fun i : Fin s ↦ (α i).degree) + 1)).biUnion
      (fun q ↦ (Finset.range (B q + 1)).image fun t ↦ Matrix.det
        (coefficientDivisionMatrix (essentialVertices (prefixVertices α q))
          (restrictedCoefficientForms α c q) t))

/-- The coefficient order locus, expressed by actual germs in maximal-ideal powers.
Source: BM 1997, completion of Theorem 9.6, p.282
(blueprint: lem-trf-coefficient-locus-uniform-division). -/
def coefficientFamilyOrderLocus {N : Scheme.{u}} {n s : ℕ}
    (α : Fin s → Fin n →₀ ℕ) (c : Fin s → (Fin n →₀ ℕ) → Γ(N, ⊤)) : Set N :=
  {b | ∀ (i : Fin s) (γ : Fin n →₀ ℕ), γ.degree < (α i).degree →
    N.presheaf.germ ⊤ b (by trivial) (c i γ) ∈
      IsLocalRing.maximalIdeal (N.presheaf.stalk b) ^ ((α i).degree - γ.degree)}
```

## New

In `Sheaf.AlgebraicGeometry.CoefficientDivisionData`, publicly imported by the item:

```lean
/-- Essential variables form an actual subtype of the original finite variable set.
Source: BM 1997, Theorem 8.1 and its application on p.282
(blueprint: def-trf-coefficient-division-data). -/
instance coefficientEssentialFinite {σ ι : Type} [Finite σ] (α : ι → σ →₀ ℕ) :
    Finite (EssentialVariables α) :=
  inferInstanceAs (Finite {j : σ // ∃ i : ι, α i j ≠ 0})

/-- The series with coefficient `[W^δ Z^γ] fᵢ = [W^δ] T(cᵢγ)`.
Source: BM 1997, Theorem 9.6, p.282
(blueprint: def-trf-coefficient-division-data). -/
def coefficientFamilySeries {m n s : ℕ} {A L : Type u} [CommRing A] [Field L]
    (T : A →+* MvPowerSeries (Fin m) L) (c : Fin s → (Fin n →₀ ℕ) → A)
    (i : Fin s) : MvPowerSeries (Fin m ⊕ Fin n) L :=
  fun e ↦ MvPowerSeries.coeff (Finsupp.comapDomain.addMonoidHom Sum.inl_injective e)
    (T (c i (Finsupp.comapDomain.addMonoidHom Sum.inr_injective e)))

open Classical in
/-- The finite set of monomials of exactly the given degree, including degree zero.
Source: BM 1997, Theorem 8.1, p.274
(blueprint: def-trf-coefficient-division-data). -/
def coefficientDegreeExponents (σ : Type) [Finite σ] (t : ℕ) : Finset (σ →₀ ℕ) :=
  (Finsupp.finite_of_degree_le (σ := σ) t).toFinset.filter (fun e ↦ e.degree = t)

/-- The monomial assigned to a generator column or a remainder column.
Source: BM 1997, Theorem 8.1, pp.274--275
(blueprint: def-trf-coefficient-division-data). -/
def coefficientColumnExponent {σ ι : Type} [LinearOrder ι]
    {D : Set (σ →₀ ℕ)} {α : ι → σ →₀ ℕ} {t : ℕ} :
    DivisionIndex D α t → σ →₀ ℕ
  | .inl p => α p.val.1 + p.val.2
  | .inr e => e.val

open Classical in
/-- Square coefficient matrix of supported division, reindexed by assigned monomials.
The selected index is unique for an ordered vertex family; the zero fallback makes
this a total construction even for other inputs, without any postponed proof.
Source: BM 1997, Theorem 8.1, pp.274--275
(blueprint: def-trf-coefficient-division-data). -/
def coefficientDivisionMatrix {σ ι : Type} [Finite σ] [LinearOrder ι]
    {A : Type u} [CommRing A] (α : ι → σ →₀ ℕ)
    (H : ι → MvPolynomial σ A) (t : ℕ) :
    Matrix ↥(coefficientDegreeExponents σ t) ↥(coefficientDegreeExponents σ t) A :=
  fun row col ↦ if h : ∃ p : DivisionIndex (generated α) α t,
      coefficientColumnExponent p = col.val then
    MvPolynomial.coeff row.val (divisionFamily (generated α) α H t (Classical.choose h))
  else 0

open Classical in
/-- Initial forms restricted to the essential Z variables of a degree prefix.
All W variables and all other Z variables have been set to zero. Coefficients
are the original regular functions, namely their derivatives of order zero / 0!.
Source: BM 1997, Lemma 7.7 and completion of Theorem 9.6, p.282
(blueprint: def-trf-coefficient-division-data). -/
def restrictedCoefficientForms {n s : ℕ} {A : Type u} [CommRing A]
    (α : Fin s → Fin n →₀ ℕ) (c : Fin s → (Fin n →₀ ℕ) → A) (q : ℕ) :
    {i : Fin s // (α i).degree ≤ q} →
      MvPolynomial (EssentialVariables (prefixVertices α q)) A :=
  fun i ↦ ∑ e ∈ coefficientDegreeExponents
      (EssentialVariables (prefixVertices α q)) (α i.val).degree,
    MvPolynomial.monomial e (c i.val (Finsupp.mapDomain Subtype.val e))

open Classical in
/-- Exactly the order witnesses and the restricted determinants in bounded degrees.
Only prefixes through the largest vertex degree occur; all later prefixes coincide.
Source: BM 1997, completion of Theorem 9.6, p.282
(blueprint: def-trf-coefficient-division-data). -/
def coefficientDivisionTests {n s : ℕ} {A : Type u} [CommRing A]
    (α : Fin s → Fin n →₀ ℕ) (c : Fin s → (Fin n →₀ ℕ) → A)
    (B : ℕ → ℕ) : Finset A :=
  Finset.univ.image (fun i ↦ c i (α i)) ∪
    (Finset.range (Finset.univ.sup (fun i : Fin s ↦ (α i).degree) + 1)).biUnion
      (fun q ↦ (Finset.range (B q + 1)).image fun t ↦ Matrix.det
        (coefficientDivisionMatrix (essentialVertices (prefixVertices α q))
          (restrictedCoefficientForms α c q) t))

/-- The coefficient order locus, expressed by actual germs in maximal-ideal powers.
Source: BM 1997, completion of Theorem 9.6, p.282
(blueprint: def-trf-coefficient-division-data). -/
def coefficientFamilyOrderLocus {N : Scheme.{u}} {n s : ℕ}
    (α : Fin s → Fin n →₀ ℕ) (c : Fin s → (Fin n →₀ ℕ) → Γ(N, ⊤)) : Set N :=
  {b | ∀ (i : Fin s) (γ : Fin n →₀ ℕ), γ.degree < (α i).degree →
    N.presheaf.germ ⊤ b (by trivial) (c i γ) ∈
      IsLocalRing.maximalIdeal (N.presheaf.stalk b) ^ ((α i).degree - γ.degree)}
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.CoefficientLocusUniformDivision --uses
coefficientFamilySeries coefficientDegreeExponents coefficientColumnExponent
coefficientDivisionMatrix restrictedCoefficientForms coefficientDivisionTests
coefficientFamilyOrderLocus coefficientEssentialFinite` reports zero downstream Lean
modules and only the item itself as a textual user of these declarations (2026-10-26).
There are therefore no existing direct Lean importers to adapt or compile.
The two DAG parents retain their dependencies; this is not a withdrawal.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CoefficientLocusUniformDivision | U8 | Same public theorem signature and unchanged definitions reexported from the data module. |
| Sheaf.AlgebraicGeometry.CoefficientFirstExponentDeterminants | new in this delivery | Imports extracted data; determinant subargument. |
| Sheaf.AlgebraicGeometry.CoefficientRestrictedFiniteTests | new in this delivery | Imports extracted data; finite matrix subargument. |
| Sheaf.AlgebraicGeometry.CoefficientOrderLocusBound | new in this delivery | Imports extracted data; fully proved lower order bound. |
| Sheaf.AlgebraicGeometry.CoefficientRestrictedToFull | new in this delivery | Imports extracted data; variable transport subargument. |
| Sheaf.AlgebraicGeometry.RegularHilbertCoefficientData | unclaimed | DAG parent only; no current Lean import or textual use. Unchanged statement and dependency. |
| Sheaf.AlgebraicGeometry.NonreducedRegularHilbertCoefficients | unclaimed | DAG parent only; no current Lean import or textual use. Unchanged statement and dependency. |

## Status

landed 20261026T092819-L-3469853 2026-10-26 (merge of deliver/U8/Sheaf.AlgebraicGeometry.CoefficientLocusUniformDivision)
