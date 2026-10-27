## Worker report

Stage 2 statement for `lem-trf-facet-lattice-supported-coordinate-cover` in
`lean/Sheaf/RingTheory/FacetLatticeSupportedCoordinateCover.lean`. Its only theorem is
`ToricMonoid.exists_facetLattice_supportedCoordinateCover`, with proof `by sorry`.
Three real definitions express its exponent notation and its prequotient assertions:
`facetCoordinateExponent`, `facetParameterExponent`, and
`IsFacetSupportedCoordinateRetraction`. They do not choose embeddings or retractions,
and contain no postponed proofs. All variables and universes are explicit, with
`set_option autoImplicit false`.

The earlier BLOCKED ending concerned an unchanged stage-1 item, already split and
reviewed by Q145. The current node has no `lean` attachment and is listed at stage 2
in `coord/queue.tsv`. The stage-handoff paragraph of `coord/brief-stage2.md` explicitly
allows this statement delivery. No reopening or alteration of the accepted split is
needed. No released repair note for this item was found.

Clause-by-clause correspondence:

| Node hypothesis or assertion | Lean rendering |
| --- | --- |
| Additive commutative monoid P | `(P : Type u) [AddCommMonoid P]` |
| Finitely generated, integral, saturated | `hfs : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative P)`; the existing definition says finite monoid generation, injectivity into the canonical group completion, and saturation there |
| Only invertible element is zero | `hsharp : ∀ a b : P, a + b = 0 → a = 0 ∧ b = 0` |
| Any n ≥ 0 | `(n : ℕ)` without a positivity assumption |
| G = group completion | `Algebra.GrothendieckAddGroup P`, with `Algebra.GrothendieckAddGroup.of` as chart inclusion, as used by the recorded facet-form definition |
| Facets and their primitive nonnegative forms | `Algebra.MonoidFacetForm P`; the recorded definition identifies these with facets for fs monoids, so no independent choice of normals is introduced |
| Finite facet set | `Finite (Algebra.MonoidFacetForm P)` |
| Enumeration by r facets | `∀ (r : ℕ) (facets : Fin r ≃ Algebra.MonoidFacetForm P)`; this equivalence imposes exactly the facet cardinality and permits any enumeration |
| ν is injective | `Function.Injective (Algebra.monoidFacetVector facets)` |
| M = ν(G), ν(P) = M ∩ N^r | The equivalence for every `v : Fin r → ℤ` between `∃ q : P, ... = v` and membership in `monoidFacetVector facets |>.range` together with all coordinates nonnegative |
| Positive vector only for P ≠ {0} | `¬ Subsingleton P → ∃ c : P, ∀ i : Fin r, 0 < ...` |
| Field coefficients and R = B_k(P,n) | `∀ (k : Type v) [Field k]`, with `Complete k P n` |
| R normal domain in field case | `IsDomain (Complete k P n) → IsIntegrallyClosed (Complete k P n) → ...` |
| Cohen coefficients with residue characteristic p | `∀ (C : Type v) [CommRing C] [IsLocalRing C] (p : ℕ), IsCohenRing p C → ...`; `IsCohenRing` includes primality, DVR, maximal ideal `(p)`, and completeness |
| Parameter θ and θ − p in the chart ideal | `∀ θ : Complete C P n, θ - (p : Complete C P n) ∈ completedChartIdeal C P n → ...` |
| R = B_C(P,n)/(θ), normal domain | The two predicates `IsDomain` and `IsIntegrallyClosed` on `Complete C P n ⧸ Ideal.span {θ}` |
| B is the specified completed monoid polynomial ring | `ToricMonoid.Complete L P n`, a published abbreviation for `AdicCompletion (localModelCompletionIdeal L P n) (MvPolynomial (Fin n) (AddMonoidAlgebra L P))` |
| A = L[[X_1,...,X_r,t_1,...,t_n]] | `MvPowerSeries (Fin r ⊕ Fin n) L`, with facets in `Sum.inl` and parameters in `Sum.inr` |
| Injective L-algebra map ι | Existential `ι : Complete L P n →ₐ[L] MvPowerSeries ... L`, and the first conjunct of `IsFacetSupportedCoordinateRetraction` |
| Extension of the displayed polynomial homomorphism | The predicate's equation for every `q : P`, parameter exponent `a`, and coefficient `c : L`, sending the completed image of `MvPolynomial.monomial a (AddMonoidAlgebra.single q c)` to the corresponding power-series monomial; linearity and addition cover all polynomials |
| Image exactly series supported on (M ∩ N^r) × N^n | The predicate's image equivalence: existence of a preimage iff every coefficient whose facet exponent is outside the range lattice vanishes; parameter exponents are unrestricted |
| Delete every other coefficient | The predicate specifies each coefficient of `ι (ρ f)` by `if` membership of its facet exponent in the range lattice, retaining the coefficient or setting it to zero |
| ρ additive and B-linear | `ρ : ... →+ Complete L P n` and `ρ (ι b * f) = b * ρ f`; these are exactly additive linearity for the B-action through ι |
| ρι = id_B | The predicate's final `∀ b, ρ (ι b) = b` |
| Field case D = A, ρbar = ρ | No separate maps are chosen: the field branch directly uses `ι` and `ρ`, their injectivity, linearity and retraction already supplied by the predicate |
| Cohen case Θ = ιθ and D = A/(Θ) | Every target quotient is `MvPowerSeries ... C ⧸ Ideal.span {ι θ}` |
| B ∩ ΘA = θB | `(Ideal.span {ι θ}).comap ι.toRingHom = Ideal.span {θ}` |
| Induced map R → D | `j : (Complete ... ⧸ Ideal.span {θ}) →+* (...)` with its equation on every quotient representative `b`; this characterizes precisely the induced map |
| Injective R → D | `Function.Injective j` |
| Well-defined descended coefficient retraction | `ρbar : D →+ R` together with its equation on every representative `a`, `ρbar (mk a) = mk (ρ a)` |
| R-linearity and identity on R | `ρbar (j b * d) = b * ρbar d` and `∀ b, ρbar (j b) = b` |
| Kill X^v outside M | Both branches quantify every `v : Fin r →₀ ℕ` outside the lattice and set its projected monomial to zero; the Cohen branch applies the quotient map first |
| Send X^{ν(q)} to z^q | Both branches quantify every `q : P`; the right side is `monomial ... q`, or its quotient image in the Cohen case |

`facetCoordinateExponent` takes the natural-number coordinates of the given forms,
using `Int.toNat`; their nonnegativity is part of `MonoidFacetForm`. Finitely supported
functions on `Fin r` and ordinary functions on `Fin r` describe the same exponent
vectors, through `Finsupp.equivFunOnFinite`. `facetParameterExponent` concatenates the
two exponent vectors. These are notation helpers for this node, not independent notions.
The predicate groups the node's own six prequotient clauses, without any new assumption.

Dependency declarations and source inspection:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup` publicly supplies
  `AlgebraicGeometry.IsFineSaturatedMonoid`, defined in its public import
  `Sheaf.AlgebraicGeometry.LogRegularPair`; read the full definition at lines 138–146.
- `Sheaf.RingTheory.SharpMonoidFacetForms`: read the complete docstrings and signatures
  of `Algebra.MonoidFacetForm` and `Algebra.monoidFacetVector`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, the compatible sequences
  of quotients; `IsAdicComplete`, with its completion-map bijectivity interpretation.
- `WeilConjectures.RingTheory.CohenRing`: read `IsCohenRing`, including all four clauses.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `coeff`, `monomial`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, with
  `IsDomain` giving exactly normal domains as prescribed by the dependency record.
- `Sheaf.RingTheory.CompleteToricModel`: `PolynomialRing`, `Complete`,
  `completedChartIdeal`, and `monomial`. Read these and their underlying ideal and
  completion definitions in `Sheaf.RingTheory.LogRegularSaturationNormality`.
  Added the already landed `def-trf-complete-toric-model` to the item's `stmt_deps`
  under brief-stage2 §5, rather than copying its constructions. No definition changes.
- Proof-only import `Sheaf.RingTheory.CompletedMonoidSupportProjection` supplies
  `AddMonoidAlgebra.exists_completedMonoid_supportProjection`; read its full statement
  and coefficientwise proof docstring. The proof dependency
  `lem-trf-sharp-cone-primitive-facet-preparation` has no Lean record yet, so it has no
  import to add; the six-step proof docstring names it for later proof work.

Source: opened the local ILO PDF with `pdftotext -f 75 -l 76 -layout`, reading printed
pp. 69–70, especially Exposé VI 1.4 and 1.6(i)–(ii). It supplies the sharp fs monoid,
field model and Cohen model with θ congruent to p. The auxiliary coordinate-cover
argument is explicitly agent-formulated in the node, not claimed as an ILO theorem.
Its six accepted proof steps are all transcribed in the theorem docstring.

Edge cases checked before completing the record:

- For the one-element monoid P, the group completion is zero and admits no surjective
  map to ℤ. Thus the facet type is empty, `r=0`, positivity is not requested, and the
  lattice and image equivalences have the unique zero vector. The supported projection
  is the identity on the parameter power-series ring.
- `r=0` excludes no legal instance: `Fin 0` exponents and the empty equivalence are
  permitted; with fs sharp P, the lattice injection then forces P to be trivial.
- `n=0` has no parameter coordinates. With both `r=n=0`, power series have just the
  constant coefficient and the rings reduce to L (or the prescribed Cohen quotient).
- For P = N, the unique primitive form gives the identity coordinate cover. For a
  nonsmooth saturated monoid with nontrivial lattice index, coefficients outside M
  are still deleted; the formula does not incorrectly replace M by the whole lattice.
- Cohen quotient expressions use the same chosen ι and θ throughout. The additive
  retraction is not assumed multiplicative. Its scalar-multiplication equation is
  exactly what descends it through the principal ideals.
- Normality and the θ congruence are retained even though the abstract retraction
  argument proves more. No `Nonempty P`, positive rank, positive n, algebraic closure,
  or extra module action has been imposed. Monoid universe u and coefficient universe
  v are independent.

Searches (prescribed msearch wrapper, rerun 2026-10-23; exact records in searches.jsonl):

- LeanFinder: "Facet lattice embedding of a sharp saturated monoid and supported power
  series completion with a linear retraction descending modulo a Cohen parameter".
  Eight hits, concerning Weierstrass division, perfectoid untilt coefficient maps and
  Laurent-series completions; none states this theorem.
- Loogle: "Algebra.MonoidFacetForm, Algebra.monoidFacetVector,
  AddMonoidAlgebra.CompletedLocalModel". Zero hits, unknown identifier for the first
  project-specific name; no existing Mathlib match.
- Mathlib grep: "facet.*[Ll]attice|supportProjection|supported.*[Mm]onoid", subdirectory
  RingTheory. Zero hits.
- LeanSearch: "Sharp saturated monoid primitive facet embedding supported power series
  coefficient retraction completion". Eight hits: ordinary polynomial-to-power-series
  maps, their density, Laurent-series equivalences and monomial constructors, none
  containing the facet embedding, lattice support and Cohen quotient retraction.
- `rg -n` in both live `lean/WeilConjectures` and `lean/Sheaf` for
  `facet.*[Ll]attice|supportProjection|supported.*[Mm]onoid|[Ff]acet.*[Cc]oordinate`.
  Only the lower-level completed-monoid support projection is relevant; it assumes
  the lattice presentation and contains no facet preparation or Cohen-quotient result.
  Other hits are unrelated étale-support functors. Searching the item id in
  `lean/WeilConjectures` gave no match. Exact new declaration names were also searched
  in both project roots, with no existing declarations found.

No new nodes, dependency repairs or statement correction were needed. No disputed
statement or mathematical fault was found. The item's statement and accepted proof
are unchanged. Initial server validation through the required `scompile.py` compiled
both the sandbox and actual module in 2.4 seconds each, with no errors or warnings.

## Second reading by Q53

A separate sequential pass reopened the node and the entire module, checking the
hypothesis/clause table above against the actual signature and predicate body. This
is the same dispatched worker's consistency reread; no second agent was started.
The maintainer's independent review remains the independent reading specified in
this dispatch brief. The reread checked that the Cohen maps use the same ι, that
prequotient exact support and coefficient deletion are both included, that the field
branch itself supplies the induced retraction, and that positivity alone is guarded
by nontriviality of P. It also identified the published complete-model definitions
as the right interface, so the only dependency-list addition is their owning node.
The signature and helper definitions required no further changes after compilation.
