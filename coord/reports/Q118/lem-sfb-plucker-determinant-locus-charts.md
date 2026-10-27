## Worker report

The module `Sheaf.AlgebraicGeometry.PluckerDeterminantLocusCharts` states
`lem-sfb-plucker-determinant-locus-charts` without changing the node's statement,
statement dependencies, proof, or proof dependencies. Its namespace is
`AlgebraicGeometry.PluckerDeterminantLocus`. Every theorem has proof `sorry`;
every definition has actual data. All setup helpers belong to the explicit
construction in this node, rather than introducing independent mathematical notions.
There are no new nodes or dependency repairs.

The positive rank in the node is represented by `r + 1`, with `N r : ℕ` and
`h : r + 1 < N` on both principal theorems. This parametrizes exactly all the
integers satisfying `0 < rank < N`; it includes rank one (`r = 0`). Columns
are numbered by `Fin N` instead of the order-isomorphic set `{1,...,N}`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Increasing rank-sized subsets: `Index N r` is the subtype of finsets of
  `Fin N` whose cardinality is `r + 1`. `columns I` is Mathlib's increasing
  enumeration `Finset.orderEmbOfFin I.val I.property`.
- The ring B: `PolynomialRing N r` is exactly `MvPolynomial (Index N r) ℤ`.
  Its grading is Mathlib's `homogeneousSubmodule`; `polynomialGradedRing`
  installs the existing `MvPolynomial.gradedAlgebra` for this index type.
- Ordered coordinates: `orderedCoordinate t` sums `C(det δ(I,t)) * X I`
  over increasing subsets I, where δ has entry one precisely when
  `columns I a = t b`. A nonzero Leibniz summand forces t to be a bijection
  onto I. Its coefficient is the sign of that permutation. Therefore exactly
  the sorting sign multiplies the sorted coordinate for distinct indices,
  and repeated indices give zero. This finite formula requires no chosen
  sorting witnesses or unproved data.
- `C_{I,K}(a,b)`: `replacementMatrix I K a b` is `orderedCoordinate` of
  `Function.update (columns I) a (columns K b)`.
- `F_{I,K}`: `relation I K` is `X I ^ r * X K - det (replacementMatrix I K)`.
  The exponent is precisely rank minus one, with natural subtraction avoided.
- H: `relationsIdeal N r` is `Ideal.span` of the range of all pairs `(I,K)`.
  It is the specified ideal, without radicalization or saturation.
- A: `CoordinateRing N r` is the actual ideal quotient `PolynomialRing N r ⧸ H`.
  `quotientGrade N r d` is the image of the degree-d polynomial submodule
  under `Ideal.Quotient.mkₐ ℤ H`. The theorem `quotientGrade_exists` states
  that these exact submodules form a graded ring. `quotientGradedRing` chooses
  the structure on those fixed components. This is permitted unique-structure
  choice: a direct-sum decomposition on a fixed family is determined uniquely,
  so no unspecified ring or unspecified degree components are chosen.
  `quotientMap` has the actual quotient ring homomorphism as its data and
  proves its degree-preserving condition directly by membership in that image.
- Every relation has degree rank: the first conjunct of
  `relations_homogeneous_and_evaluate_zero` is
  `∀ I K, (relation I K).IsHomogeneous (r + 1)`.
- Evaluation vanishes over every commutative ring: the same theorem binds
  `(R : Type u) [CommRing R]` and
  `(M : Matrix (Fin (r + 1)) (Fin N) R)` for arbitrary `u`. Its second conjunct
  evaluates at `det (M.submatrix id (columns J))` using `eval₂Hom` and the
  unique integer ring homomorphism, and sets every relation to zero.
  There is no field, domain, reducedness, or regularity assumption.
- X is literally `Proj (quotientGrade N r)` throughout.
- The graded quotient's canonical j is the definition `immersion N r`,
  exactly `Proj.map (quotientMap N r) (irrelevant_le_map N r)`.
  `irrelevant_le_map` states the requisite irrelevant-ideal containment;
  it is a theorem about this fixed map, not an arbitrary-map assumption.
- Closed embedding and projective ambient scheme: the first conjunct of
  `closedImmersion_and_charts` is `IsClosedImmersion (immersion N r)`.
  Its third conjunct identifies the polynomial Proj with the recorded
  `ProjectiveSpace (Index N r) (Spec (.of ℤ))`. The index consists of all
  rank-sized subsets, so this has exactly binomial(N,rank) homogeneous
  coordinates, or classical projective dimension binomial(N,rank)-1.
- U_I: the opens in the theorem are exactly
  `Proj.basicOpen (quotientGrade N r) (Ideal.Quotient.mk H (X I))`.
  The second conjunct states that their supremum is top.
- The denominator of `fraction I t` is the image of `X I`; its numerator is
  the image of `orderedCoordinate t`. It uses `HomogeneousLocalization.Away.mk`
  with exponent one and degree one, justified by the named degree theorems
  `coordinate_mem` and `orderedCoordinate_mem`.
- M^(I): `normalizedMatrix I a j` is the single-column-replacement fraction.
  The theorem explicitly states, for all rows a and pivot indices b,
  `normalizedMatrix I a (columns I b) = if a = b then 1 else 0`.
  This is the specified identity pivot matrix, with the specified ratios in
  every off-pivot column, rather than an unrelated matrix with the same size.
- Off-pivot polynomial ring: `ChartIndex I` is
  `Fin (r + 1) × {j : Fin N // j ∉ I.val}`. The forward `chartMap I` is the
  polynomial evaluation ring homomorphism at exactly the corresponding
  `normalizedMatrix` entries. The existential ring equivalence e is required
  to satisfy `e.toRingHom = chartMap I`; a bare unrelated isomorphism is not used.
- Inverse formula: `universalMatrix I` has identity pivot columns and variable
  `X (a,j)` in every off-pivot entry. For each J, the theorem specifies
  `e.symm (fraction I (columns J)) = det ((universalMatrix I)_J)`.
  The equivalence's inverse laws make this the inverse of the specified map.
- Normalized minors: for every J the same theorem gives
  `det ((normalizedMatrix I)_J) = fraction I (columns J)`.
  For increasing J, the definition of orderedCoordinate is exactly `X J`.
- Affine charts and dimension: the final assertion is an isomorphism between
  the actual open subscheme U_I and `Spec (MvPolynomial (ChartIndex I) ℤ)`.
  The theorem also explicitly states
  `Fintype.card (ChartIndex I) = (r + 1) * (N - (r + 1))`.
  Thus this is the claimed affine rank*(N-rank)-space. The coordinate ring
  equivalence is fixed by `chartMap`, and the canonical standard-open-to-Spec
  identification is the one supplied by `Proj.basicOpenIsoSpec`.

Dependency declarations read and used:

- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial`, `MvPolynomial.X`,
  `MvPolynomial.aeval`, and `MvPolynomial.algHom_ext`, from
  `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`. We use the equivalent
  ring-hom form `MvPolynomial.eval₂Hom` at the unique integer structure map.
- `def-weil-pbc-matrix-determinant`: `Matrix.det`, `.det_apply`, and submatrices,
  from `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`.
- `def-weil-pbc-algebra-hom-quotient`: `Ideal.Quotient.mk`, `.mkₐ`, the
  quotient's algebra instance, and `Ideal.span`, from
  `Mathlib.RingTheory.Ideal.Quotient.Operations` and its imports.
- `def-pc-proj`: `AlgebraicGeometry.Proj`, from
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`, and the standard
  opens and their Spec isomorphisms from `.Basic`. The recorded upstream
  `Proj.isAffineOpen_basicOpen_and_nonempty_iso` was also read; it packages
  those same standard-open constructions, which are already available here.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `.Hom`, from
  `Mathlib.AlgebraicGeometry.Scheme` (publicly imported through Proj).
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`, from
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `def-nagata-projective-space-base-change`: `AlgebraicGeometry.ProjectiveSpace`
  and `Proj.projectiveSpaceOverAffine`, from
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`. The existing definition
  is used directly for the ambient projective-space identification.
- `def-nagata-homogeneous-localization-degree-zero`:
  `HomogeneousLocalization.Away` and `.Away.mk`, from
  `Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`.
- Proof dependencies imported: the exact Cramer/adjugate identities
  `Matrix.det_mul`, `.det_adjugate`, `.cramer_eq_adjugate_mulVec` from
  `Mathlib.LinearAlgebra.Matrix.Adjugate` and its imports; relative-Proj
  functoriality from `WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality`
  (including its recorded `isClosedImmersion_relProjMap`); the standard-open
  isomorphism and covering `Proj.basicOpenIsoSpec`, `.iSup_basicOpen_eq_top`
  through the public Proj imports. Localization away is supplied by those
  imports as well. The absolute closed-immersion API `Proj.isClosedImmersion_map`
  is publicly imported from
  `WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor`.

Sources opened: the normalized quotient-chart argument at
`constructions.tex`, `lemma-gkn-representable` (089T); the graded-surjection
closed-immersion argument at `lemma-surjective-graded-rings-map-proj` (01N0);
and standard-open homogeneous localization at `lemma-standard-open` (01M4).
The node explicitly attributes its determinant presentation and chart-ring
completion to the agent-written completion, rather than to the literal
statement of 089T. The Lean docstrings preserve this attribution and carry
the proof plan, including all seven original proof steps across the statements.

Edge cases checked before and after writing: rank one (all relations are zero,
and projective space has its ordinary polynomial affine charts); maximal
allowed rank N-1; arbitrary ordering of I and J; replacement by another pivot
column (repeated tuple, so zero); unchanged pivot replacement (ratio p_I/p_I
is one); negative permutation signs over ℤ; rings of characteristic two; the
zero coefficient ring; matrices with all minors zero; nilpotent or zero-divisor
pivot minors. All evaluation cases are included without a nonzero-divisor
hypothesis. Actual chart fractions are homogeneous localizations of the
quotient, so no cancellation in A is assumed. For the fixed components used
by the grading helpers, even an empty Index type causes no undefined tuple or
chosen pivot: the universal chart assertions simply quantify over its elements.

Searches performed for an existing statement or construction:

- `msearch.py`, LeanFinder: "Homogeneous determinant relations between maximal
  minors define a projective scheme whose normalized affine charts are
  polynomial rings" returned generic Proj, ProjectiveSpectrum, and graded
  geometric construction results, with no determinant quotient/chart identity.
- `msearch.py`, Loogle: "HomogeneousIdeal, MvPolynomial,
  HomogeneousLocalization.Away" returned zero hits.
- `msearch.py`, grep: `Plucker|plucker|Grassmann|quotient.*[Gg]rad` returned
  the module-theoretic Grassmannian file, with no scheme/chart construction.
- `msearch.py`, LeanSearch: "Degree zero localization of the homogeneous
  determinant relations for maximal minors is a polynomial ring" returned
  generic homogeneous localization and polynomial localization APIs; no match.
- Local `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for
  `plucker|Plucker|Grassmann|lem-sfb-plucker-determinant-locus-charts` found
  the abstract `FreeQuotientGrassmannProjective` and Hilbert construction
  consumers, not this explicit determinant-quotient interface. The exact item
  identifier has no upstream implementation. DAG search finds this node and
  its consumers, with no separately defined duplicate construction.
- Local Mathlib API searches found the existing homogeneous polynomial
  grading, ideal quotient, homogeneous localization, sorted finset
  enumeration, determinant, and Proj map constructions used here.

Validation: `scompile.py` compiled the module both in sandbox mode and at its
real library module name without errors or warnings. No local/global build was
run and the shared source repository was not modified.

No statement dispute or source-based correction was needed.

## Second reading by Q118

No second reading by a worker: the dispatcher explicitly prohibits starting
other agents. The maintainer's independent review reads this delivery. The
worker's own final rereading checked the sign convention, rank-one exponent,
exact quotient rather than saturated ideal, canonical quotient Proj map,
identity pivot columns, forward generator map, inverse on every minor ratio,
and the numerical affine dimension against the node and the source text.
