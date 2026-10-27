## Worker report

Group Q70, stage 2, 2026-10-23. The module
`Sheaf.AlgebraicGeometry.ExactBlockCoefficientProjection` states
`AlgebraicGeometry.HilbertCoefficient.exactBlockCoefficientProjection`.
Its proof alone is `sorry`; every auxiliary definition has its actual data.
There is no statement correction and no statement dispute. The accepted stage-1
statement and split are preserved. The inherited Q21 stage-1 already-reviewed
rejection does not apply to this stage-2 assignment (brief-stage2 §0).

### Hypotheses and coordinates

All the following names live in `AlgebraicGeometry.HilbertCoefficient`.
The theorem takes the given diagram, generators, regular old operator, its
`ExactBlockInput`, and the finite set E with its exact membership characterization.
The structure packages hypotheses, not conclusions or assumed existence results.

| Node hypothesis | Lean rendering |
| --- | --- |
| Characteristic-zero base field | `{k : Type u} [Field k] [CharZero k]` |
| Smooth affine finite-type coefficient scheme C | `C : Scheme`, `affine`, `smooth`, `finiteType`; the last contains both `LocallyOfFiniteType` and `QuasiCompact` of the k-structure morphism |
| Etale coefficient coordinates w | `coordinates : MvPolynomial (Fin m) k →+* Γ(C, ⊤)` and `etale` on its canonical spectrum morphism |
| Point a, including nonclosed points | `center : C`; the actual field is `C.residueField center` |
| Centered coefficient Taylor expansion | `taylor`, `taylor_spec : isTaylorMap coordinates (C.Γevaluation center).hom taylor`; this specifies residue, k-scalars, and all coordinates, so this is not an arbitrary ring map |
| Ordered original variables Z and their actual position among W,T | `originalVariables`, `originalCoordinates : Fin originalVariables ↪o Fin (m+t)`, `originalVertices`, `vertex_eq` |
| Monotone diagram with precisely the ordered minimal vertices | `monotone` and `vertices` use `MonomialDiagram.IsMonotone`, `IsOrderedVertexFamily`, and `generated` on the ORIGINAL variable set |
| Degree blocks and fixed block ell | Block is represented by its degree `d`, with `block_exists`; earlier vertices have degree `< d`, current vertices degree `= d`, retained prefix degree `≤ d` |
| T is the current essential-variable set | `prefix_has_no_W` says prefix vertices have no coefficient-variable part; `essential_T` says every displayed T-coordinate occurs in that prefix. Thus the prefix essential set is exactly T. Original monotonicity supplies its final-segment property. |
| Later vertices may use remaining Z-coordinates among w | They have no `prefix_has_no_W` restriction. `originalCoordinates` preserves their actual order, even with extra coefficient coordinates interspersed among them. |
| Full regular generator families in R[[T]] | `f : Fin s → MvPowerSeries (Fin t) Γ(C, ⊤)`; no finite-support restriction |
| First coefficient 1 and first exponent alpha_i in W-before-T order | `normalized`, with `MonomialDiagram.IsFirstExponent (blockTaylor taylor (f i)) (α i)` and coefficient equality `= 1` |
| Earlier tests are full coefficients in the complementary variables | `blockSlice S η H` extracts the S-coefficient and retains the entire complementary series; `blockForbidden` includes degree ≤ Q, support in S, and prefix diagram membership |
| All earlier blocks simultaneously | `blockOldKernel α Q d` quantifies over all prefix degrees `h < d`. Degrees with no vertex simply repeat an unchanged prefix or impose no tests. |
| Regular coefficient extractions/full columns of P-minus | The parameter `K : exponent → exponent →₀ Γ(C, ⊤)` records its finite coefficient rows; `blockOperator K φ` is the explicit finite row sum after transporting the regular coefficients along φ. |
| P-minus projects onto the earlier common kernel and fixes it | `old_image` and `old_fixed` |
| Linearity over R[[T minus old essential variables]] | `complement_linear`; the support condition on G is zero exponent in every earlier essential-variable set, equivalently in the last such set |
| P-minus fixes every generator after the previous block | `fixes_later`, with `d ≤ (α i).degree` |
| P-minus minus identity lies in the earlier-generator ideal | `old_ideal`, using degree `< d` and Mathlib `Ideal.span` |
| First-exponent preservation at a when earlier tests pass | `old_first`, over arbitrary full iterated series with coefficients in κ(a)[[W]], flattened in the actual W-before-T order; `blockOldMonomial` is precisely the admissibility condition |
| Finite Q and finite E | `Q : ℕ`, `E : Finset ...`, and `hE : γ ∈ E ↔ blockNewExponent α Q d γ` |

The finite-row representation is a data encoding of the stipulated regular
coefficient operator, not a further finiteness restriction on the series.
A fixed output coefficient of a coefficient extraction uses one input
coefficient; a fixed output coefficient of multiplication by a full column
uses finitely many Cauchy factors. Finite composition and addition retain this
property. Thus the given defining coefficient extractions/full correction
columns have exactly such rows. Entries are regular functions on C. Conversely
the explicit row formula defines the operator on every formal series, without
choosing an extension after restricting or Taylor-expanding the coefficients.
The hypothesis `old_first` tests this same formula, not an unrelated lift of P-minus.

The full exponent α in the theorem is the original vertex embedded into the
ordered Taylor variables, padding the extra coefficient coordinates by zero.
Importantly, monotonicity is imposed on `originalVertices`, not on the padded
diagram: inserting unused coefficient coordinates between original coordinates
would otherwise impose an unjustified stronger monotonicity hypothesis. This
was caught and corrected while reading the statement before delivery.

### Conclusions and actual constructions

| Node clause | Lean rendering |
| --- | --- |
| D_h and first-vertex quotient sets | Prefix family is `{i // (α i).degree ≤ h}`; `MonomialDiagram.generated` and `quotientSupport` are reused. `blockVariables` retains inherited coordinate order. |
| E = bounded new diagram minus extended previous diagram | `blockNewExponent` tests degree ≤ Q, divisibility by a degree-≤d vertex, and absence of a degree-<d divisor; all these prefix vertices have zero W-part. |
| Unique assigned pair (j,beta) | First theorem conjunct is `∀ γ : E, ∃! p : Fin s × exponent, ...`; p.1 has degree d, beta is in the existing `quotientSupport`, and gamma is the exact sum. |
| C_gamma = P-minus(T^beta f_j) | `blockColumn` is the finite sum selecting that unique assigned pair, with a whole monomial multiple of a whole generator; the first conjunct identifies it with the specified column. |
| Columns pass earlier tests | Second conjunct includes `blockOldKernel ... (blockColumn ...)`. |
| Difference from original multiple lies in earlier-generator ideal | Same conjunct explicitly gives the pair and membership of `C_gamma - T^beta f_j` in the degree-<d span. |
| Columns have first exponent (0,gamma) at a | `IsFirstExponent (blockTaylor A.taylor ...) (Finsupp.mapDomain (Fin.natAdd m) γ.val)` |
| B_eta,gamma is the specified coefficient matrix | `blockMatrix` uses `MvPowerSeries.coeff η.val (blockColumn ... γ.val)` |
| B(a) triangular with diagonal 1 | Third and fourth conjuncts give zero below the column's leading exponent in degree lexicographic order, and diagonal equal to one. |
| One open det B nonzero, containing a | `exactBlockOpen = C.basicOpen (Matrix.det B)` and the center-membership conjunct |
| Canonical inverse and prescribed projection formula | `blockProjection` uses Mathlib's `Matrix.inv`, `mulVec` of the coefficient vector of `blockOperator K φ H`, and subtracts the finite sum of FULL transported columns. The `Inv` instance is explicit to prevent Lean from treating a matrix as a bare function type. |
| R-linearity | `ExactBlockOver` gives additivity and scalar compatibility over the coefficient ring. |
| Image is in every earlier kernel and every bounded current forbidden kernel | The image conjunct of `ExactBlockOver` includes the full old slices and the current individual coefficient equalities. |
| Fixes that common kernel; is a projection | The next conjunct gives fixedness; the following conjunct gives idempotence. These together express precisely the stated projection. |
| Regular on this single open | `ExactBlockOnOpen` on `exactBlockOpen` gives finite rows with entries in Γ(C,U) evaluating to the prescribed formula; no further open is chosen. `ExactBlockOver` also asserts that the transported determinant is a unit. |
| P_ell minus identity lies in current prefix ideal | `ExactBlockOver` gives membership in the span of the transported degree-≤d generators. |
| Preserves every admissible first exponent at a | The universal residue-extension conjunct quantifies over H and μ, requires `IsFirstExponent`, `blockOldMonomial`, and the nonforbidden current restriction, and concludes `IsFirstExponent` of the exact formula with exponent μ. The identity extension includes the original residue field. |
| Replace only i > s_ell | `blockReplacement` keeps every degree-≤d generator literally and applies the formula only at larger degrees. |
| Generated ideal unchanged | `ExactBlockOver` equates the two `Ideal.span (Set.range ...)` ideals. |
| Vertex exponent unchanged at a for every generator | The same universal residue-extension conjunct gives the original `α i` as first exponent of each replacement. Later vertices retain all their W components. |
| Every earlier derivative equation unchanged | `ExactBlockOver` equates all `iteratedPartial β` of every retained prefix generator and its original transported series; this includes the chosen earlier vertex derivatives. |
| Every earlier Jacobian unchanged | Its final conjunct equates the full matrices of constant coefficients of the first derivatives of arbitrary chosen earlier vertex derivatives. It includes all the earlier choices and hence their determinants. |
| Generated ideal unchanged at every point, including residue-field extension | The pointwise conjunct takes every V inside U, b in V, every extension ι, and the actual coordinate-normalized Taylor map τ on Γ(C,V), specified on residues/scalars/coordinates. It asserts `ExactBlockOver` both for the residue coefficient map and the full Taylor coefficient map. The latter ideal is in L[[W]][[T]], the same full Taylor ring as L[[W,T]] via `blockFlatten`. |
| No correction tail truncated | All columns are `MvPowerSeries`, and all coefficient transports are the actual `MvPowerSeries.map`; only the column index E is finite. |
| Empty E gives zero correction sum | The last conjunct explicitly asserts `blockProjection = blockOperator` for E empty, after any coefficient transport. |
| All assertions include residue-field extension | The center clause quantifies over `L : Type (max u v)` and every field map ι, asserting `ExactBlockOver`, first-exponent preservation for arbitrary series, and every replacement vertex. The pointwise clause supplies `ExactBlockOver` on the full Taylor rings at every other point and after every extension. Matrix and column normalization identities transport along the same field maps. |

The auxiliary definitions and the input/conclusion packages belong to this
node's explicit construction. They are recorded in `lean.declarations`, with
source/blueprint docstrings. No independent mathematical notion or postponed
helper theorem has been introduced, so no new DAG node is required.

### Dependency declarations used

- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`;
  `AlgebraicGeometry.QuasiCompact` from its quasi-compactness dependency.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `coeff`, `monomial`, `C`;
  the actual `MvPowerSeries.map` coefficient transports.
- `Sheaf.RingTheory.SupportedHomogeneousDivision`: `MonomialDiagram.IsMonotone`,
  `IsOrderedVertexFamily`, `generated`, `quotientSupport`; the full source was read.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.residue`;
  evaluation is the canonical global germ followed by the residue map.
- Already landed `def-trf-formal-initial-diagram`:
  `Sheaf.RingTheory.FormalInitialDiagram`, `MonomialDiagram.IsFirstExponent`.
- Already landed `def-trf-regular-hilbert-coefficient-datum`:
  `Sheaf.AlgebraicGeometry.RegularHilbertCoefficientDatum`, `isTaylorMap`,
  `iteratedPartial`. Both landed definition nodes are added to `stmt_deps` under
  the rule allowing statement dependencies to gain existing landed nodes.
- `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`: `Matrix.inv`, which is the
  adjugate divided by the ring inverse of the determinant; `Matrix.det` and the
  adjugate identities are the existing determinant/adjugate DAG dependencies.
  The only theorem proof is postponed; the accepted shifted-inverse proof
  dependency has no Lean declaration yet and is not imported or restated here.

No dependency module is needed. The recorded definitions were usable.

### Searches actually run

All service searches used the prescribed msearch.py wrapper with Q70 and this item.

- LeanFinder: "Projection of multivariate formal series onto kernels of coefficient
  tests using full correction columns and an invertible finite matrix". Eight hits
  (`MvPowerSeries.inv.aux` and formal multilinear inverse/composition results), none
  stating this construction with the earlier tests and vertex/ideal invariants.
- Loogle: `MvPowerSeries.coeff, Matrix.inv`. Available, zero hits.
- Mathlib grep, RingTheory: `coefficient.*[Pp]rojection|[Pp]rojection.*coefficient|[Cc]oefficientOperator`.
  Available, zero hits.
- LeanSearch: "regular row finite coefficient kernel defining linear operators on
  multivariate formal power series". Eight hits including `MvPowerSeries.coeff`,
  `MvPowerSeries`, `MvPowerSeries.monomial`, and linear-topology definitions;
  none states this simultaneous coefficient-elimination result.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for coefficient projections,
  first exponents, Taylor maps, and regular coefficient kernels found unrelated
  derived-functor projections and the usable Taylor/diagram definitions listed above.
  An exact rg of the item id in `lean/WeilConjectures` gave no hits.
- Read the entire recorded supported-division module, the initial-diagram module,
  the coefficient-datum module including `isTaylorMap`, the relevant signatures of
  Smooth/Etale/LocallyOfFiniteType/residue fields/MvPowerSeries, and the matrix inverse
  definition. There is no existing theorem matching the item.

### Edge cases and source reading

Before drafting, checked the first block (old ideal zero and old kernel all
series), Q=0, Q below the new block degree (E empty), t=0, zero-size derivative
matrices, and extra coefficient variables interspersed among the original
coordinates. The zero original diagram has no block to fix, so `block_exists`
excludes no case of the node. If the vertex is zero then d=0, t=0, E can contain
the empty exponent and the one-by-one solve kills the full forbidden kernel;
this is allowed. Empty E uses Mathlib's empty determinant one, and the final
identity has no nonemptiness hypothesis. First exponents exclude zero series
through the existing definition's nonzero-coefficient clause. Nonclosed points
use the genuine residue field and diagonal Taylor characterization. Universes
are explicit; extension fields use `max u v`, never an independent smaller
universe. The full Taylor ring at another point is retained, not replaced by
coefficientwise evaluation alone.

Read the current blueprint unit proof and local-term-locality proof under
`literature/blueprint/latest`, the node and all six statement dependencies,
and Q21's accepted split report. The latter explicitly separates the ILO
VIII 2.3.11--2.3.13 route reference from the BM 9.12--9.14 finite matrix argument
and its agent refinement. The module docstring copies all eight accepted proof
steps, including the shifted inverse support estimate, without supplying a proof.
No unit, chapter, source statement, accepted split or target was changed.

### Validation

The delivered file compiles cleanly through scompile.py both as the sandbox
module and as `Sheaf.AlgebraicGeometry.ExactBlockCoefficientProjection` (about
3.5 seconds each, 60-second limit). No warning, no implicit variable, and no
proof beyond the single named `sorry` theorem. Delivery dry-run results follow.

The prescribed `deliver2.py ... --no-push` completed successfully: commit
`bc5018b4c76` passes server preflight and compilation; nothing was pushed by
that run. Width, public declaration visibility, and the single named sorry
were also checked against the final source.

I independently opened and read BM Lemma 9.12, equation (9.13), and Definition
9.14 on printed pp.280--281 (PDF pp.74--75) of the
[original paper](https://mahalex.net/seminars/gabber/Bierstone-Milman%20Canonical%20desingularization%20in%20characteristic%20zero.pdf).
The source uses a finite matrix, a triangular specialization, Cramer's rule,
and replacement by subtracting whole generator multiples. The node's simultaneous
old-test refinement is retained as such; the source is not claimed to state
that refinement verbatim. No downloaded file or live source was changed.

## Second reading by Q70

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
