## What changed

Proved `AlgebraicGeometry.Scheme.pur_integral_reduction_uniform_tor` from simultaneous
finite integral perfect charts. Its signature is unchanged. The proof establishes
finite projectivity of every quotient term, computes finite constant homology models
on the slice charts, derives intrinsic constructibility, proves the all-module Tor
bounds globally and on every stratum, and proves bounded constructibility of the
already retained compatible etale origins. Their normalization equation is retained
verbatim. The source finite-stalk constructibility predicate is obtained using the
proved finite-value/finite-stalk comparison.

Added `Sheaf.Paper.StratifiedFiniteProjectiveTor`, with a complete proof of
`AlgebraicGeometry.Scheme.stratified_finite_projective_tor`. The argument transports
slice models to the covering schemes, applies the bounded flat-complex Tor theorem,
and detects the tensor-test homology on the finite covers and strata. It uses the
existing source-library tensor pullback and conservative detection APIs.

Added `Sheaf.Paper.PurIntegralFinitePerfectCharts` for the separate simultaneous
chart-selection and quotient-comparison step of Proposition 6.6.11. Moved the five
existing chart abbreviations there verbatim and publicly imported it from the item;
all names, signatures, bodies, visibility and original public imports are preserved.
The change record is `coord/changes/T9-pur-integral-chart-constructions.md`.
No source-library declaration was changed or removed. The unit route is unchanged.

Validation: all three modules compile together against the current library with
lcompile.py --all. A textual signature/body comparison confirms that
the original theorem signature and all five abbreviation bodies are unchanged.
All Lean lines are at most 100 characters. No definition contains sorry.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.pur_integral_reduction_uniform_tor`
(node `lem-pur-integral-reduction-uniform-tor`), by a complete combining proof.
The item module now has zero sorry.

The new theorem `AlgebraicGeometry.Scheme.stratified_finite_projective_tor`
(node `lem-pur-stratified-finite-projective-tor`) is fully proved, with zero sorry.

Added one remaining hole:
`AlgebraicGeometry.Scheme.pur_integral_finite_perfect_charts`
(node `lem-pur-integral-finite-perfect-charts`). This is strictly the chart-selection
and actual quotient-comparison part of the source argument. It assumes no Tor,
finite quotient homology, constructibility of reductions, or bounded etale-origin
conclusion. The item derives all of these from it with real Lean proofs. Its source,
edge cases and proof in words are recorded in its docstring and node.

Thus this is a decomposition: one original hole closed, one lower hole added,
net zero holes, with the independent Tor-descent step fully proved. There are no
other holes added by this packet. Existing imported declarations may retain holes.

## No longer needed

Removed these original proof imports from the item:

- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`
- `Sheaf.AlgebraicGeometry.FiniteStratificationWidePullback`
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.AlgebraicGeometry.StratifiedLocalCohomologicalBounds`
- `Sheaf.Paper.PerfectChartTensorComparison`
- `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`
- `Sheaf.Paper.PerfectStrataUniformReductions`
- `Mathlib.RingTheory.Flat.Basic`
- `Sheaf.Algebra.Homology.FlatScalarRealizationFlat`
- `Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleLocalDerivedRestrictionComparisons`
- `Sheaf.AlgebraicGeometry.NoetherianStratumDetection`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`

The new chart node still needs the finite refinement, coefficient inverse image,
tensor pullback, finite-cover selection, perfect-chart tensor and local-restriction
nodes. They move below chart selection and are not globally claimed as pruned.
The actual-valuation-ring local-perfect criterion replaces the broader integral
stratified-perfect characterization on that route.

The quotient terms are finite projective by ordinary scalar extension, so
`lem-weil-pbc-standard-quotients-perfect` is unnecessary. Scalar homology and exact
constants replace `lem-weil-pbc-perfect-strata-uniform-reductions`. The source flat
model and tensor pullback APIs replace `lem-sfb-flat-scalar-realization-flat`,
`lem-weil-pbc-independent-bounded-flat-kflat` and the Tor use of
`lem-weil-pbc-local-derived-restriction-comparisons`. Source finite quasi-compact
pullback detection replaces `lem-weil-pbc-noetherian-stratum-detection`.
No compact-support comparison unit is used: exact conservative comparison and
homology descent prove boundedness of the retained origins directly. The underlying
constructible-origin and site-comparison results remain needed through source APIs.

Removed the corresponding twelve obsolete direct entries from the original node's
`tool_uses`, retaining its constructible-origin and site-comparison approvals in order.
The projective-module-flat result remains used by the proved Tor node. No existing
module is withdrawn, and no whole-library module is claimed pruned solely because
this item has no current Lean importer.

## Where the brief, the DAG or earlier work was wrong

The planned cohomological-bounds theorem is not itself an all-module Tor theorem.
The new Tor proof tests every degree-zero sheaf and uses strict term bounds, flatness,
and conservative pullback detection. The original conclusion was not weakened.

The project and source-library etale bounded-constructibility predicates have distinct
definitions. The proof explicitly converts their homology constructibility predicates
using `isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf`; it proves both bounds
and does not identify these predicates by definitional equality.

The quarantine/rework attachment is preserved by restoring the item's full source and
its theorem. Its absence at the quarantine path is not used to withdraw anything.
The retained packet was rechecked against the current sources and compiled again.
The current downstream query finds eight consumers; the change record now lists them.
Its earlier zero-importer note was stale. The identical public reexports require no
consumer adaptation.
The preceding attempt did not push: the delivery queue remained full.

## New nodes

`lem-pur-integral-finite-perfect-charts` records the separate finite simultaneous
perfect-chart selection and quotient-comparison argument of Proposition 6.6.11.
Its declaration is in `Sheaf.Paper.PurIntegralFinitePerfectCharts`, with one sorry.
It has the original geometric hypotheses and retains the same scalar representatives
for every positive reduction. Empty schemes, empty lists and all-zero lists are
explicitly allowed.

`lem-pur-stratified-finite-projective-tor` records descent of a fixed projective term
interval from slice charts to every tensor test on the strata and the whole scheme.
Its declaration in `Sheaf.Paper.StratifiedFiniteProjectiveTor` is fully proved and
allows unordered endpoints and empty covers. It neither assumes constructibility
nor deduces Tor bounds from cohomological boundedness.

Change record: `coord/changes/T9-pur-integral-chart-constructions.md`.

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
