## What changed

Completed the Lean proof of
AlgebraicGeometry.ProjectiveBundleQuotientGeometry.projective_bundle_quotient_geometry
with its original statement, from its four declared geometric dependencies and the
new separate affine coefficient lemma. The classification proof uses both inverse
identities and invariance under quotient isomorphisms to prove actual uniqueness.
The pullback clause uses the stated arbitrary-pullback identity. Open and free
compatibility come from the tautological chart theorem; separatedness comes from
the separatedness theorem. The canonical-map clause combines the affine coefficient
normalization with the fraction morphism's canonical-map equation.

Moved all seven data declarations verbatim into the new
Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientData module. The original module
publicly reexports it. This breaks the actual import cycles between the assigned
module and its chart/inverse proof dependencies. Adapted one public import line in
each of SymmetricProjTautologicalCharts (held by J2) and
LineQuotientChartInversePullback (held by G3); every declaration there is unchanged.
The old definition node now attaches to the data module; a new definition node
records the four comparison predicates formerly attached to the theorem node.

Server lcompile --all compiled all five sandbox modules. No definition contains a
hole, and no source-library module or target statement changed. The extracted seven
definition bodies were compared byte-for-byte with the originals. The new lemma
was checked mathematically at the zero module, zero ring, empty affine chart and
arbitrary non-finitely-generated quasi-coherent module: the surjective line quotient
hypothesis forces the required generation, including the degenerate empty cases.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.ProjectiveBundleQuotientGeometry.projective_bundle_quotient_geometry
(node lem-trf-projective-bundle-quotient-geometry). The item module has zero sorry.

Added one hole, in the separate theorem
AlgebraicGeometry.Scheme.Modules.line_quotient_trivialized_coefficients
(node lem-trf-line-quotient-trivialized-coefficients), in its own module. It is the
algebraic coefficient construction only: no Proj map, tautological datum,
classification, uniqueness, pullback naturality, separatedness or free comparison
occurs in its conclusion. Its docstring gives a full proof, including the unit
irrelevant-ideal argument using affine quasi-coherent pullback and surjectivity.
This is a decomposition, one hole closed and one added, not a net hole reduction.
Attempts to prove the coefficient lemma identified the normalized-adjunction and
monoidal pullback coherence needed to prove the homogeneous product equation;
these exploratory incomplete private helpers are not part of the delivery.

The two adapted dependency modules retain their existing holes unchanged:
AlgebraicGeometry.SymmetricProjTautologicalCharts.symmetric_proj_tautological_chart_gluing
(node lem-trf-symmetric-proj-tautological-chart-gluing) and
AlgebraicGeometry.ProjectiveBundleQuotientGeometry.line_quotient_chart_inverse_pullback
(node lem-trf-line-quotient-chart-inverse-pullback). These are existing dependencies,
not holes added by this packet. ProjectiveBundleQuotientData has zero holes.

## No longer needed

No declared geometric dependency is pruned: all four are used. No module is
withdrawn. The following original proof imports are no longer directly needed in
the item: Sheaf.CategoryTheory.SiteModuleSheafGluing,
WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections,
Mathlib.AlgebraicGeometry.Gluing, Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic,
Mathlib.AlgebraicGeometry.AffineScheme,
WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction,
Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra,
Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules, and
WeilConjectures.AlgebraicGeometry.RelativeProj.Basic.
Their lower-level work is delegated to the already stated chart and inverse
lemmas rather than repeated in the assembly. The nine original public imports
are retained transitively by the publicly reexported data module. The separatedness
proof import remains.

## Where the brief, the DAG or earlier work was wrong

The stated proof dependencies could not originally be imported: both chart and
inverse modules publicly imported this same module for its definitions. Restoring
either original import in the final sandbox produces the cycle errors quoted in
the change record and below. The data-module extraction repairs this without
changing the mathematical definitions or a statement.

The fraction map's RelativeGradedLineMap.IsCanonicalMap quantifies conditionally
over ring maps with the prescribed homogeneous values. In contrast, this item's
IsCanonicalMap asserts existence of such a map and specifies the quotient generator
coefficients. Thus the former cannot be applied directly to discharge the latter.
The DAG's assembly needs the separate coefficient construction, now stated and
recorded explicitly. It is the affine algebra construction in Tags 01OA/01O9,
strictly below the geometric classification and inverse identities.

## New nodes

lem-trf-line-quotient-trivialized-coefficients records the separate coefficient
construction, in Sheaf.AlgebraicGeometry.LineQuotientTrivializedCoefficients.
Its proof steps separate homogeneous multiplicativity from the unit irrelevant
ideal. It carries the statement, sources, searches, full proof in words and Lean
attachment. It is the only new theorem and the only new hole.

def-trf-projective-bundle-comparison-data records four existing unchanged
comparison predicates in ProjectiveBundleQuotientData. The other three unchanged
data declarations keep their existing def-per-projective-bundle-quotient-data
node, whose Lean module attachment moves to the data-only module.

Change record: coord/changes/X5-projective-bundle-quotient-data.md.

## Forced adaptations

SymmetricProjTautologicalCharts (J2), line 8, and
LineQuotientChartInversePullback (G3), line 14, each change only
`public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry` to
`public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientData`.

With the first original restored, lcompile --all reports:
`the modules import one another in a cycle: Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry, Sheaf.AlgebraicGeometry.SymmetricProjTautologicalCharts`.
With the second original restored, it reports:
`the modules import one another in a cycle: Sheaf.AlgebraicGeometry.LineQuotientChartInversePullback, Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry`.
Both commands exit 1 before compiling. The two adapted files compile, and the
whole packet compiles. Every signature, visibility, definition body and theorem
body in those two held files is unchanged. The changed imports are necessary for
the assigned theorem to use its declared proof dependencies.

## Forced adaptations

### Sheaf.AlgebraicGeometry.LineQuotientChartInversePullback
NOT FORCED: the original compiles unchanged against the changed dependencies. Adapted module compiled in the delivered set; the reader judges whether the change is right.

### Sheaf.AlgebraicGeometry.SymmetricProjTautologicalCharts
NOT FORCED: the original compiles unchanged against the changed dependencies. Adapted module compiled in the delivered set; the reader judges whether the change is right.

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
