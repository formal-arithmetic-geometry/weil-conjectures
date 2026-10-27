## What changed

Proved `semilinearProperOpenMatePasting` and `gamma_identities` with their original
statements. The proof identifies the actual intrinsic operations and comparisons
with the existing varying-ring constructions, transports vertical and horizontal
pasting and identity equations, and applies the mate-cube theorem to the existing
alpha base-change cube.

Added six supporting modules: `SemilinearProperOpenCore` contains the unchanged
core constructions and adjunct normalization;
`SemilinearProperOpenNormalization` proves the concrete comparison; and
`Sheaf.CategoryTheory.ExactClopenNormalization` contains the proved general
localization, compositor and equality-transport calculations. The existing scalar
and evaluation constructions are retained verbatim in
`SemilinearProperOpenScalarSupport` and `SemilinearProperOpenEvaluationSupport`.
`SemilinearProperOpenCoherence` retains the original proved compositor-associativity
statement and proof. Its nine private supporting calculations retain exact aliases
in the assigned module. Both unfinished gamma compatibility statements remain there.
The split follows profiling of a monolithic proof that exceeded the per-file limit;
serialization was a substantial cost, with no single proof dominating.

All 101 existing public declaration headers and all existing public non-theorem
bodies are textually unchanged. The original public imports remain. Exact private aliases
preserve the original helper types and binder information for current import-all
consumers. Three noncomputable forwarding definitions return the original private
constructions. No source
library declaration is removed or modified, and no unit route is bypassed.

The assigned module re-registers its eighteen original instances after all proof
imports, in their original order and at their original priorities. This preserves
the original registration precedence after the declarations move to support modules.

Three unclaimed consumers also receive compile-time repairs.
`DiagramOpenClopenShiftModels` gives its three product equivalences concrete
private definitions and proved functor equations. Explicit restriction isomorphisms
transport the insertion maps, and cancellation proves the same projector laws.
The original public structures and generic exact-localization proofs move to
`DiagramOpenClopenShiftCore`; the original open-model and identity calculations
move to `DiagramOpenClopenShiftOpenSupport`. The proved theorem
`openModels_nonempty` constructs the original open-model record. The final theorem
selects this fully proved witness. Its statement stays unchanged. The original
generic gluing calculations remain beside the final clopen model; the cover proof
uses an explicit complementary-range rewrite in place of a fragile `simpa`.

`SemilinearEvaluationRingSquare` changes only its private import to the evaluation
support API. `SemilinearCompactifiedGraphEvaluation` disables costly automatic
injectivity generation and publicly re-exports its unchanged ordinary data from
`SemilinearCompactifiedGraphData`. Eleven existing helper holes move with that
data; the final existing hole stays in the original module. All original graph
headers, data bodies and proof bodies remain unchanged. No new hole is introduced.
The graph module has no current direct Lean importers. Change record:
`coord/changes/semilinear-proper-open-consumer-elaboration.md`.

Validation: all thirteen delivery files pass artifact-writing compilation.
The final twenty-six-file general consumer recheck passes without failures.
Both direct importers of the clopen model pass against its new artifact, and the
ring-square's ordinary-adjunction importer passes against its new artifact.
Thus thirty-one of the thirty-five original direct importers pass, including the
refreshed integral ambient-model source, which now imports through another module.
The original thirty-five sources were unchanged during this final validation.

Four timing failures also occur against the published library:
`SemilinearEvaluationDerivedAdjunction` (87 seconds),
`CompactSupportCondensedRealization` (62 seconds), `FiniteFreeCompactComposition`
(75 seconds), and `SemilinearCompactSupportCoefficientTransport` (75 seconds).
Those four unchanged sources are not included; these are baseline failures rather
than forced adaptations. All unchanged validation copies have been removed from
the packet. The delivery tool performs final compilation, axiom and preflight checks.

## Proved and sorry left

Closed 2 of the original 4 holes:

- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.semilinearProperOpenMatePasting`.
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.gamma_identities`.

The two unchanged remaining holes, both attached to
`lem-sf-semilinear-proper-open-mate-pasting`, are:

- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.gamma_scalarRestriction`.
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.gamma_evaluation`.

Added 0 holes. Every new supporting theorem is proved. The six support modules
of the assigned item and both clopen support modules contain no `sorry`. No closed hole is replaced by a
split-off statement.

The graph consumer family retains twelve pre-existing holes, all attached to
`lem-sp-semilinear-compactified-graph-evaluation`, in namespace
`AlgebraicGeometry.ProEtale.SemilinearGraph`:

- `inclusion_continuous` and `restrictionRing_existsUnique`.
- `restriction_isRightAdjoint` and `sumExtension_exact`.
- `openRestriction_existsUnique` and `levelRestriction_isRightAdjoint`.
- `levelSum_exact` and `sumEvaluation_existsUnique`.
- `levelOpenRestriction_existsUnique` and `openEvaluation_existsUnique`.
- `pushEvaluation_existsUnique` and `semilinear_compactified_graph_evaluation`.

The eleven graph helper holes are in `SemilinearCompactifiedGraphData`; the final
`semilinear_compactified_graph_evaluation` hole remains in the original graph module.

Thus the assigned module has two remaining holes; the complete thirteen-module
packet has fourteen, with zero newly introduced holes.

## No longer needed

The assigned node no longer needs the external support nodes
`lem-sf-semilinear-clopen-unit-projector` and
`lem-sf-semilinear-compositor-coherence`: their relevant intrinsic unit and section
coherence calculations are already proved in the core and intrinsic coherence support. Their proof-dependency
edges are removed; the retained intrinsic compositor proof now has its own node. This is pruning of the assigned route; their files and nodes
are preserved because other parents may still need them.

The generic module publicly imports the exact-derived adjunction, restriction
composition and adjunction-composition APIs its statement needs. The new supporting
files also omit unused direct proof imports of
`WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique` and
`Sheaf.AlgebraicGeometry.ProperOpenClopenProjector`, respectively.

The assigned module also drops direct proof imports of the scalar-derived and
scalar-adjunction modules, constant-tower direct-image normalization, and
exact-localization inverse mates. Those needed
for the retained coefficient proofs occur in the appropriate support file. The
assigned file also omits unused direct proof imports of
`WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates`,
`WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique`,
`WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`, and
`Sheaf.CategoryTheory.DerivedExactSquareComposition`; the core and normalization
files import these APIs where their proofs need them. Each
new coefficient file publicly imports the intrinsic core; it omits the original
finite-origin and full proper/open-calculus imports its statements do not use.

The ordinary graph data file omits the three derived-only proof imports of
`RightDerivedFunctorOfQuasiIsoResolutions`, `ExactSquareDerivedCounit` and
`KInjectiveResolution`; the final graph-evaluation file retains them.

The evaluation ring-square consumer replaces the private `import all` of the
entire mate module with the private evaluation support import. Its public mate
import stays unchanged.

No module is withdrawn. The remaining scalar and evaluation proof dependencies
stay for the two untouched holes. Normalization-only proof imports occur in their
supporting modules, rather than the assigned module. The core does not import the
scalar-derived comparison, fixed-origin witness, constant-tower normalization,
proper/open pasting or strict-tower direct-image coherence modules that its
constructions do not use. Those modules remain available where the retained proofs need them.

## Where the brief, the DAG or earlier work was wrong

The planned appeal to varying-ring pasting needs a comparison of the actual chosen
constructions. Equal underlying functors alone do not identify separately specified
derived adjunctions and their compositors. The delivery supplies the missing
unit-normalized exact-localization bridge, reusing the proved calculations from
the ambient beta/clopen comparisons without creating an import cycle. The general
compositor proof is adapted from the already proved adjunction-compositor
normalization.

The original 3,181-line module plus the bridge exceeded the file limit. Profiling
also showed that the remaining coefficient implementation needed a further split.
The module split preserves the constructions and public statements, with
exact aliases for the private API used by current importers. Change record:
`coord/changes/semilinear-proper-open-module-split.md`.

## New nodes

`lem-sf-exact-localization-open-compositor` records the proved normalization of
left-adjoint composition under exact localization. Its module is
`Sheaf.CategoryTheory.ExactClopenNormalization`. The proof uses normalized
adjunction composition and uniqueness, the cochain unit equation, and localization
extensionality.

`lem-sf-intrinsic-varying-ring-mate-normalization` records the proved equality of
the intrinsic and varying-ring proper/open mates. Its module is
`Sheaf.SixFunctors.SemilinearProperOpenNormalization`. The proof identifies the
ordinary chosen operations, localizes beta and the clopen projector, normalizes
open composition, identifies alpha by exact transformation pasting, and takes
proper-adjunction mates. Both nodes add zero holes.

`lem-sf-intrinsic-semilinear-compositor-coherence` attaches the original proved
`compositor_associativity` and its unchanged private section and adjunction
calculations to `SemilinearProperOpenCoherence`. It adds no hole.

`def-sf-semilinear-scalar-normalization-data` and
`def-sf-semilinear-evaluation-normalization-data` attach the existing coefficient
constructions to their new support files. Their statements record the retained
ordinary and derived functors and normalized comparisons. They introduce no new
mathematical constructions, proof obligations or holes.

`lem-sf-diagram-open-model-construction` records the proved `openModels_nonempty`
constructor theorem. It packages the original open-model record and its complete
proofs; the final clopen theorem uses this genuine part of its argument. It adds
zero holes.

`def-sp-semilinear-compactified-graph-data` attaches the original ordinary graph
constructions and eleven unchanged existing helper theorem holes to their new
support file. It adds no declaration name, mathematical assumption or hole. The
original graph node retains the final derived-evaluation theorem and records its
ordinary-data dependency.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
