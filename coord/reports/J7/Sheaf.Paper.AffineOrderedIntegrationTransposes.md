## What changed

Moved the 36 existing public construction declarations through sourceLine, together
with their proved private helpers, verbatim to Sheaf.Paper.AffineOrderedIntegrationData.
AffineOrderedIntegrationTransposes publicly reexports them and keeps its former public
imports. The data module has no holes. The original suffix retains proved private copies of
pullback_plus and tensorLine_plus (and the latter's flat-tensor helper), whose private
names otherwise belong to the data module. This lets the new successor calculation import
the independently constructed trace and transpose without importing their comparison
theorem. The unchanged prefix compiled in 38.9 seconds before the split was used.

Replaced the body of ordered_integration_transposes by two inductions and direct assembly:
its dimension-zero HEq comes from the existing unique characterization; one induction
identifies the transpose with the published comparison recursion; the other proves
invertibility using the existing coordinate-line adjunction. The exceptional compositor
is invertible by the existing proved relative-Hom-bijection argument, including its
identity normalization at zero. The actual source/exceptional naturality square is an
application of the single-line naturality theorem to integrationTranspose_d.

AffineLineComparisonNaturality proves that single-line theorem from the existing
orderedAffineComparison_natural at dimension one. It identifies the source normalization
with a natural isomorphism, uses naturality of the identity exceptional compositor,
and cancels both invertible comparison maps. It adds no hole. The remaining geometric
successor calculation is isolated as integrationTranspose_successor in its own module.
No signature of any original declaration is changed, and no source-library file is edited.

Change record: coord/changes/J7-affine-ordered-integration-data.md. It includes the
verbatim old/new construction block and the complete consumer table.

Validation: the cleaned main module compiled in 36.2 seconds. The line-naturality,
construction-data, and successor modules passed the delivery compile. All four current
direct consumers compiled unchanged against the reexport: ChartTargetOpenDescent,
ProjectionTensorIntegration, VectorIntegrationUnitTranspose, and
ModelAffineIntegrationOrientation. Their temporary sandbox copies were removed.
The original three theorem signatures and the moved construction block were compared
with the shared source and remain verbatim. Final delivery checks validate the packet.

## Proved and sorry left

Original module: three holes before this delivery, two afterward.
Closed body: AlgebraicGeometry.ProEtale.AffineOrderedIntegration.ordered_integration_transposes
(lem-pur-affine-ordered-integration-transposes), proved by induction from the named
successor lemma and existing project declarations. This is a decomposition, not a net
closure or an axiom-free proof of the entire result.

Added one hole:
AlgebraicGeometry.ProEtale.AffineOrderedIntegration.integrationTranspose_successor
(lem-pur-affine-ordered-integration-successor).

The two unchanged original holes are:
AlgebraicGeometry.ProEtale.AffineOrderedIntegration.ordinary_counit_formula and
AlgebraicGeometry.ProEtale.AffineOrderedIntegration.pro_coordinate_projection_composition,
both attached to lem-pur-affine-ordered-integration-transposes. Their existing signatures,
sources, proof plans and bodies remain intact. The packet therefore leaves three holes
in total, for net zero (one closed, one added).

New proved theorem:
AlgebraicGeometry.ProEtale.AffineSpacePurity.lineComparison_natural
(lem-pur-affine-line-comparison-naturality). It depends on the already stated
orderedAffineComparison_natural, whose preexisting sorry is not introduced by this packet.
The construction data and all private helpers have zero sorry.

## No longer needed

The original module drops the proof imports
WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues,
WeilConjectures.ConstructibleSheaf.Monoidal, and
WeilConjectures.ConstructibleSheaf.SpecializationCriterion. They remain in the
construction-data module, where their applications moved.

No module or mathematical obligation is withdrawn. No original public import is removed:
its existing exported interface is retained. The new data module omits the unused public imports of ShriekTensorComposition and
CompactSupportSiteCoherence, and the three unused
proof-context imports `import all Sheaf.Paper.FiniteProjectionActionLaws`,
`import all Sheaf.Paper.CompactSupportSiteCoherence`, and
`import all Sheaf.AlgebraicGeometry.ShriekTensorComposition`; the remaining suffix uses
them in the original module. FiniteProjectionActionLaws remains a public import of the data module because
reassociate uses its canonical projectionActionAssociator. The omitted imports are not
dependencies of the relocated constructions.

For the final assembly, a new uniqueness-of-right-adjoint argument on all d is unnecessary:
invertibility follows by induction from CoordinateLineAdjunction and the already proved
conjugate-compositor argument in CoordinateSectionArrows. The one-coordinate contraction
and the two untouched counit/projection obligations retain their lower proof dependencies;
none is claimed pruned from the target closure.

The parent no longer directly cites det-sp-unique-right-adjoint: its all-d uniqueness
step is replaced by the two inductions. The obsolete duplicate final proof steps
are removed; def-exchange-projection and def-weil-pbc-adjunction-mate are no longer
direct proof dependencies of the final naturality calculation (the former remains
a statement dependency and both remain available through the constructions). The dependencies
lem-pur-vector-integration-site-comparison, lem-sf-proetale-constructible-origin,
lem-sf-pullback-tor-amplitude, and lem-sf-tensor-ctf now attach to the relocated data
and its applicability results. The corresponding obsolete direct tool_uses entries
for det-sp-unique-right-adjoint and the latter three lem-sf nodes are removed in order.
These dependencies remain reachable through the retained constructions and tools;
this packet claims no module pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is changed or disputed. The final all-d result did not need
another all-d naturality or invertibility hole: the defining zero characterization,
existing line adjunction, relative-Hom compositor argument, and dimension-one ordered
naturality suffice for those parts. The missing trace-contraction successor is explicitly
separated from the induction which consumes it. The unit route is retained. The proof uses the existing
lem-pur-ordered-affine-comparison-natural from sk-prop-an as a cross-unit tool, only at
dimension one to obtain arbitrary-arrow line naturality. The local unit has no stated
arbitrary-arrow naturality lemma. No tool_uses approval was added by the worker;
the independent reviewer/maintainer can record this tool use.

## New nodes

`def-pur-affine-ordered-integration-data` attaches the unchanged independent constructions
to their new data module. Their old names and actual maps are preserved by public reexport.

`lem-pur-affine-ordered-integration-successor` states exactly the single-coordinate
trace/transposition calculation of the source's ordered argument. It asserts only a
successor identity, not all-d equality, invertibility, naturality, or zero normalization.
Its proof docstring records the ordinary line counit, projection/tensor contraction,
canonical mate, site transport and even-shift calculation needed to finish it.

`lem-pur-affine-line-comparison-naturality` is a proved extraction of dimension-one
ordered naturality through the canonical source and exceptional normalizations. It is
used at the actual arrow from the ordered source to the exceptional target.

The parent node now records these steps and the relocated Lean attachments. The source
is the current blueprint's projection-purity agreement proof, final paragraph, with the
parent DAG's expanded steps. Mathlib searches used leanfinder, loogle and grep; they
returned generic adjunction/naturality tools, with no affine trace contraction. Project
searches supplied the reused line adjunction, compositor proof and ordered naturality.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
