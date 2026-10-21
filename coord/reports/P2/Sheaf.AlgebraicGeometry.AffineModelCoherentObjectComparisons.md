## What changed

Re-proved `AlgebraicGeometry.exists_affineModelCoherentObjectComparisons` in
`WeilConjectures.AlgebraicGeometry.AffineModelCoherentObjectComparisons`, the
implementation re-exported by the assigned Sheaf module. Constructed θ and θlim
with the existing explicit two-label comparison constructor, and constructed the
four object comparisons directly from its one-model chart components. Proved the
four triangles from the one-model chart cocycle, elementary naturality and the
projection-comparison triangle. No comparison-family existence theorem is used.
The assigned Sheaf re-export includes a route comment documenting this source
proof repair; its public import and existing module docstring are unchanged.

The existing 22 source declarations retain their signatures, attributes and
visibility, public imports, and non-theorem bodies. Eight private helpers provide
explicit object and projection constructors, folded equation types and their
proved transport API. The labelled equation retains the full natural comparison;
its two Bool cases reduce to the one-model chart cocycle. These interfaces keep
large derived-category arguments folded. The five new private definitions use
`no_expose`; existing declaration attributes are unchanged. The node records the
new proof route. The existing
`affineModel_scalarConjugation_nat` proof applies its component theorem directly;
its former simplification only unfolded the definition of an iso component.
Change record: `coord/changes/P2-affine-model-explicit-comparisons.md`.

## Proved and sorry left

Assigned Sheaf module: 0 initial holes, 0 holes left. Adapted source module:
0 initial holes, 0 holes left. Closed: 0. Added: 0. Split off: 0.

`AlgebraicGeometry.exists_affineModelCoherentObjectComparisons` is re-proved;
its node is `lem-pc-affine-model-coherent-object-comparisons`.
The private `affineModelTransportTriangle_of_comp`,
`affineModelChartTransportTriangle` and `affineModelLabelledTransportTriangle`
are fully proved. The five private definitions explicitly construct isomorphisms
or state their equations; none chooses an existence witness. There are no
new public declarations, new modules, new nodes, or remaining proof obligations.

Validation: source and re-export compile with artifact output and no warnings.
The unchanged stage-Hom, limit-Hom, Hom-equation packaging and bottom-model
comparison modules compile against these artifacts. All eighteen exported
declarations and those four downstream theorems have only `propext`,
`Classical.choice` and `Quot.sound` as axioms. The consumer copies and axiom probe
were temporary validation files and are not delivered.

## No longer needed

Removed the proof import
`WeilConjectures.AlgebraicGeometry.AffineCoordinateComparisonCoherence` and use of
`exists_affineCoordinateComparisonTransportFamily`. Neither that module nor
`WeilConjectures.AlgebraicGeometry.AffineCoordinateComparisonFamilyBase` remains
in this item's import closure. The corresponding nodes
`lem-pc-affine-coordinate-comparison-coherence` and
`lem-pc-affine-coordinate-comparison-family-base` are unnecessary for this proof.
Their existing source declarations and proofs are preserved. No module is withdrawn.

Bottom-arrow two-label natural isomorphisms γ and γlim are unnecessary: their
individual components suffice to construct the object comparisons. The explicit
derived comparison, chart cocycle, K-flat scalar-extension and projection-comparison
theory remain needed. The existing scalar-conjugation API and its scalar-extension
proof dependency remain needed. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The brief predates source reconciliation: the assigned Sheaf module is now a
zero-hole re-export, and the adopted source already proves the chart comparison,
its naturality and its one-model cocycle. Reusing these proved declarations makes
the recommended cut without rebuilding the lower theory or handing on an
obligation. This is a proof and dependency repair with zero original holes;
no sorry closure is claimed.

The previous proof constructed full natural isomorphisms for the bottom arrows,
although only their object components were used. Constructing these components
directly removes that unnecessary packaging. The stage and cocone isomorphisms
still retain all cross-label morphisms, including coincident models.

The initial direct elaboration expanded the two object equations into very large
terms. Compact geometric object constructors and named equation types avoid that
expansion; the labelled equation keeps the actual two-label comparison folded
until its Bool case is proved. The complete source file, including artifact
output, compiles in 56.1 seconds; the assigned re-export compiles in 2.6 seconds.
No proof obligation was moved to another module.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
