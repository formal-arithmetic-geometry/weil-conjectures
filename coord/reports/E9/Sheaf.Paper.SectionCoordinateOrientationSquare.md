## What changed

Replaced the sorry in AlgebraicGeometry.Etale.sectionCoordinateOrientation_square by
an explicit factorization and pasting proof. The new orientation-free source and
family chart maps are genuine composites of the existing sectionMap, sectionLocality
and centre transports. Both centre equations, including the Rees augmentation equation,
are proved. Private helpers prove that each original orientation is its chart map
followed by the standard zero-section affineSectionIso.

The standard affine case already existed as sectionCoordinateCounit_standard in the
parent SectionCoordinateCounitNormalization, which imports the item. Extracted that
unchanged declaration to StandardAffineSectionOrientation to remove the import cycle;
the parent publicly imports it. Proved standardAffineSectionOrientation_one from it:
normalization fixes the inverse affineDualizingIso maps, and naturality plus inverse
cancellation turns the rawComparison equality into the required standard square.

The remaining geometric locality square is separately stated in
SectionCoordinateChartRestriction. The existing coherence API uses bundled
ExceptionalSectionFamily and ExceptionalFamilyEtaleMap diagrams; identifying their
comparison formulas with these raw Rees chart maps is the remaining geometric glue. The item combines that square with the standard
square by Functor.map_comp and associativity. Existing target statements and all
existing declaration signatures are unchanged. No source-library files are edited.

Validation: lcompile.py --all compiled SectionCoordinateChartMaps (35.8 s),
SectionCoordinateChartRestriction (41.3 s), StandardAffineSectionOrientation (42.0 s),
the item (42.4 s) and the adapted parent (36.1 s), without warnings or errors.
The unchanged direct importer AffineDiagonalTraceRestriction initially took 62.9 s;
profiling it took 28.8 s, and its clean final source compiled in 43.9 s. No consumer
edit was needed, and its temporary copy and all profiling options are removed.
The item and moved-standard signatures were compared verbatim with the originals.
No newly added DAG edge closes a cycle.

Change record: coord/changes/E9-standard-affine-section-counit-extraction.md.

## Proved and sorry left

Closed the item's one syntactic hole:
AlgebraicGeometry.Etale.sectionCoordinateOrientation_square
(lem-trf-section-coordinate-orientation-square).

Added one strictly smaller geometric obligation:
AlgebraicGeometry.Etale.sectionCoordinateChart_restriction
(lem-trf-section-coordinate-chart-restriction), in its own module. It concerns only
exceptional base-change/locality maps and contains no Tate transport, trace tower,
normalized affine adjunctions, or affine orientation hypothesis. Its docstring gives
the complete base-change, open-locality and inverse coordinate-locality pasting proof.
This delivery is a decomposition, with net zero syntactic holes closed after this split.

The existing sorry AlgebraicGeometry.Etale.sectionCoordinateCounit_standard moved
unchanged to StandardAffineSectionOrientation and is now attached to
lem-trf-standard-affine-section-orientation. It is neither a new hole nor a closed one.
The adapted parent retains its two original sorries unchanged:
AlgebraicGeometry.Etale.affineCoordinateCounit_baseChange and
AlgebraicGeometry.Etale.exists_coordinateCounitAdjunction
(lem-trf-section-coordinate-counit-normalization).

New complete proofs include SectionCoordinateChartMaps.sourceCentre,
SectionCoordinateChartMaps.familyCentre and standardAffineSectionOrientation_one.
No definition contains a sorry or selects data from an unproved existence theorem.
The only data selection in the proof is elimination of the existing standard theorem
inside a proposition. Empty bases, the zero ring and d=0 use the same centre, functor
and inverse-isomorphism equations; no extra nonemptiness or invertibility is imposed.

## No longer needed

None. No existing import is removed and no existing mathematical dependency is
withdrawn. The original two proof steps are distributed over the standard affine
node and the geometric chart restriction node. Their original trace, twist, Rees
and exceptional-coherence dependencies remain needed by those respective steps.
No source-library declaration is removed. The unchanged consumer copied for testing
is removed from the sandbox after its successful compile.

## Where the brief, the DAG or earlier work was wrong

The planned standard affine assertion was already stated in the parent, but the
parent/item import cycle prevented its direct reuse. Extracting that assertion
preserves the original obligation and avoids adding a duplicate affine-orientation
sorry. The original orientation square also suppressed the separate centre transport
and orientation-free chart maps; these are now explicit constructions with proved
centre equations. No mathematical statement has been weakened or disputed.

## New nodes

- def-trf-section-coordinate-chart-maps owns the orientation-free constructions and
  their proved source/Rees centre equations in SectionCoordinateChartMaps.
- lem-trf-standard-affine-section-orientation owns the existing moved
  sectionCoordinateCounit_standard and its proved fixed-presentation consequence.
- lem-trf-section-coordinate-chart-restriction is the strictly geometric fibre
  locality step, with a complete proof in words and one sorry in its own module.

The parent node's declaration list and standard-case dependency are updated; the
item node records the actual factorization and pasting proof. The unit route stays.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
