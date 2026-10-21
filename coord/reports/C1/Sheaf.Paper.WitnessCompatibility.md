## What changed

Proved `AlgebraicGeometry.ProEtale.pbcComparisonReductionMap_isIso` for an arbitrary
coefficient ring map. The proof establishes ordinary scalar-extension compatibility
by iterated mates, proves comparison flatness using local relations, transports the
calculation to derived categories through functorial K-flat resolutions, and then
identifies the result with the fixed chosen adjunctions. The module also adds private
helper lemmas and explicit functor arguments that keep the expensive derived-category
elaboration folded. Four public definitions receive explicit functor arguments or a
result type; their constructions and public signatures are unchanged. The required
change records are included under `coord/changes/`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.pbcComparisonReductionMap_isIso`.

Holes added: none. Sorries left in the delivered module: none.

## No longer needed

No imports, nodes, or modules are withdrawn. The proof does not directly invoke the
generic ringed-topos tensor-pullback or change-of-rings nodes; they remain statement
dependencies of the witness interface. The unit route is retained.

## Where the brief, the DAG or earlier work was wrong

The earlier proof step left `pbcComparisonReductionMap_isIso` open even though the
required mate and K-flat argument can be stated and proved entirely with existing
source-library declarations. The source-library comparison-flatness theorem also
imposes a Noetherian coefficient hypothesis that is unnecessary here; the proof uses
the full relation kernel and finite pure-tensor expansions instead. No statement is
weakened or disputed.

Change records:

- `coord/changes/C1-pbcFixedScalarExtension-explicit-functors.md`
- `coord/changes/C1-pbcFixedScalarExtensionComp-explicit-functors.md`
- `coord/changes/C1-pbcDerivedComparisonRestrict-explicit-functors.md`
- `coord/changes/C1-pbcComparisonReductionMap-explicit-functors.md`

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
