## What changed

Filled the four geometric helper proofs in
`Sheaf.SecSmoothPurity.NestedAffineOrientation`, preserving all signatures and
all definitions and imports. `blockEq` inducts on the outer coordinate block.
`blockProjection` carries the scheme and its projection together in a dependent
pair, then extracts the projection equation for the specified `blockEq`
transport. This avoids rewriting only one endpoint of a dependent morphism.
`mapEtale` applies stability under base change to
`affineTraceMap_isPullback`. `chartComposite` precomposes and postcomposes that
square's commutativity equation and substitutes the two chart equations.
The induction starts at zero and requires no nonemptiness of the scheme.

This is a partial delivery of the module's existing holes, as permitted for a
module with several holes. No intermediate theorem or new hole is introduced.
The four new proof bodies passed single-file server compilation in 10.7 seconds.
The delivery preflight checks the final file with its retained original imports
and probes the axioms of its declarations.

## Proved and sorry left

Closed 4 of the original 5 holes, all in namespace
`WeilConjectures.PurityFiniteSetting.NestedAffine`:

- `blockEq`
- `blockProjection`
- `mapEtale`
- `chartComposite`

Added holes: none. Split-off statements: none.

The single remaining hole is
`WeilConjectures.PurityFiniteSetting.NestedAffine.nested_affine_orientation`,
node `lem-sp-nested-affine-orientation`. Its statement, source and complete
seven-step proof docstring are unchanged. Its affine integration, ordinary/site
comparison, tensor-compositor and normalization arguments remain to be written
in Lean. In particular this delivery does not claim the main orientation
comparison is proved.

## No longer needed

None. No import, node or module is withdrawn. The DAG proof plan of the
remaining main theorem is retained: having proved its geometric helpers does
not justify pruning its orientation or integration dependencies. In particular
`AffineSpacePurityComposition` and `OrderedAdjointTowerRegrouping` remain for
its positive- and zero-rank integration comparisons. The four helper proofs
use the existing public affine-tower API, so no new import is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The four helper proofs follow their
existing docstrings. The library also has a regrouping equation for
`iteratedAffineLine` in `AffineSpacePurityCompositionMaps`; transporting its
separate tower/projection definitions to `affineTraceTower` would require the
same dependent induction, so the direct induction is used here.

The main theorem's declared projection/composition lemmas use transported
pro-etale presentations, while this module specifies ordinary-etale arrows.
Their further comparison equations must be retained in the remaining proof;
they are not definitional rewrites that would close the main hole directly.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
