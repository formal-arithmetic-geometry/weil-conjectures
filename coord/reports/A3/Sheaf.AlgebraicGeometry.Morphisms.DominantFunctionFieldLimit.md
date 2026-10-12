## What changed

Proved `AlgebraicGeometry.Scheme.exists_dominant_function_field_limit` in
`Sheaf.AlgebraicGeometry.Morphisms.DominantFunctionFieldLimit` without changing its
statement, universes, visibility, or original public imports. Added the proof-only import
`Sheaf.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods`.

The diagram, cone, and inclusions are constructed explicitly from generic stalk maps.
Private proved helpers establish their compatibility by cancelling the canonical generic
inclusions, which are monomorphisms. The limit proof uses Mathlib's affine-transition
limit topology basis to detect the generic point, then the already proved universal
property of the spectrum of a stalk as the limit of its affine neighbourhoods.
All private definitions contain actual constructions; none chooses data from an
unproved existence theorem.

Updated `lem-sbc-dominant-function-field-limit`'s proof, proof dependencies and origin
to match this route. The unit's `realized` fields contain no required node-level steps;
the generic-fibre limit assertion required by the unit is retained.

Validation: the file compiles without warnings through `lcompile.py`.
`#print axioms AlgebraicGeometry.Scheme.exists_dominant_function_field_limit` reports
only `propext`, `Classical.choice`, and `Quot.sound`. The delivery dry run is the final check.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Scheme.exists_dominant_function_field_limit`
(node `lem-sbc-dominant-function-field-limit`). Added 0 holes. There are no remaining
`sorry`s in the delivered module. This is a complete proof, not a decomposition.
The affine-neighbourhood universal property used from the existing library is proved.

## No longer needed

Removed imports: none. Removed proof-dependency nodes or modules: none; the original
node had no proof-dependency imports. No new residual modules are introduced.
The planned explicit filtered-colimit-of-fraction-fields calculation, choice of an
affine stage and cofiltered slice, and cofinality transport are unnecessary: the
universal-property argument proves the desired scheme limit directly. These previously
unstated steps do not become new work items. Both original Mathlib imports remain.

## Where the brief, the DAG or earlier work was wrong

The original plan was mathematically usable, but did not expose Lean dependencies for
the fraction-field colimit calculation. The shorter topology and affine-neighbourhood
route closes the theorem using existing proved APIs instead. The qcqs stage hypotheses
are unnecessary for this argument; they remain unchanged in the public statement.
A scoped unused-variable linter option accommodates those retained hypotheses and the
unused existential limit-proof binder in the original signature.

The original declaration docstring retains its valid fraction-field proof sketch;
the updated DAG describes the actual Lean proof. No statement correction or forced
adaptation is necessary. Search via launcher leanfinder, loogle and grep found the
function-field, stalk-map and affine-transition APIs, but no exact function-field
limit theorem. Stacks Tag 0EZJ was read for the generic-fibre limit assertion. Tag
01ZA concerns Noetherian approximation itself, rather than the affine ring limit
calculation suggested by the old docstring; the actual proof uses the Mathlib
basis theorem tagged 01Z4 and the affine-neighbourhood limit theorem sourced at
0GWT and 01YW.

## Second reading by A3

1. Compared the delivered module with the repository version. The public theorem signature and all existing declaration signatures are unchanged byte for byte; the only interface-level addition is a proof-only import. Verdict: pass.
2. Compiled the delivered module with `lcompile.py`; it compiles without errors or warnings. The theorem has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; the scratch axiom check reports only `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. Reviewed the proof route and split statements. No statements were split off and no new holes were added; the private helpers are concrete constructions and the use of the existing affine-neighbourhood limit theorem is valid. Verdict: pass.
4. Checked pruning and imports. The added `SpecStalkLimitAffineNeighbourhoods` import is proof-only and necessary; no removable imports or proof dependencies were found. Verdict: pass.
5. Compared the DAG proof, dependencies, origin, and unit route with the Lean proof. The node records the universal-property route and its sole proof dependency, while the unit's generic-fibre limit assertion remains represented. Verdict: pass.

Changed only this second-reading report; no Lean code, statements, definitions, or DAG fields were altered during review.
