## What changed

Filled both existing theorem proofs in
`Sheaf.CategoryTheory.RelativeTrivialCyclicMap`, preserving every public signature,
definition body, attribute and import. Seven proved private helpers establish that
trivial coefficients have identity generator, that both complexes have zero
differentials and support only in degrees zero and one, and construct the two
nonzero coordinate isomorphisms. `HomologicalComplex.Hom.isoOfComponents` assembles
them; cancellation and componentwise extensionality establish normalization and
uniqueness. `forgetTrivialExist` uses the underlying identity isomorphism and
subtype extensionality.

Updated only `proof`, `proof_deps` and `proof_origin` of
`def-sfb-relative-trivial-cyclic-map` to describe this implementation of the
existing docstring argument. No new nodes or shared interfaces were introduced. The construction works uniformly
for zero coefficients and arbitrary restriction maps; negative degrees and degrees
above one are handled by explicit zero-object proofs.

Searches used LeanFinder for two-term cochain isomorphisms, Loogle for biproducts
with a zero object, and ripgrep over Mathlib and both source roots. The useful
existing tools were `isoBiprodZero`, `isoZeroBiprod`, `Functor.map_isZero`,
`HomologicalComplex.extendXIso` and `HomologicalComplex.Hom.isoOfComponents`.

Validation: the complete module compiled cleanly through `lcompile.py` in 19.8 seconds,
with no warnings and the original transparency options retained.

## Proved and sorry left

Closed both of the item's two holes:

- `CategoryTheory.RelativeCyclic.trivialTotalIsoExist`
- `CategoryTheory.RelativeCyclic.forgetTrivialExist`

Both belong to `def-sfb-relative-trivial-cyclic-map`. No holes remain in the item,
none were added, and none were split off. The proof uses the existing
`CategoryTheory.RelativeCyclic.generatorEndExist` characterization in
`def-sfb-relative-derived-invariants`; this delivery does not close that existing
upstream hole or the other transitive infrastructure holes.

## No longer needed

None. Both existing public imports remain necessary for the exported definitions.
No node, module, declaration or unit step was withdrawn or bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement or definition correction was needed. The definition node had an
empty proof list although its two existence theorems already had the correct
coordinate and identity arguments in their docstrings; its proof fields now
record those arguments. The existing source-reference qualification remains.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
