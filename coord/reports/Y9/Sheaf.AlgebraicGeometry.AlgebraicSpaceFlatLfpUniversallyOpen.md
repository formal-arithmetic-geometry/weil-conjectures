## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.universallyOpen_of_flat_of_locallyOfFinitePresentation`
with its original signature. Construct compatible scheme atlases, apply Mathlib's
`UniversallyOpen.of_flat` to the chart map, and descend openness after every
algebraic-space base change through a continuous surjective scheme-source atlas.
The whole-image conclusion follows from the identity base change.

Repair of the returned delivery: removed the duplicate private theorem
`representableWith_baseChange` from the assigned module. Exposed the existing proved
helper in the unclaimed `Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence` module and
added a private proof import to reuse it. Its statement and proof are unchanged;
only visibility and a source/proof docstring change. No source-library file changes.
Change record: `coord/changes/Y9-reuse-representable-base-change.md`.

The proof also privately imports `AlgebraicSpaceAffineEtaleCover` and Mathlib's
Yoneda limit API. The assigned node's proof, proof_deps and proof_origin follow the
implemented argument, including reuse of the chartwise module's base-change helper.

Validation: `lcompile.py --all` generated compiled artifacts for both modified
modules in import order. `deliver3.py` repeats the compilation and axiom probes. The added import is acyclic, all Lean lines are at most 100
characters, and the updated 314-node dependency closure is acyclic. The change
record lists every current downstream consumer of the exposed helper's module.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.AlgebraicSpace.universallyOpen_of_flat_of_locallyOfFinitePresentation`
(node `lem-sfb-flat-lfp-space-universally-open`). Zero holes added; zero remain in
either delivered module. No statements are split off and no definition contains a
hole. The existing `chartwise_etale_permanence` theorem and all its helpers retain
their complete proofs. The original base-change helper's proof is unchanged.

The assigned proof uses existing stated dependencies, including the currently
unfinished `exists_affine_etale_cover_and_point_topology`, as permitted by stage 3.

## No longer needed

Removed the redundant private import `Mathlib.AlgebraicGeometry.Morphisms.Etale`:
the statement dependencies already expose it. Removed the duplicate local proof
of `representableWith_baseChange`; the existing theorem is reused instead.

The proof does not call the three declarations of
`lem-trf-space-fibre-products-etale-covers`: scheme tests provide the needed schemes,
Mathlib constructs scheme pullbacks, and presheaf pullback pasting proves their
properties. That node remains in stmt_deps and its module remains publicly imported
by `AlgebraicSpaceMorphismProperties`; it is not withdrawn or globally pruned.

The planned equality of inverse images of arbitrary point images and its
common-field lifting calculation are unnecessary. `IsOpenMap.of_comp` descends
openness through the continuous surjective source atlas. Point-surjectivity is
proved by testing on field representatives and lifting through a surjective scheme
test. The existing affine-atlas theorem supplies openness of the target atlas.
No module is withdrawn or globally pruned.

## Where the brief, the DAG or earlier work was wrong

The statement is unchanged and true. The plan's last two steps shorten by descent
along a continuous surjective source map, without identifying a space fibre product
with a topological fibre product. Empty spaces, empty opens, identity maps and
non-quasi-compact sources are covered. The unit's route and statements are preserved.

The returned packet duplicated a private theorem. Importing its module alone cannot
make that name available. This repair exposes the original proved helper in place
and reuses it. All 54 current downstream modules were checked textually; none
mentions the formerly private helper. Its existing callers are internal to its
unclaimed defining module. Their statements and proofs remain intact.

## Second reading by Y9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
