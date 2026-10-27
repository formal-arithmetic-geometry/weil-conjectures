## What changed

Repair of returned head `d9f7fd601be`: the independent reviewer passed the
mathematics; landing rejected a reviewer override named
`T8-point-tate-comparison-data.md`. The change record is present at its
repository path `coord/changes/T8-point-tate-comparison-data.md`.
`tools/batch_land.py` requires the flattened reviewer-fix filename
`T8-point-tate-comparison-data.change.md` for that record. Use that name
if applying a reviewer override; the repository record itself keeps `.md`.
The record now documents this landing interface explicitly. No Lean or
mathematical change was requested. All 25 moved declarations and docstrings
and the main theorem signature were compared with the current shared source
and are identical; existing node copies retain current non-owned fields.
The delivery tool rebuilds the commit on freshly fetched `sheaf-dag`.

Replaced `WeilConjectures.PointTateFiber.coefficientComparisons`' single sorry by a
complete assembly from four strictly smaller named statements. Constructed
`canonicalSheaf`, `canonicalIntegral`, and `canonicalRational` as actual composites
of existing fixed isomorphisms. Proved their arbitrary-section tensor formulas,
rationalization square, and integral and rational identity and tower equations.
The main proof derives negative finite dual reduction from the published signed
reduction theorem, derives the localization formula by tensor balancing, and
obtains the final point-fibre stage independence from equality of source
representatives and the defining pointQbarFibre formula.

Moved the existing 25 helper declarations, verbatim, into
`Sheaf.Paper.PointTateFiberComparisonData`, publicly reexported by the original
module. This is necessary to let the four new argument modules import the same
carriers/composites without an import cycle through the theorem they prove.
The main theorem signature is byte-identical to the source signature, and all
moved definition bodies and signatures are byte-identical. The only transitive
existing consumer, `Sheaf.Paper.PointWeilPairingRealization`, continues to receive
`rationalSizeNormalization` through the public reexport, without adaptation.
The existing size-coordinate node's Lean attachment follows its declarations.
The change record is `coord/changes/T8-point-tate-comparison-data.md`.

Repair validation: server-only `LCOMPILE_NO_LOCAL=1 lcompile.py --all` completed
with exit code 0 for all seven modules in import order, with no warnings or
errors (result `e449feb3c90ddbac7702d19c`). The new statements were checked in their written arguments at m=0, m=1, m=-1, n=0 (the positive quotient exponent is 1),
the identity embedding, and M=L in its natural-language argument. The finite
comparison proof uses balancing in a possibly nonreduced ring and assumes no
field structure on the quotient. Root generators are prescribed by the input e,
and all coefficient comparisons are the actual specified maps.

## Proved and sorry left

Closed the one original hole by decomposition:
`WeilConjectures.PointTateFiber.coefficientComparisons` (1 of 1 original sorries).
This is a decomposition, not a completed sorry-free proof: four lower holes are
added. No sorry remains in the item module. No sorry occurs in any definition.

Proved without additional local holes in PointTateFiberCanonicalComparisons:
`canonicalSheaf_tensor`, `canonicalIntegral_tensor`,
`canonicalRational_compatibility`, `canonicalRational_tensor`,
`canonicalIntegral_identity`, `canonicalIntegral_tower`,
`canonicalRational_identity`, and `canonicalRational_tower`.

Every new remaining sorry is a standalone public theorem with source and full
proof in words, one per new module:

- `WeilConjectures.PointTateFiber.normalizedSectionGenerators`:
  `lem-pur-point-tate-normalized-section-generators`.
- `WeilConjectures.PointTateFiber.finiteSectionComparison`:
  `lem-pur-point-tate-finite-section-comparison`.
- `WeilConjectures.PointTateFiber.canonicalDerivedCoordinates`:
  `lem-pur-point-tate-derived-comparison-coordinates`.
- `WeilConjectures.PointTateFiber.canonicalCommonStage`:
  `lem-pur-point-tate-common-stage-coherence`.

The first contains only generator normalizations and no coefficient-isomorphism
existence. The second concerns only the finite section quotient. The third
concerns fixed constructed comparisons and only derived normalization squares;
it has no generator or finite reduction assertions. The fourth is equality of
source representatives, before applying the point fibre, with no root,
localization, finite reduction, or point-fibre conclusion. None restates the
original theorem or repackages all its hypotheses and conclusion.

## No longer needed

No mathematical module or existing declaration is withdrawn, and no original
proof dependency is pruned from the remaining argument. The unit route is kept.
The top file no longer directly imports IntegralTwistBaseChange or
FiniteFreeCompletedScalarComparison: their roles remain in the actual canonical
construction and the derived-coordinate step. The other original public imports
are retained in the reexported data module, so consumers receive the same names.

The original step-6 compositum detour is unnecessary for the stated nested-stage
comparison M≤N: equality of each common-stage source representative with the fixed
source map, followed by the existing point-fibre representative specification,
already proves the nested-stage equality. No node is removed for this observation.
The arbitrary-section identity/tower proofs also avoid any additional lemma that
pure tensors of a chosen root basis span: repeated use of the scalar-extension
adjunction reduces equality directly to the tensors with all coefficients one.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or target was changed. The DAG's sentence that the two
ordinary scalar-extension models are the same needs an actual bridge: they are
separate chosen functors. The existing proved
`isomorphismScalarSheafModel_existsUnique` supplies the needed normalized bridge;
canonicalSheaf uses its inverse before twistLineScalarIso. Merely treating the
two models as definitionally equal would not typecheck.

The existing node groups helper definitions and the main theorem in one module.
Separate ownership and the public reexport are recorded so lower lemmas do not
have a circular import. This relocation is unrelated to compile time.

The two deferred root-coordinate argument modules do not import the root-coordinate
module solely for their future proofs; its node remains a proof dependency of each.

Mathlib searches (recorded in the new nodes and searches.jsonl) used leanfinder,
loogle, leansearch, grep, direct searches of both project roots, and whole
blueprint searches for point Tate, root coordinates, and scalar extension.
They found generic tensor/localization APIs and the existing project comparison
bridge, but no duplicate of these four precise intermediate statements.

## New nodes

`def-pur-point-tate-comparison-data` records the moved carriers and fixed
composites; the two existing size-coordinate definitions keep their original
node owner. `def-pur-point-tate-canonical-comparisons` records the three constructed
canonical maps and their proved tensor/coherence API.

`lem-pur-point-tate-normalized-section-generators` isolates steps 1--3 on roots,
positive reduction and signed scalar normalization. It uses the existing proved
root-coordinate theorem rather than duplicating its construction.

`lem-pur-point-tate-finite-section-comparison` isolates step 2 on sections of
signed sheaf reduction, for all positive coefficient quotients.

`lem-pur-point-tate-derived-comparison-coordinates` isolates the exact-single,
size-descent, completion and rational scalar normalization diagrams of steps 4--5.

`lem-pur-point-tate-common-stage-coherence` isolates the step-6 source morphism
identity. The main file proves its point-fibre consequence, including independence
of enlargement, using the defining formula of the existing point functor.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
