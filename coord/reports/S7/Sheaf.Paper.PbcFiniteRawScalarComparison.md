## What changed

Proved `AlgebraicGeometry.Scheme.pbcFiniteRawScalarComparison_existsUnique` in
`Sheaf.Paper.PbcFiniteRawScalarComparison`, preserving both existing public declarations,
their signatures, docstrings, and public imports. Added proved private helpers identifying
finite/completed coefficient maps and integral tensor functors, and descending the existing
integral comparison by an explicit denominator-clearing naturality argument. Added the private
proof import `Mathlib.RingTheory.Localization.BaseChange`. Updated the existing node's proof,
proof dependencies, and proof origin to describe this argument.

Change record: `coord/changes/S7-finite-raw-scalar-private-proof-context.md` records
the added scope commands conservatively classified by preflight as an interface edit.
The downstream inventory has zero current Lean importers; no adaptation is needed.

The semantic searches found Mathlib's localization lifting interface; the shorter route here
uses the already recorded integral comparison and the actual unchanged-object scalar
localization, without constructing a new categorical localization equivalence. LeanFinder,
Loogle, project grep, and the existing implementation in `PbcAutomorphismTransport` were read.

Validation: the complete item compiled cleanly through `lcompile.py` (25.3 seconds),
with no warnings. All added helpers are proved private theorems; no axiom or data
construction was added. The delivery preflight performs the additional required checks.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.Scheme.pbcFiniteRawScalarComparison_existsUnique`
(node `def-zl-pbc-finite-raw-scalar-comparison`). No holes added or split off. No `sorry`
remains in the delivered module. Its dependencies retain their own existing proof obligations;
this delivery proves the requested comparison from their published declarations.

The proof covers arbitrary independent scheme/algebraic-closure universes, the empty scheme,
all integral objects and localized arrows, and both equal and distinct coefficient fields.
Equal fields use the existing integral comparison, so the tensor-unit normalization is kept.

## No longer needed

None. Both existing public imports supply the statement and constructions used by the proof.
The original node had no proof dependencies or proof steps to prune. No modules or nodes are
withdrawn, and no blueprint unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The node's proof was empty, although the declaration's docstring already gave a valid plan.
That plan is now made explicit and implemented. No statement or definition repair was needed.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
