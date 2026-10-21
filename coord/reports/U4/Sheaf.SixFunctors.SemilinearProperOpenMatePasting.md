## What changed

Proved `AlgebraicGeometry.ProEtale.SemilinearProperOpen.evalR_isIso` and
`AlgebraicGeometry.ProEtale.SemilinearProperOpen.evalJInv_isIso` for the comparisons
as defined, with their existing adjunctions and section normalizations.

The ordinary evaluation square is first identified with the constant-diagram lift
of the existing varying-ring evaluation square. Exact derived square composition
then factors this square through the ordinary module category. For direct image,
mate pasting combines the existing varying-ring `evalPMate_isIso` with the
constant-diagram `chi` comparison. For open extension, inverse mate pasting combines
the existing varying-ring `evalJInv_isIso` with the constant-diagram open comparison.
The latter follows from a proved private exact-localization inverse-mate lemma.
Private adjunction-uniqueness arguments handle the specified choices of open adjoints.
All new private helpers have complete proofs.

Added proof-only imports for adjunction uniqueness, constant-tower normalization,
exact square composition, and the derived mate comparison. Updated the existing
node's proof, proof dependencies, and proof origin to record this argument.
No public signature, definition, instance, public import, or consumer was changed.
No new module or node was introduced. The command changes are documented in
`coord/changes/U4-semilinear-evaluation-proof-local-commands.md`, as requested by
the first server preflight. They are scoped to the existing Evaluation section or
to the new private helpers; the record lists all 37 downstream modules, which
need no adaptation.

Validation: the entire item module compiled without errors or warnings through
`lcompile.py`; the final successful server compilation took 38.8 seconds. Import
cycle checks allow the new Sheaf dependencies. New lines satisfy the 100-character
limit. This is a partial delivery of two of the module's nine original holes.

## Proved and sorry left

Holes closed (2):

- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.evalR_isIso`
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.evalJInv_isIso`

Holes added: 0. Split off: 0. Both proved declarations and all seven remaining
holes realize `lem-sf-semilinear-proper-open-mate-pasting`. The seven remaining
original `sorry` declarations are:

- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.semilinearProperOpenMatePasting`
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.gamma_identities`
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.rhoPullInv_isIso`
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.rhoR_isIso`
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.rhoJInv_isIso`
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.gamma_scalarRestriction`
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.gamma_evaluation`

These seven declarations retain their original statements, docstrings, and bodies.
The proofs use existing lower declarations, including the varying-ring evaluation
mate invertibility declarations; no claim of an axiom-free target closure is made.

## No longer needed

None. No import, node, module, or dependency has been withdrawn. All original
proof dependencies remain needed by the unfinished clauses of this node. The
constant-diagram factorization reuses the existing varying-ring comparisons rather
than introducing duplicate intermediate statements.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The first preflight required a change record
because it conservatively treats the added proof-local commands as an interface
change. The record now documents the exact commands, their scope and consumers. The evaluation comparison is not
literally the varying-ring module comparison: evaluation here also forms a constant
strict tower, and the specified exact open adjunction differs from a right-derived
presentation. The proof makes both extra identifications explicit. It uses
localization normalization and mate pasting, never faithfulness of derived evaluation.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
