## What changed

Restored `lean/Sheaf/AlgebraicGeometry/PerfectComplexDescent.lean` from its
quarantine archive as assigned by `coord/rework.tsv`. Replaced its stale public
import of the withdrawn `Sheaf.AlgebraicGeometry.DerivedPullback` with
`WeilConjectures.AlgebraicGeometry.DerivedPullback`, which provides the actual
public declaration used in the signature. This is the only changed line relative
to the archive. The signature and complete existing proof of
`AlgebraicGeometry.perfect_complex_descends` are preserved verbatim.

The proof applies `compact_open_induction_on` to `PerfectDescentOnOpen`, using
`perfect_descent_affine_open` for the empty and affine cases and
`perfect_descent_open_union` for the induction step. Quasi-compactness over an
affine makes the source compact. Presenting the top open by the identity recovers
the exact canonical pullback and isomorphism in the conclusion. Both the empty
source and the single-affine-cover case are covered by the same induction.
This is the essential-surjectivity argument of Stacks `perfect.tex`,
`lemma-descend-perfect` (09RF), whose proof was read alongside the current
predicate and both dependency theorem signatures. All three existing DAG proof
dependencies and the unit route remain necessary and unchanged.

Validation: the unmodified archive reproduced the public-visibility error.
After the one-line repair, `lcompile.py` compiled the module cleanly in 4.9 s,
using the current open-union dependency from its private overlay. A bytewise
comparison confirms that the import replacement is the only archive change.
The resumed attempt revalidated the same packet through `lcompile.py` (exit 0,
4.9 s) and the import-direction check (no cycle). The theorem, its dependency
signatures and its archived parent were checked against the current sources.

Change record: `coord/changes/PerfectComplexDescent-public-derived-pullback.md`.

## Proved and sorry left

This is a zero-hole restoration repair. The archived module has zero sorries;
the delivered module has zero sorries. Holes closed: none (0 of 0). Holes added:
none. Split off: none. No theorem is newly claimed as proved in this session;
the complete existing proof of `AlgebraicGeometry.perfect_complex_descends`
(node `lem-pc-perfect-complex-descent`) is restored with its working interface.
There are no remaining sorry declarations in any delivered module.

## No longer needed

Removed the stale import of the empty withdrawn module
`Sheaf.AlgebraicGeometry.DerivedPullback`, replacing it with the actual adopted
source module. No mathematical dependency, node or library module is pruned.
The existing affine-open, two-open-union and descent-on-open dependencies stay.
The quarantined parent `FilteredCartesianPerfectDescent` still needs this theorem
both in its Lean proof and in its DAG proof dependencies; it is not withdrawn.

## Where the brief, the DAG or earlier work was wrong

The stage-3 repair has zero holes, as permitted by the brief. The quarantine row
records the original cluster rollback. The newest failure, recorded against
`a7d709d57a` on 2026-10-24, pinpoints the stale public import: the Sheaf
derived-pullback duplicate became an empty module, causing an unknown-identifier
error at the public signature. The compiler explicitly requests the adopted
source import used by this repair. No mathematical statement or proof-route
correction is needed.
The current node attachment is preserved; the quarantine archive is untouched.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
