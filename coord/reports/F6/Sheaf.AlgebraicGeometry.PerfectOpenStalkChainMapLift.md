## What changed

Retired Sheaf.AlgebraicGeometry.PerfectOpenStalkChainMapLift, listed in
coord/retire-items.tsv, in favour of the already proved stronger source theorem in
WeilConjectures.AlgebraicGeometry.PerfectOpenStalkChainMapLift. Its source supplies a
canonical comparison and needs neither affineness of U nor perfectness of Q.

Migrated the private import and theorem application in
Sheaf.AlgebraicGeometry.PerfectOpenStalkDerivedHomDescent and
Sheaf.AlgebraicGeometry.PerfectStalkQuasiIsoDetection. Each now names the canonical
comparison explicitly; all consumer public signatures and public imports stay
verbatim. Updated the item node attachment and the relevant parent proof steps.
Both adapted modules compile individually through lcompile.py. Declaration-local
unusedVariables linter suppression preserves the original, now unused hypotheses
without warnings. No source-library file changes.
Change record:
coord/changes/F6-retire-perfect-open-stalk-chain-map-lift.md.

## Proved and sorry left

The assigned module originally had zero sorries. Holes closed: none (0 of 0).
Holes added: none. Holes left in delivered modules: none. No decomposition.
The source declaration
AlgebraicGeometry.Scheme.exists_affine_perfect_open_stalk_chainMap_lift is already
proved; its canonical comparison realizes the original existential statement.
Both adapted consumer theorems retain complete proofs.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.PerfectOpenStalkChainMapLift. Both private
imports of it are replaced by the source module. The withdrawn file's imports of
WeilConjectures.AlgebraicGeometry.PerfectComplex,
WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor,
WeilConjectures.AlgebraicGeometry.PerfectOpenStalkDegreewiseLift,
WeilConjectures.AlgebraicGeometry.PerfectOpenStalkDegreewiseShrink and
Sheaf.Paper.DerivedHomMayerVietoris disappear with that duplicate. These dependencies
are still used elsewhere; no further module or node is claimed as pruned.

The item node and both proof dependencies (degreewise lift and shrink) stay needed:
they now attach to the existing source proofs. Both parent nodes retain their edge
to the item node. No unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

This assignment is a listed zero-hole retirement rather than a new proof obligation.
The duplicate retains unnecessary hU and hQ binders and existentially chooses the
comparison which the source theorem supplies canonically. The unchanged consumer
interfaces remain valid after explicitly naming that canonical comparison.
Library search found the exact source theorem; LeanFinder and Loogle found no
shorter Mathlib result. The proof route and mathematical node statement are kept.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
