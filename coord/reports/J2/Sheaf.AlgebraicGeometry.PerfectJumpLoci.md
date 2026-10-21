## What changed

Restored `lean/Sheaf/AlgebraicGeometry/PerfectJumpLoci.lean` verbatim from the
quarantine path named in `coord/rework.tsv`. The complete proof of
`AlgebraicGeometry.Scheme.pseudoCoherent_jump_loci`, its signature, its public and
private imports, its docstrings and its existing DAG attachment are preserved.
The restoration record is
`coord/changes/J2-perfect-jump-loci-restoration.md`.

The proof uses the existing bounded finite-free local fibre model, the finite-free
homology semicontinuity theorem, and the derived-fibre base-change isomorphism.
Compact open strict sublevels give constructible level sets by set difference;
open chart images give global upper semicontinuity. Scalar extension preserves
finrank and gives the arbitrary-base-change clause. No new result is split off.

Validation: current dependency sources and the restored item compile in sandbox
import order through `lcompile.py --all`; the item takes 4.4 seconds. A separate
`#print axioms` check reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
The unchanged current dependency sources are included in the sandbox only to
refresh stale compiled dependencies; they carry no source changes for delivery.

## Proved and sorry left

Zero archived holes; zero holes closed; zero holes added; zero holes split off;
zero holes left. The restored theorem
`AlgebraicGeometry.Scheme.pseudoCoherent_jump_loci` has a complete proof, attached
to `lem-sc-perfect-jump-loci`. This is restoration of a previously proved module,
not new proof progress or a decomposition. No definition or theorem contains
`sorry` in the restored item.

## No longer needed

None. Every archived import is retained. All three current proof dependencies
remain used: `lem-sc-pseudo-coherent-fiber-finite-free-model`,
`lem-sc-finite-free-complex-homology-upper-semicontinuous`, and
`lem-sc-derived-fiber-cohomology-base-change`. No node, module or unit route is
withdrawn. In particular, the quarantined parents
`Sheaf.AlgebraicGeometry.PerfectLowestRankBoundOpen` and
`Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible` still use this
public theorem; absence of live importers does not justify withdrawal.

## Where the brief, the DAG or earlier work was wrong

The assigned item is absent from the live source tree but present in quarantine,
and already has zero textual holes. Its actual repair is restoration after the
cluster restore. There is no current item-specific return requiring a different
mathematical argument. The archived proof agrees with the current DAG and with
Stacks Tag 0BDI, whose three conclusions and pseudo-coherent hypothesis are retained.

The first compile using published artifacts alone failed at imports because the
old compiled local-model dependency contained the retired
`Sheaf.AlgebraicGeometry.PseudoCoherentComplex`; a later attempt exposed the
analogous retired `Sheaf.AlgebraicGeometry.DerivedFiberBetti` collision. Compiling
unchanged current sources for `PseudoCoherentFiberBoundedAboveModel`,
`PseudoCoherentFiberFiniteFreeModel`, and `DerivedFiberCohomologyBaseChange` in
sandbox order resolves both collisions. The archived item then compiles verbatim;
no import workaround or dependency interface change is delivered.

Edge cases: integer thresholds handle the empty sublevels at nonpositive ranks;
the rank-zero level is the difference of the less-than-one and less-than-zero
sublevels. Empty schemes have no local point obligations. The argument is local
on arbitrary affine charts and uses compact opens, so it does not assume that X
is Noetherian, quasi-compact, or quasi-separated. The base-change finrank equality
needs no finite-dimensionality assumption. No target, definition, statement,
universe or hypothesis changes.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
