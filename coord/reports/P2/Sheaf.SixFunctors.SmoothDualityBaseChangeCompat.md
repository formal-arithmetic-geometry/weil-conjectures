## What changed

The general-base smooth exceptional base-change theorem is reduced to smooth base change
on affine base charts, using the source-library theorem in
WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange.
The new ExceptionalBaseChangeAffineLocality module proves the affine-cover descent argument:
it constructs the cartesian chart cubes and their jointly surjective open cover, then applies
the new open-restriction comparison and existing derived cover detection.
ExceptionalBaseChangeOpenRestriction isolates the compatibility of the canonical exceptional
base-change mate with open restriction, without quasi-compactness of the restricting opens.
The packet compiles through lcompile.py --all.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension_general.
Proved the new
AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_affine_open.
Added one remaining hole:
AlgebraicGeometry.Etale.isIso_leftDerivedUpperStar_map_baseChange_of_open_restriction
(lem-asd-exceptional-base-change-open-restriction).
Thus one original hole is closed and one new hole added; this is a decomposition, with net zero
holes closed. No other sorry is introduced. The source-library affine-space adjunction
base-change result remains an existing dependency.

## No longer needed

No original import was removed. No original blueprint dependency is claimed pruned:
the affine model theorem retains the etale/affine-space route, and the parent tensor
compatibility proof is unchanged. The earlier scratch tensor-only reduction is not delivered.

## Where the brief, the DAG or earlier work was wrong

The source-library smooth base-change theorem now requires a quasi-separated base.
It cannot directly prove this compatibility bridge, whose signature has no such hypothesis.
The existing vertical-composition theorem requires quasi-compact base-changed factors;
an arbitrary affine open of a non-quasi-separated scheme need not have quasi-compact inclusion.
Consequently that composition theorem cannot directly justify the open-base restriction step.
The new coherence lemma states that separate part explicitly, with the full compactification
and mate argument in its docstring. All existing signatures are preserved.

The interrupted resumptions preserved the sandbox but reset the budget marker: the observed
start changed from 2026-10-19 16:03:25 UTC (1792425805.6698363) to
2026-10-19 19:26:46 UTC (1792438006.6105134). These are the available attempt identifiers.
The packet was revalidated against current sources and compiled again; launcher metadata was
not edited.

## New nodes

lem-asd-exceptional-base-change-affine-locality: a proved generic descent theorem, using
jointly surjective open pullbacks and the separate open-restriction compatibility lemma.

lem-asd-exceptional-base-change-open-restriction: compatibility of the canonical exceptional
base-change mate with open base restriction. It is independent of smoothness and coefficient
invertibility, and is a strictly separate coherence step rather than the original theorem
under another name. Its source is prop-asd-smooth-base-change, coherences (i) and (iii).

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
