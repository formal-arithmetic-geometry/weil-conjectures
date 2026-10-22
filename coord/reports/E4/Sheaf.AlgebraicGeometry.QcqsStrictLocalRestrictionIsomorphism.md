## What changed

This is the zero-hole retirement of `Sheaf.AlgebraicGeometry.QcqsStrictLocalRestrictionIsomorphism`.
The Sheaf duplicate is withdrawn; its adopted theorem is already proved in
`WeilConjectures.AlgebraicGeometry.QcqsStrictLocalRestrictionIsomorphism`.
The live Sheaf path remains an empty withdrawal stub after landing, and no public
statement or source-library declaration is changed.

## Proved and sorry left

The assigned retirement begins with zero `sorry`s. No holes were closed (0 of 0),
no holes were added, and no `sorry` remains. The adopted WeilConjectures theorem
`AlgebraicGeometry.Etale.isIso_qcqsStrictLocalRestriction_of_formula` is already
proved and is unchanged by this delivery.

## No longer needed

The withdrawn Sheaf module and its duplicate declaration are no longer needed.
The adopted WeilConjectures module supplies the retained theorem; its dependencies
remain in use by the adopted source theorem and its consumers. No additional
imports or DAG nodes are pruned here.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 brief describes a module containing `sorry`, but this item is a
retirement row in `coord/retire-items.tsv` and therefore has zero holes. The prior
retirement landing already removed the duplicate and retargeted the DAG node to the
adopted WeilConjectures theorem. There is no disputed statement or unfinished proof.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
