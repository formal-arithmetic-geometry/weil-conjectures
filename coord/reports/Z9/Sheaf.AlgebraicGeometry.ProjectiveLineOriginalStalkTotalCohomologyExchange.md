## What changed

Complete the explicit retirement of
Sheaf.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange in
coord/retire-items.tsv. Its smallModel theorem is already proved with zero holes.
Withdraw the wrapper and migrate its sole consumer,
Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison, to the
adopted canonical-model theorem. The consumer now constructs the two canonical
presentations, proves the structural-map identities, transports the three
structural/residue equations, and rewrites the theorem's cohomology conclusion.
Its entire public signature, all public imports and final conjugation proof stay
unchanged. No source-library file changes.

Reattach lem-weil-pbc-p1-original-stalk-total-cohomology-exchange to the existing
adopted theorem, with its verbatim signature and actual proof dependencies.
Update the parent proof to record the small/full-model transport. No mathematical
statement or target changes. The change record is
coord/changes/Z9-retire-projective-line-original-stalk-total-cohomology.md.

## Proved and sorry left

Holes closed: 0 of 0. Holes added: 0. Split off: 0.
This is the listed retirement repair, not a new proof or decomposition.
AlgebraicGeometry.Etale.projectiveLine_strictLocal_stalkExchangeComparison_smallModel
remains proved with precisely its original statement. No sorry remains in any
delivered Lean file. The adopted
AlgebraicGeometry.Etale.projectiveLine_originalStalk_totalCohomologyExchange and its
full proof are preserved verbatim. No claim is made about unverified transitive
axiom closure; the delivery tool runs its declaration probe.

## No longer needed

Withdraw Sheaf.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange
and its theorem
AlgebraicGeometry.Etale.projectiveLine_originalStalk_totalCohomologyExchange_smallModel.
Remove its private import from the sole caller. Pruned: one wrapper module.
No mathematical node is pruned: the original-stalk total-cohomology node is attached
to the adopted canonical theorem and remains a dependency of the parent.

The module/abelian stalk comparison, abelian original-stalk comparison, coefficient
pullback-forget isomorphism and cohomology naturality are still used by the adopted
proof; none is declared unnecessary. The small/full structural identity is moved
to the parent proof. Only that identity is used from
Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison; its closed-fibre
consequence is not applied. No unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes an open proof obligation; the current item has zero
holes and the retirement table explicitly assigns removal of this wrapper.
The canonical theorem takes strictLocalization presentations whereas this wrapper
and its caller take strictHenselizationScheme presentations. A name-only migration
would be ill-typed. The packet retains the full presentation transport in the
caller and updates both node proof plans to agree with that placement.

The current source includes D2's restoration, A3's smallModel rename and M9's
abelian-wrapper retirement. Those changes are preserved. The only current Lean
caller and the only DAG parent have both been accounted for; the module is present
in lean and is not an already-absent quarantine path. Searches by msearch.py in
LeanFinder, Loogle and grep gave no Mathlib replacement; source search found the
adopted canonical theorem. The current sk-thm-p1 blueprint and all realized unit
steps retain their proper-base-change route.

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
