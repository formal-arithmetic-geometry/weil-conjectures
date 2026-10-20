## What changed

Retired the assigned duplicate Sheaf.AlgebraicGeometry.ProEtaleReplete in favor
of WeilConjectures.AlgebraicGeometry.ProEtaleReplete, as explicitly assigned in
coord/retire-items.tsv. Updated the lean attachment and proof description of
det-pe-replete-epimorphism. The upstream theorem has the exact same signature
and a complete proof. No source file changes.

The source proof follows the same local lifting argument: cover by spectra of
w-contractible rings, apply weak contractibility and the sectionwise tower
theorem, then use downward closure of the image sieve and the epi criterion.
Both steps of sk-prop-pe-replete and all its mathematical inputs remain.

There are no active consumers to migrate. All three consumers named in the
retirement inventory are quarantined in coord/rework.tsv. Preserved those
archives and their attachments, and recorded their exact private import
replacement for restoration in the change record. No unrelated cluster is
restored or withdrawn. The result remains available at its adopted source name.

The current source proof, including its exact universe-polymorphic type, compiled
through lcompile.py in 1.5 seconds. Its axioms are only propext, Classical.choice,
and Quot.sound. Project import traversal, stopping at Mathlib leaves, visited
225 project modules, no Sheaf modules, and no missing project modules.
LeanFinder, Loogle, and Mathlib grep ran in the retained delivery;
the project source theorem is the exact match. No new theorem is needed.

Repair of reviewer C-13030's return (delivery head 13030976d9): compared the retained
packet with current sheaf-dag at a151094fa9. The source theorem, live duplicate,
retirement assignment, DAG parents, and three quarantine rows still support the
same retirement. Recompiled the current adopted source proof on the server;
rechecked the live import graph and preserved every quarantine archive. The
reported ScalarExtCupInverseImage path is an unrelated quarantined rework item,
not a dependency of this theorem; this packet does not restore or withdraw it.
The delivery tool rebuilds this packet on freshly fetched sheaf-dag.

Change record: coord/changes/proetale-replete-retirement.md.

## Proved and sorry left

The item already contained zero holes. Closed 0 of 0 sorries; added 0 holes;
split off 0 statements. No sorry remains in the withdrawn module. The retained
AlgebraicGeometry.Scheme.isReplete_proEtale has a complete source proof and
depends only on the three permitted axioms, as checked on the compile server.
This is a retirement, not a newly closed proof hole.

## No longer needed

Withdrawn duplicate module: Sheaf.AlgebraicGeometry.ProEtaleReplete. Its
declaration is retained in WeilConjectures.AlgebraicGeometry.ProEtaleReplete.
The withdrawn file's imports disappear with it; in particular the source proof
does not need Sheaf.AlgebraicGeometry.WContractibleAffineCover or
Sheaf.CategoryTheory.SiteCoveringAxioms. No other module is withdrawn and no
claim is made that those two modules are globally unnecessary.

No mathematical dependency node is removed. The covering input det-pe-wcb-cover
stays on the unit route: the source proof needs its covering clause, obtained
directly by ProEt.exists_isWContractibleRing_cover. Its stronger affine-open
factorization is not needed for this theorem. The definition of repleteness,
affine weak contractibility, sectionwise tower lifting, and local-surjectivity
criterion remain needed. All parent references to det-pe-replete-epimorphism
continue to resolve through its new Lean attachment.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a holed item; the current explicit queue
row instead assigns retirement of this already-proved duplicate. The listed
three consumers are stale as active importer information: they were quarantined
by the upstream sync. Their archive imports must migrate when those independent
rework clusters are restored; the change record lists each one. None currently
imports or compiles the retired module in the library. The fourth DAG parent,
det-pe-continuous-cohomology-etale, also keeps its dependency on the same node;
reattaching that node preserves its planned use of repleteness.

The earlier keep reason cited the duplicate RepleteOnContractible dependency.
That copy was retired by V8, so the source replacement now has no such clash.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
