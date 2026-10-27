## What changed

Restored Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect from its
quarantine archive and repaired its universe elaboration. In the proved private
helpers perfect_of_iso and perfect_Q_transport, restriction is now explicitly
SheafOfModules.overFunctor.{u}. These are the only two Lean edits. All signatures,
imports, definitions and the public theorem's proof are unchanged.

The existing route is retained: use properSupport_perfect_directImage with O_X[0]
in standard derived models, then transport perfectness to the supplied independent
source, target and open derived models. Stacks Tag 0B91(1) gives precisely this
specialization of 0A1H. The declared dependencies were read and the three msearch
queries found no shorter theorem. The restored file compiled cleanly through
lcompile.py in 47.6 seconds; all lines are at most 100 characters.

Change record: coord/changes/Y3-ProperFlatDerivedDirectImagePerfect-restoration.md.
Its consumer table includes the three quarantined importers as well as the zero-live-
importer result. No consumers need adaptation. The existing DAG proof, attachment
and dependencies remain accurate, so no node fields change.

## Proved and sorry left

This assigned rework has zero existing holes. Holes closed: none (0 of 0).
Holes added or split off: none. Sorries left in the delivered module: none.

AlgebraicGeometry.properFlat_derivedDirectImage_perfect is restored as a complete
proof from the existing declared dependencies, under node
lem-sc-proper-flat-derived-direct-image-perfect-universes. Its five proved private
helpers are iso_Q_transport, perfect_of_iso, perfect_Q_transport,
isFinitePresentation_of_isZero and properFlat_common_perfect. The two restriction
helpers now elaborate at the intended universe. This repairs the recorded defect;
it does not claim new hole-count progress or close holes in imported dependencies.

## No longer needed

None. No imports, nodes, modules, declaration attachments or parent dependencies
are removed. All seven existing proof dependencies remain used by the retained
argument. The quarantine archive is preserved; no deleted.txt is supplied.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief described a sorry-bearing item, but coord/rework.tsv correctly
identifies this as a zero-hole quarantine repair. The archived restriction transports
left the sheaf-of-modules universe implicit, producing the recorded impossible
universe constraint. Explicit .{u} fixes it without changing the theorem or the
mathematics. The DAG route and source citation need no correction; the unit route
is preserved. No new nodes or statement changes were needed.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
