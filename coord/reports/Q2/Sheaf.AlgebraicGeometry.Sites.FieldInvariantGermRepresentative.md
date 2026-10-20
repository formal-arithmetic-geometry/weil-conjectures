## What changed

Retired Sheaf.AlgebraicGeometry.Sites.FieldInvariantGermRepresentative as requested
by its current retire queue entry. Its node now points to the existing upstream
theorem, with its exact upstream signature and proof dependencies. Adapted the sole
direct importer, Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants, using a
private upstream import and two private Mathlib imports. The consumer's theorem
signature and public imports are unchanged. Its proof lifts the sheaf by ULift,
transports the stalk action via the comparison equivalence with Equiv.mulAction,
proves compatibility on germs and fixed elements, applies the upstream theorem,
and lowers the resulting section. No upstream files are changed.

Change record: coord/changes/Q2-retire-field-invariant-germ-representative.md.

## Proved and sorry left

Zero holes initially and zero holes left. Closed 0; added 0; split off 0.
The withdrawn exists_fieldSection_of_invariant_germ was already proved. Its
upstream declaration remains unchanged. The adapted fieldSections_stalkInvariants
has a complete proof including the new universe bridge. No decomposition.
The adapted consumer compiles through lcompile.py (4.4 seconds alone; 6.6 in the
set). Its four direct importers also compile unchanged against the adapted module:
BaseFieldCohomologicalDimension, EtaleFieldSectionsInvariants,
FieldEquivariantGermsOnePoint and FieldModuleSectionsInvariants (2.9–6.6 seconds).
A #print axioms check of fieldSections_stalkInvariants reports only propext,
Classical.choice and Quot.sound. No sorryAx is reachable. The consumer signature
was also compared verbatim with the repository source and is unchanged.

## No longer needed

Withdrawn module: Sheaf.AlgebraicGeometry.Sites.FieldInvariantGermRepresentative.
Removed its private import from FieldSectionsStalkInvariants and replaced it with
the upstream twin. The removed module's private imports are superseded by the
upstream proof dependencies. No mathematical node is deleted: the original node,
its finite-Galois construction and descent dependencies remain needed upstream.
No source-library declaration or dependency is removed. Other DAG parents still
use the same node, now attached to the upstream theorem.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a proof item; the current queue assigns retirement
and the source has zero holes. The upstream twin requires Type (max (u+1) v),
whereas the local consumer allows Type (max u v); a literal import substitution
is insufficient. The proved ULift/action-transport bridge preserves that consumer.
The item node's proof now describes the upstream proof rather than U1's inlined
smaller-universe descent. The consumer node records its new ULift bridge.
No statement is disputed and no target or unit route changes.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
