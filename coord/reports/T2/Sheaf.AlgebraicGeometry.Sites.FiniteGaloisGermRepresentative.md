## What changed

Retired Sheaf.AlgebraicGeometry.Sites.FiniteGaloisGermRepresentative in favor of
WeilConjectures.AlgebraicGeometry.Sites.FiniteGaloisGermRepresentative. Repointed
lem-exc-field-invariant-germ-representative-construction to the unchanged upstream
declaration. The sole direct importer,
Sheaf.AlgebraicGeometry.Sites.FieldInvariantGermRepresentative, now applies the
upstream theorem to an ULift of the sheaf and transports the section and its germ
back using Mathlib's Point.presheafFiberCompIso compatibility theorem. Its signature
and public imports are unchanged. Its node records this coefficient adaptation.

Change record: coord/changes/T2-retire-finite-galois-germ-representative.md.

## Proved and sorry left

This is a retirement, with zero holes in the item at the start. Holes closed: none
(0 of 0). Holes added: none. Holes left in the delivered consumer: none. The existing
exists_fieldSection_of_invariant_germ proof remains complete after replacing its
finite-Galois-representative step with the upstream theorem and ULift transport.
No statements are split off. The adapted consumer compiles cleanly via lcompile.py. Its sole direct importer,
Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants, also compiles unchanged
against the adapted consumer. The delivery probe checks its axioms as part of the
dry run.

## No longer needed

Withdrawn module: Sheaf.AlgebraicGeometry.Sites.FiniteGaloisGermRepresentative.
Its consumer no longer imports it. The retired module's two private helper proofs,
factor_separable_embedding and pointed_field_neighbourhood, are no longer duplicated
locally; the upstream proof remains intact. Its five public imports and two private
imports disappear with the withdrawn copy, but are still used by the unchanged
upstream module. No mathematical dependency node is pruned: the construction node
is now attached to the upstream theorem, which follows the same residue-field and
normal-closure argument. No other module is claimed to leave the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The generic worker brief describes a proof obligation that was split off twice.
The current item is already proved and is listed as a retirement in coord/queue.tsv
and coord/retire-items.tsv. The retirement inventory says the statements are the
same, but the coefficient universes differ: the local theorem uses max u v and the
upstream theorem uses max (u+1) v. A bare import substitution would lose the
smaller-universe application introduced by D5. The ULift adapter preserves that
application without editing any upstream declaration or changing any target.
The item node's mathematical route and the unit's route are retained.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
