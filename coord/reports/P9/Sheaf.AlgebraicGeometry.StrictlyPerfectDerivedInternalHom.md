## What changed

Completed the listed retirement of
Sheaf.AlgebraicGeometry.StrictlyPerfectDerivedInternalHom in favour of
WeilConjectures.AlgebraicGeometry.StrictlyPerfectDerivedInternalHom. The upstream
public theorem is identical apart from its hypothesis binder name. Withdrew the
Sheaf module through deleted.txt and repointed the existing DAG node
lem-pc-rhom-strict-perfect-hom to the upstream theorem.

The only current importer is
Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomMapQuasiIso. It uses only the
generic retract lemma that the Sheaf copy exposed. Replaced its proof import with
Mathlib.CategoryTheory.MorphismProperty.Retract, moved that complete generic proof
into a private helper in the consumer, and changed the single call accordingly.
The consumer is unclaimed. Its public interface is unchanged; no source-library
module is edited.

Change record: coord/changes/P9-retire-strictly-perfect-derived-internal-hom.md.

Validation: original item and adapted consumer compile separately through
lcompile.py. The original strictly-perfect theorem signature is also checked by a
scratch Lean example applying the upstream declaration. All direct imports and
public-name uses were searched in lean/ and quarantine/. The only DAG parent,
lem-pc-finite-free-derived-dual-model, already uses the upstream theorem; its
proof dependencies remain intact. The unit's route is unchanged.

## Proved and sorry left

This is a zero-hole retirement: 0 of 0 original sorries closed, 0 sorries added,
0 split off, and no sorry remains in any delivered Lean file. No new mathematical
proof is claimed. The private shortExact_of_retract helper retains its complete
existing proof. The upstream
AlgebraicGeometry.Scheme.isIso_homComplex_resolution_of_isStrictlyPerfect remains
proved by the existing bounded exact-term Hom and K-injective comparison argument.

## No longer needed

Withdrawn module: Sheaf.AlgebraicGeometry.StrictlyPerfectDerivedInternalHom.
Its sole current consumer no longer imports it. The duplicate theorem, private
finite-free-retract calculation, and their local proof-import list disappear with
the module. The generic retract calculation survives privately in its consumer.

No mathematical DAG node or proof dependency is pruned: the existing node is
attached to the upstream theorem, which retains the original dependencies and
proof. In particular, finite-free internal Hom exactness, the bounded exact-term
Hom quasi-isomorphism theorem, Hom complexes, localization, and derived Hom are
still needed by the upstream argument.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 brief describes a module to prove, but the current item is a
listed retirement with zero textual holes. The retirement inventory's DIFFERENT
classification reflects the public generic retract helper and the spelling `_hP`
versus `hP`; it does not indicate a changed mathematical theorem. The inventory's
other two consumers already import the upstream twin. The helper's earlier
visibility change was needed at the time; its one user can now own it privately,
which allows retirement without changing any upstream declaration.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
