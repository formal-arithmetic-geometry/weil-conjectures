## What changed

Restored lean/Sheaf/Paper/RealizationScalarFunctor.lean from its rework quarantine
archive and repaired the missing target triangulation. The proved instance
WeilConjectures.realizationScalarTargetTriangulated applies continuous-field local
finite freeness in Type u, the existing constructible Serre argument, and the bounded
homology triangulated criterion. It supplies the inherited shift and pretriangulation
needed to state the existing record. Source comparison confirms that the record,
existence theorem, original public imports, DAG statement and unit route are unchanged.

Changed the proof import of CondensedConstructibleSerre to import all to access its
proved generic private helper, and added the private IsoClosed import for transport
across isomorphisms. Added the instance to the item's existing Lean attachment and
recorded its three actual dependencies in the DAG proof. Change record:
coord/changes/D3-realization-scalar-target-triangulation.md.

Validation: a scratch copy compiles with the upstream triangulation instance disabled.
This verifies the new proof independently of the stale unrestricted instance.
A second lcompile batch compiled the restored item and all ten unchanged quarantined
consumers in import order. All eleven compiled without warnings or source adaptations;
only the item is included in this delivery. The consumer inventory is in the change record.

## Proved and sorry left

This is the listed rework repair, not a proof of the scalar-functor existence theorem.
Proved WeilConjectures.realizationScalarTargetTriangulated with no new sorry.
Closed 0 of the archive's 1 sorry; added 0 holes and split off 0 statements.
The instance is proved from existing library declarations; its transitive axiom output
includes the existing dependency sorryAx, so this packet makes no claim of an
axiom-free scalar-realization theorem.
The sole remaining sorry is WeilConjectures.realization_scalar_functor
(blueprint: lem-weil-pbc-realization-scalar-functor), unchanged from quarantine.

## No longer needed

No modules, nodes or imports pruned. The item and its unfinished parents remain needed.
The original scalar-extension proof route and dependencies are preserved. The repair
no longer relies on the upstream unrestricted triangulation instance, which the sync
replaced by a coefficient-class instance unsuitable for E : Type u.

## Where the brief, the DAG or earlier work was wrong

The item is absent from lean because of quarantine, not because it was withdrawn.
Restoration preserves its Lean attachment and mathematical statement.
The post-sync source's finiteness-coefficient constructor for continuous fields accepts
Type 0 coefficients, whereas this item uses E in the scheme universe. The generic
local-freeness and Serre arguments already support that universe and give the required
triangulation. The initial published-build compile exposed the previous unrestricted
instance; the refreshed build subsequently exposed the restricted signature. Validation therefore
also disables the upstream instance in a scratch copy, rather than relying on it.
The two newer DAG dependencies continuous-scalar-derived-encoding and
integral-scalar-constructible-image currently have no Lean attachments; this packet
preserves them and repairs the assigned interface rather than claiming their proof.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
