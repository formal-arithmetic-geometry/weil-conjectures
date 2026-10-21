## What changed

Completed `CategoryTheory.diagramRingRestrictionPushforward` in
`Sheaf.CategoryTheory.DiagramRingRestrictionPushforward`, preserving its signature and
all existing public declarations and imports. Added proved private helpers for the
ordinary coefficient comparison, exactness of restriction, the commutative-ring
presentation, the derived universal-property comparison, and restriction acyclicity.

The ordinary comparison is the composite of the supplied underlying identifications.
Transposing generalized elements through the common geometric adjunction proves its
linearity from the structural ring square. Faithfulness proves its uniqueness.

Exact scalar restriction supplies the actual termwise derived functors and their
factorization isomorphisms. Applied to source restriction followed by `fS`, the
existing ringed-topos composition theorem proves that the second derived unit is
invertible on restricted K-injectives. The two normalized composite units then both
satisfy the right-derived universal property. Their unique comparison gives `kappa`
and exactly the required equation on every complex. No claim that scalar restriction
preserves K-injectives is used.

Added proof imports for the identity-site restriction morphism, the source-library
Grothendieck and K-injective APIs, and Cartesian products of sheaves. Updated the
existing node's proof, proof dependencies and proof origin to record this argument.
There are no public interface changes and no consumer adaptations. The original
`hBY` and `hStructuralS` hypotheses remain in the signature; the proof does not need
them. Standard sheaf instances are cached privately to avoid repeated searches.
The complete proof compiled on the server in 32.1 seconds; profiling options were
then removed for the final delivery checks.

The first server preflight requested a record for the new section/local-instance
commands. `coord/changes/diagram-ring-restriction-proof-scope.md` documents their
private scope, the identical old/new public signature, and the consumer check
(zero current Lean importers). No existing public instance or attribute changes.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.diagramRingRestrictionPushforward`
(`lem-pur-diagram-ring-restriction-pushforward`).

Original holes: 1. Holes closed: 1. Holes added: 0. Holes left: 0.
Every new private helper is proved; there are no split-off statements or new modules.

## No longer needed

Removed the proof import `Sheaf.CategoryTheory.DiagramSiteRealization` and the proof
edge to `lem-weil-pbc-diagram-site-realization`. The specified concrete diagram
site, ring and sheaf equivalence already enter through the existing public imports;
the existential realization theorem and module-diagram equivalence are not invoked.
The realization remains a statement dependency, and its module is not withdrawn.

One invocation of the composition theorem, for source restriction followed by `fS`,
suffices: exact target restriction and the K-injective universal property provide
the other factorization directly. No auxiliary composition/coherence statement is
needed. No source-library declaration or module is removed.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The original plan's two composition applications
can be reduced to one, followed by the normalized universal property. The node now
records that more direct argument. The ordinary comparison also works for arbitrary
rings; commutativity is used only to apply the existing derived-composition API.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
