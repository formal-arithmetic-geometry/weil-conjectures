## What changed

Implemented `Sheaf.Paper.RingIsoQuotientSystemTransport` directly on the recorded
strict semilinear systems. Named inverse scalar restriction gives the ordinary additive
exact equivalence, and exact localization gives the derived equivalence with its
specified factorization. Normalized inverse mates give all scalar comparisons,
pure-tensor formulas, Hom equations, units and associators. The strict reduction
is constructed from the supplied scalar models; a resolving-class universal pair
and comparison on flat-term K-flat resolutions give its system-valued derived
reduction and evaluation formulas. Uniqueness of universal right Kan extensions
gives the transported comparison on every complex.
The unchanged strict transition squares descend and transpose to the required
adjoint transition law and invertibility equivalence.

The three public normalization records are instantiated from generic dependent
records with named normalization predicates. Every original data field and clause
is retained; this avoids expensive concrete recursor elaboration. The change is
recorded in `coord/changes/ring-iso-quotient-system-normalization-records.md`.
The consumer search finds zero downstream Lean modules. The new public normalization
predicates and transport instance APIs are attached to the existing node. All
construction and proof helpers are private and proved. No new mathematical assumption
is introduced, and no other Lean module is adapted.

## Proved and sorry left

Closed the original hole in
`SheafOfModules.QuotientIsoTransport.ringIsoQuotientSystemTransport`
(blueprint: `lem-pur-ring-iso-quotient-system-transport`).
Original holes: 1. Closed: 1. Added: 0. Split off: 0. Remaining in the item: 0.
Every private helper has a complete proof; the delivery adds no `sorry` elsewhere.
The complete module compiled successfully in 53.2 seconds through `lcompile.py`.

## No longer needed

Removed the direct imports of `Sheaf.CategoryTheory.SystemRingedSequenceSite`,
`Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction`,
`Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`, and
`Sheaf.Algebra.Homology.ChangeOfRingsKFlat`.

The direct proof no longer uses `lem-pur-system-ringed-sequence-site`:
strict transport and its inverse are constructed levelwise.
It also does not use `lem-pur-ring-iso-derived-transport` or its module
`Sheaf.Algebra.Homology.NormalizedRingIsoDerivedTransport`: the ordinary
restriction equivalence is constructed directly and then localized, and
the two derived reduction pairs are compared using their universal properties.
The proof also avoids `lem-sfb-ring-isomorphism-tensor-transport` and its module
`Sheaf.Algebra.Homology.RingIsomorphismTensorTransport`; equivalences preserve the
right Kan universal property, so no separate flatness transport is required.
The generic comparison-from-resolutions theorem is reused from
`Sheaf.CategoryTheory.DerivedCategory.ConstantTowerNormalization`; that module
and `lem-cbc-derived-constant-tower-normalization` remain needed. The proof
uses the existing cochain Kan helpers in
`Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares`.
The two coefficient-adjunction nodes
`lem-pur-sheaf-ring-coefficient-ordinary-adjunction` and
`lem-pur-sheaf-ring-derived-coefficient-adjunction` are not separately invoked:
the statement already supplies normalized `SystemScalarModel` adjunctions.
`lem-pur-kflat-change-of-rings` is unnecessary for scalar associators, because
normalized adjoint uniqueness and the restriction compositor prove their
compatibility. These four obsolete top-level tool-use entries are removed in
the node copy. No source-library declaration or module is withdrawn. These are
changes to this node's direct proof dependencies; dependencies still used by
other library declarations remain in the library.

## Where the brief, the DAG or earlier work was wrong

The statement is retained. The DAG's eight-step route is longer than necessary:
its sequence-site equivalence and iterated K-flat tensor calculations can be
replaced by a direct strict equivalence and normalized adjunction comparison.
The system-valued derived reduction is still necessary and is constructed,
not inferred merely from a family of evaluated derived objects. The current
`QuotientSystemFlatModels` interface uses a larger coefficient universe and
does not directly replace this construction with independent site universes.

The public normalization records retain all of their original clauses through
generic packaging and named predicates. The
private implementation uses proved comparison APIs to control unfolding of
localization and scalar transport during elaboration. No target signature or
source-library declaration is changed.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
