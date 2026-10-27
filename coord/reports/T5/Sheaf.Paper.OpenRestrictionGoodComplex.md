## What changed

Filled `WeilConjectures.CanonicalOpenRestriction.restriction_preservesGood` in
`Sheaf.Paper.OpenRestrictionGoodComplex`, preserving its signature and public import.
Only private proof helpers and proof imports were added. The item node now records
this argument and its actual dependencies.

The prescribed finite maps equal the constructed slice coefficient isomorphisms by
sheafification uniqueness and `finiteConstants`. Joint monicity of the completed
projections then identifies `o.completedMap` with the constructed completed slice
isomorphism. Continuous, cocontinuous restriction with this invertible ring map
supplies the strong monoidal structure on the specified `o.integral.functor`;
its inverse inherits the inverse monoidal structure.

The existing slice theorem supplies K-flatness. The local equational criterion
proves flatness of every restricted term by transporting covering sieves to the
over site. The exact monoidal equivalence transports the acyclic tensor test and
flatness. The resulting two proofs form the unchanged good-complex predicate for
the prescribed composite restriction. No auxiliary hypotheses on completeness,
boundedness, quasi-compactness, or nonemptiness are introduced.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.CanonicalOpenRestriction.restriction_preservesGood`
(node `lem-sf-open-restriction-good-complex`). No holes added; no holes remain in
this delivery. This is a proof, not a decomposition. Both new private coefficient
normalization helpers are proved.

Validation: the complete item compiled through `lcompile.py` in 17.0 seconds,
with no errors or warnings. All six added proof imports are used; no debug options
or extra axioms were introduced.

## No longer needed

No existing import or module is removed, and no whole module is claimed pruned.
The general derived tensor-pullback dependency
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` is unnecessary for this ordinary
restriction argument: slice K-flat restriction, flatness by the local equational
criterion, and the monoidal equivalence suffice. Its module
`Sheaf.Paper.RingedTopoiDerivedTensorPullback` is not imported by this proof.
The other original proof dependencies remain. The blueprint unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The previous split correctly identified coefficient transport as the missing step,
but the library already contains its ingredients: the constructed finite/completed
slice coefficient comparisons, strong monoidality of cocontinuous ringed restriction,
and the exact monoidal equivalence acyclic tensor test. Their combination closes the
obligation without another split. Importing the coefficient construction with
`import all` allows its proved private comparison helpers to be reused without
changing that module's public interface.

The normalization equations determine the coefficient maps even for the empty open.
The argument uses sheafification uniqueness and limit projections, so it introduces
no choice of an arbitrary coefficient equivalence or monoidal replacement category.

## Second reading by T5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
