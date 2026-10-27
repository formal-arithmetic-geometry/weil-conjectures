## What changed

Completed the Lean proof of
`AlgebraicGeometry.Scheme.rationalRealizationOrdinaryLocalization`, with its original
signature and both public imports preserved. Added a proved private equivalence of
module sheaves by restriction along an inverse ring-sheaf isomorphism, plus proved
private helpers for functor identification and the adjunction comparison. Keeping
these helpers general in the coefficient rings avoids expensive unfolding of
completed scalar-extension witnesses inside the realization theorem. The proof
checks semilinearity on sections using the normalized scalar formula. The ordinary
tensor comparison is obtained from the scalar adjunction, the explicit object/map
identifications of F, and uniqueness of left adjoints.

Split the coefficient-ring part into the new module
`Sheaf.Paper.RationalRealizationCoefficientLocalization`. Its assertion concerns
only a ring-sheaf isomorphism, its coefficient-unit square and its inverse action
on constant scalars. It has no module functor, no module equivalence and no tensor
comparison. It is strictly the first part of the original argument, rather than
another assertion of the original module-category conclusion.

The item was checked against the current server queue, rework, build-error and
claim records. The queue assigns a proof with one hole. The historical bad-import
failure does not reproduce against the current published dependencies. No existing
dependency module, declaration signature, instance or attribute is changed.

Validation: both delivered modules compile through `lcompile.py` in import order;
the coefficient module took 7.8 seconds and the final item took 18.9 seconds, with
no errors or warnings. The theorem signature was also compared with the original.

## Proved and sorry left

Closed the one hole in
`AlgebraicGeometry.Scheme.rationalRealizationOrdinaryLocalization`
(node `lem-per-rational-realization-ordinary-localization`). Its proof is complete
from the named coefficient-ring lemma and the existing ordinary scalar adjunctions.

Added one hole:
`AlgebraicGeometry.Scheme.rationalRealizationCoefficientLocalization`
(node `lem-per-rational-realization-coefficient-localization`). This is the only
remaining sorry in the delivered files. Its docstring and node give the quotient,
localization and constant-scalar argument. No sorry is inside a definition or a
private declaration.

This is a decomposition: one upper hole closed and one strictly smaller ring-level
hole added, for net zero holes. It is not a complete proof free of sorry dependencies.

## No longer needed

The ordinary comparison no longer needs the planned generic derived-transport
node `lem-pur-ring-iso-derived-transport` or its module
`Sheaf.Algebra.Homology.NormalizedRingIsoDerivedTransport`. The ordinary equivalence
uses Mathlib's pushforward equivalence for the identity site; the tensor comparison
uses `pbcScalarAdjunction`, `pbcRestrictComp` and `Adjunction.leftAdjointUniq`.
These modules may still be needed elsewhere; none is withdrawn.

No existing import was removed: both original public imports are used in the
unchanged signature and canonical linear action. The uniformizer-localization
node `lem-weil-l-adic-integers-localization-uniformizer` remains needed for the new
coefficient-ring step; it has moved below that step and is not pruned. The normalized
realization node remains a statement dependency and a dependency of that ring step.

## Where the brief, the DAG or earlier work was wrong

The original DAG's ordinary-equivalence step suggested the large derived tensor
transport package. The ordinary scalar adjunction and uniqueness of its left
adjoint suffice. No statement was disputed or weakened, and the unit route stays.
The source paper's Lemma 6.8.12 is the direct-sum Hom lemma, not the ring coefficient
comparison itself; Lemma 6.8.2 gives the coefficient completion/localization used
implicitly in Proposition 6.8.14(2).

The new statement was checked on the empty scheme (all section rings may be zero),
locally varying denominators, and arbitrary normalized realization data. It makes
no pointwise global-denominator assumption. The module argument applies to zero,
torsion and arbitrary module sheaves, since it uses adjunctions and sectionwise
scalar identities without any finiteness condition on modules.

## New nodes

`lem-per-rational-realization-coefficient-localization`: the completed coefficient
localization isomorphism with its unit and inverse constant-scalar normalizations.
The source, proof steps and exact Lean signature are in its new node and module.
LeanFinder, Loogle, LeanSearch and source grep were run through msearch.py. The
whole-blueprint search found no duplicate coefficient-localization statement.
No change record is needed: existing interfaces and all other modules are untouched.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.RationalRealizationCoefficientLocalization": "ad82fd221ef5d35544872806c6f259a27fbec86e", "Sheaf.Paper.RationalRealizationOrdinaryLocalization": "dba83abb4a24dd05a130a6b89158b533ce26fa62"}, "results": {"Sheaf.Paper.RationalRealizationHomTransport": {"hash": "3243f1b3da9d3f2c3da42d4129bc1cf6d4ce877c", "status": "OK"}}, "seconds": 87, "time": "2026-10-28T00:51:59+0800", "transitive": 0, "version": 1}
```

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
