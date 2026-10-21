## What changed

Filled the three proof holes in `Sheaf.SixFunctors.FrobeniusPointTransport`.
Finite sigma is restriction on sections. Naturality of constant sections and the
normalized coefficient isomorphism prove its linearity. The integral construction
checks this identity after every finite quotient projection; joint injectivity
of the projections proves completed-coefficient linearity. Presheaf naturality
proves that both constructions commute with differentials, and termwise
extensionality proves uniqueness.

For integral transport, descend the natural chain-level sigma by the fully
faithful localization functor. Construct the comparison as the adjunction
transpose of the whole-tower reduction unit followed by the inverse-image tower
unit. The existing reduction-counit theorem identifies it on good complexes with
the prescribed Roos comparison. Naturality along a resolution quasi-isomorphism
then gives the required formula for every representative and resolution. One
flat-term K-flat resolution forces uniqueness.

The restriction helper preserves the two successive scalar restrictions used
by inverse image followed by point sections. This avoids kernel conversion to a
single restriction along a composite ring map. Instance removals are scoped to
individual proof declarations; Frobenius constructions are locally irreducible.

Added the private proof import `Sheaf.Paper.IntegralPullbackReductionCounit`. The imported realization and
reduction-counit theorems are used as stated; their pre-existing holes are not
claimed as closed. Realization data is chosen only inside a proof.

Reformulated the two sigma specifications as heterogeneous equality of their
underlying functions. The function types are definitionally the old section
types, so heterogeneous equality and function extensionality give exactly the
original pointwise specifications. The witness types and all public data
constructions retain their signatures and bodies. The two change records are
`coord/changes/Z9-frobenius-point-finite-sigma-specification.md` and
`coord/changes/Z9-frobenius-point-integral-sigma-specification.md`.
The proof-context inventory is recorded in
`coord/changes/Z9-frobenius-point-private-proof-context.md`.

Validation: the complete final file compiled without warnings through the server
wrapper in 56.9 seconds, after removing an unused exploratory import. The finite
sigma prefix also compiled independently in 16.8 seconds. The import cycle
check permits the added proof dependency. No new lemma holes are introduced.

## Proved and sorry left

The original holes are:

- `WeilConjectures.frobeniusPointFiniteSigma_existsUnique`
- `WeilConjectures.frobeniusPointIntegralSigma_existsUnique`
- `WeilConjectures.frobeniusPointTransportIntegral_existsUnique`

All belong to node `def-weil-frobenius-point-transport`. The delivery closes these
three holes and adds none. Retained holes: zero. Split-off statements: zero.
The two prime-unit theorems were already proved and are not counted as progress.

## No longer needed

No original import, node or module is pruned. The exploratory proof import
`Mathlib.CategoryTheory.Adjunction.Whiskering` is unnecessary and was removed. The existing dependency plan is
used. The common-refinement discussion in the old theorem docstring is replaced
by the whole-tower reduction-counit identity and adjunction uniqueness; no new
common-refinement lemmas are needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false. The existing node already records the
localization and adjunction argument. Earlier G9 change records and its reviewed
report describe a completed proof that was returned when a global build failed;
the current source again has the three holes and the pointwise specifications.
This delivery is checked against that current source.

The two sigma specifications have no external direct users according to
`tools/downstream.py --uses` and the declaration-name search. Their local choice
constructions retain the same witness type. The construction treats all integer
degrees and unbounded complexes. The finite case includes exponent one (`n = 0`)
and does not assume the coefficient ring is nonzero.

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
