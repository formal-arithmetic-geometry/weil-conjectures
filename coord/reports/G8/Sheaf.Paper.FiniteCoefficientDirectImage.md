## What changed

Proved the Etale naturality clause and the etale restriction/projection identity in
`Sheaf.Paper.FiniteCoefficientDirectImage`. All existing public signatures and
definitions are unchanged. Two private categorical lemmas implement the shared
naturality argument: insert the naturality defect as an off-diagonal biproduct
entry, then use the existing componentwise uniqueness statement to show that entry
vanishes. This avoids an incorrect faithfulness assumption for derived scalar
restriction. The restriction identity follows from the geometric adjunction
bijection, the mate/counit identity, and counit naturality.

The earlier sandbox's proposed scalar-unit split was withdrawn before delivery.
The original existence/uniqueness hole remains in place; no auxiliary statement
or module from that proposal is delivered.

## Proved and sorry left

Closed two of the eleven original holes:

- `AlgebraicGeometry.Etale.finiteCoefficientDirectImageMap_naturality`.
- `AlgebraicGeometry.Etale.finiteCoefficientDirectImageMap_restriction_projection`.

Added zero holes. Nine original holes remain, all attached to
`lem-coef-finite-direct-image`:

- `AlgebraicGeometry.ProEtale.finiteCoefficientDirectImageMap_naturality`.
- `AlgebraicGeometry.Etale.finiteCoefficientDirectImageMap_existsUnique`.
- `AlgebraicGeometry.ProEtale.finiteCoefficientDirectImageMap_existsUnique`.
- `AlgebraicGeometry.Etale.finiteCoefficientDirectImageMap_comp`.
- `AlgebraicGeometry.Etale.finiteCoefficientDirectImageMap_coefficientChain`.
- `AlgebraicGeometry.ProEtale.finiteCoefficientDirectImageMap_comp`.
- `AlgebraicGeometry.ProEtale.finiteCoefficientDirectImageMap_coefficientChain`.
- `AlgebraicGeometry.Etale.finiteCoefficientDirectImageMap_isIso`.
- `AlgebraicGeometry.ProEtale.finiteCoefficientDirectImageMap_etaleOrigin_isIso`.

## No longer needed

No existing dependency import is removed: the nine unfinished clauses retain
their original proof plans and dependencies. The completed naturality proofs need
only the defining uniqueness theorem, naturality of structural transformations,
additivity, and binary biproducts. The restriction identity uses the published
mate/counit equation directly, without a K-flat-model calculation. No existing DAG
node or library module becomes unnecessary in this partial delivery.

## Where the brief, the DAG or earlier work was wrong

Etale naturality does not require proving the scalar/pullback comparison universal
first. Componentwise uniqueness suffices by the biproduct argument above. In
particular no faithfulness of derived restriction is used. This proves the stated
equalities for arbitrary coefficient maps and complexes, including identity and
nonflat maps, zero complexes, and empty schemes.

The existing ringed-topos tensor/pullback and change-of-rings statements use
SheafOfModules coordinates. Applying them to the original existence theorem still
requires a fixed-ring comparison and normalization bridge; that theorem remains
unchanged rather than exporting an unproved replacement. Geometric and coefficient
composition require the corresponding canonical-compositor coherence computations;
the two isomorphism clauses still require the original projection-formula and
etale/pro-etale transport arguments. Their original source and proof docstrings
are retained.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
