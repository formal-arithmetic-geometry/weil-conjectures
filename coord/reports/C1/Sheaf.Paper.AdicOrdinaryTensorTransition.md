## What changed

Proved `AlgebraicGeometry.Scheme.adicOrdinaryTensorLevelMap_transition` in
`Sheaf.Paper.AdicOrdinaryTensorTransition`, following the existing node's transpose argument.
The private ordinary coefficient transformation is constructed by the ordinary extension/restriction
adjunction. Its pure-tensor formula identifies its restricted complex map with the prescribed
quotient tensor transition. The localization factorization for composed restriction identifies
both derived transposes; injectivity of the supplied upper adjunction proves the square.

The existing diagram comparison theorem then assembles the same level maps as before. No public
statement, definition, import, or downstream interface changed. The existing public import is
sufficient. Local irreducibility of the localization constructions keeps proof elaboration within
the single-file limit.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.adicOrdinaryTensorLevelMap_transition`
(node `lem-weil-pbc-adic-ordinary-tensor-transition`).

No holes remain in the item. No holes or split statements were added. All private helpers have
complete proofs or explicit constructions. The previously proved
`AlgebraicGeometry.Scheme.adicOrdinaryTensorComplexDiagram_comparison` is retained.

## No longer needed

None. Both existing dependencies, `lem-weil-pbc-adic-ordinary-tensor-levels` and
`lem-weil-pbc-finite-perfect-adic-quotient-diagram`, remain necessary for the explicit level maps
and canonical quotient transitions. No imports, modules, DAG nodes, or unit steps were pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The prescribed argument works for arbitrary ideals and
unbounded complexes, without a K-flatness assumption for the consecutive square. The tensor
calculation uses only the coefficient homomorphism and scalar insertion, so it also covers the
zero ring, the unit ideal, and zero complexes. No new nodes were necessary.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
