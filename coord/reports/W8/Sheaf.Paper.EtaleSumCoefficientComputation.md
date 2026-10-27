## What changed

Filled `AlgebraicGeometry.Etale.etaleSumCoefficientComputation` in
`Sheaf.Paper.EtaleSumCoefficientComputation`, keeping every existing statement.
The two complex-map definitions drop identity comparison factors; their canonical
transformations and sources and targets stay the same.
The proof applies the bounded compactification models over both coefficient rings,
uses the acyclic-flat proper model and the existing normalized open model equation,
and transports the ordinary graph/scalar calculation degreewise and through localization.
The definition change is recorded in
`coord/changes/W8-etale-sum-complex-identity-factors.md`.
Private helpers compare the two adjunction presentations and establish independent-coefficient
K-flatness from boundedness and termwise flatness. A private generic chain-map
construction makes the successive complex functors explicit in the diagram.
All additional imports are proof imports.

Validation: the complete proof compiled without warnings in 36.3 seconds.
The final conversion uses a proved generic equality of the two chain-map wrappers
to keep the large comparison definitions abstract. Both old/new public-definition
equality checks also compiled.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Etale.etaleSumCoefficientComputation`
(node `lem-sp-etale-sum-coefficient-computation`). One hole closed; zero holes added;
zero holes remain in the delivery. No statements are split off.
The original theorem signature is byte-identical to the shared source.

## No longer needed

None. The proof uses all five original proof dependencies, together with existing
independent-coefficient flatness and open-normalization lemmas recorded in the node.
No public imports, nodes, or modules are withdrawn. No adopted source-library declaration is changed.

## Where the brief, the DAG or earlier work was wrong

The K-flatness supplied by the bounded-model theorem is categorical, whereas the item
uses the independent-coefficient realization. The private bounded-flat helper bridges
these interfaces via the existing constant-module equivalence and site-flatness theorem.
The two sum/scalar isomorphisms use different presentations of the same restriction
adjunction; their agreement is proved from the canonical units, without choosing a map.

## Second reading by W8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
