## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.chartwise_isLocallyQuasiFinite_of_etale`
in `Sheaf.AlgebraicGeometry.EtaleSpaceLocallyQuasiFinite`, preserving its statement,
visibility, imports, and docstring. Introduce an arbitrary representable étale chart,
register the étale composite supplied by the hypothesis, and apply
`Scheme.Hom.isLocallyQuasiFinite_of_unramified`. Mathlib supplies local finite type
and the open immersion diagonal from étaleness.

The proof follows the existing node's three steps and Stacks Tags 03XU, 03WS and
02V5. The existing cross-unit scheme theorem remains the approved tool; no unit
step is bypassed. Searches of the source library, Mathlib, Lean Finder and Loogle
found no shorter matching theorem for the project's finite-type-inclusive
`Scheme.Hom.IsLocallyQuasiFinite` conclusion.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.AlgebraicSpace.chartwise_isLocallyQuasiFinite_of_etale`
(node `lem-a1-etale-space-locally-quasi-finite`). No holes remain in the item.
No holes added; no split-off statements.

Validation: `lcompile.py` compiled the item successfully in 1.4 seconds, with no
Lean errors or warnings.

## No longer needed

None. All original imports and both declared proof dependencies remain necessary
for the statement or proof. No nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

None. The stated dependencies suffice. Mathlib expresses étaleness by affine-local
ring maps, and its existing instances provide the unramifiedness conditions used
in the DAG. No statement, definition, node, or dependency repair was needed.

## Second reading by T5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
