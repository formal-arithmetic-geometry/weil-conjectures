## What changed

Completed `AlgebraicGeometry.Etale.etaleSupportNestedSummands` with its signature
unchanged. Added two proved private helpers in the item module: restriction of graph
extension to a disjoint range is zero, and successive graph extensions agree with the
composite graph extension under the canonical test-object identification. The final
argument cancels the injective inclusion, uses its naturality and the three supplied
normalizations, and applies graph-extension naturality and composition.

Updated the existing node's proof, proof dependencies and proof origin to describe this
argument. No definitions, public signatures, public imports, or other modules changed.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Etale.etaleSupportNestedSummands`
(node `lem-sfb-etale-support-nested-summands`). Added 0 holes; 0 holes remain in the
item or elsewhere in this delivery. Both new helpers have complete proofs.

## No longer needed

The proof does not use node `lem-cbc-proper-support-sheaf-composition`, module
`Sheaf.AlgebraicGeometry.ProperSupportSheafComposition`: the section-preserving
composition equation is already a hypothesis, and graph-extension composition follows
from the existing clopen graph API. Removed that proof dependency from the item node.
No Lean imports were removed; the two existing public imports supply its signature and
adjunction/graph APIs. No module is withdrawn or globally claimed to be pruned.

## Where the brief, the DAG or earlier work was wrong

The old plan's appeal to proper-support sheaf composition is unnecessary in this
conditional statement. Its assertion about extending from generators by linearity and
sheafification is also unnecessary: graph/complement extensionality works directly for
the given sheaf. The unit route and all hypotheses are preserved. No statement dispute,
new node, definition repair or forced consumer adaptation was required.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
