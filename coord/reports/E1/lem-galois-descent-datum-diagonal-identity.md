Files written:

- `dag/nodes/sec-curve-estimates/lem-galois-descent-datum-diagonal-identity.json` (statement, split; no new nodes)

Attachments:

- None for the item. The source checkout has no declaration tagged `(blueprint: lem-galois-descent-datum-diagonal-identity)` and no declaration stating this diagonal identity.

WANTED:

- None. The cited Stacks source is named in the item and its paragraph is the source of the identity.

What was wrong or incomplete:

- The imported item had no proof and only a Mathlib grep search. I supplied the missing two-step argument. The first step constructs the diagonal and the canonical identifications by the fibre-product universal property. The second step uses the descent cocycle on the triple diagonal, then cancels the resulting isomorphism to obtain the identity.

What I could not finish:

- Nothing.

## Review by E1

I read the item, the ancestor `lem-galois-descent`, the existing canonical-pullback split, and the exact statements of `def-pc-fibre-product` and `def-pd-descent-datum`. Step 1 cites only the fibre-product statement, which explicitly gives the universal property and uniqueness needed for the diagonal and its projection identities. Step 2 cites the descent-datum statement, which explicitly supplies both that `varphi` is an isomorphism and the cocycle equation; these are exactly the hypotheses used to derive `e = e \\circ e` and cancel `e`. I checked the edge case `X = Y`, where the diagonal is the identity and the same cancellation forces the datum's restriction to be the identity. I also searched the whole DAG and blueprint for a duplicate diagonal-identity node and searched both Lean source checkouts by item id and descent/diagonal terms; no exact declaration or duplicate was found. The original empty proof and missing proof dependencies were the only defects corrected.
