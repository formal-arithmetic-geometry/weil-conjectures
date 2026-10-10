# lem-sc-rational-section-order

## Files written

- `dag/nodes/sec-picard-framework/lem-sc-rational-section-order.json`: split the two-clause statement in three proof steps; no new nodes and no new Mathlib leaves.

## Attachments

None. A search of `WeilConjectures/` and `Comparator/` by item id and by rational-section/order terminology found no declaration stating this item.

## WANTED

None. The Stacks source is listed as obtained in `literature/LIST.md`; this clone lacks the ignored `literature/stacks-project/` checkout, so I read the official Stacks pages for Section 02SE, Definition 02SF, Lemma 02SG, and Lemma 0BE1 directly. The blueprint source likewise is absent from this clone; the imported parent node preserves the relevant proof sentence.

## Findings

The item's statement agrees with the cited Stacks result after specializing to a smooth connected curve. The imported source compresses the finiteness argument: 02SG gives local finiteness on a locally Noetherian scheme, while finiteness here also uses that a finite-type curve has a finite zero-dimensional closed complement. No statement correction was needed. `lem-sc-smooth-connected-curve-local-rings` is a generic tool in unit `sk-def-pic` outside this item's unit route; the statement already depends on it and records the needed DVR valuation facts, so the proof invokes those standing facts directly. `lem-sc-integral-function-field-affine-fraction` is a Mathlib leaf and `lem-sc-dim0-finite` is Lean-closed in the cited unit `sk-thm-picard-duality`.

## Unfinished

None for this one-level split. The existing dependency nodes continue independently in the DAG.

## Review by F1

I checked the item against the official Stacks Section 02SE and Lemma 02SG, and checked its blueprint place against the sentence about `D=div(s)` retained in `lem-sc-line-bundle-rational-section`. Step 1 uses the exact rank-one stalk and generic-basis assertion of `lem-sc-invertible-module-generic-stalk` and the normalized DVR valuation recorded in the item's statement: two generators differ by a local unit, whose valuation is zero. This proves equality of the two orders, rather than just asserting independence.

Step 2 expands the first sentence of the proof of 02SG. `def-sc-invertible-module` supplies a trivialization near the generic point; the generic-stalk node makes its generator a basis; the affine fraction-field node writes the coefficient of `s` as `a/b`. On `D(ab)` both are units, so `s` generates there. The open is nonempty since `a,b` are nonzero in the domain of a nonempty affine open of the integral curve. Step 3 uses the valuation facts in the item's statement, the dimension-one and finite-type hypotheses in `def-sc-curves`, and the exact finite zero-dimensional closed-subset statement of `lem-sc-dim0-finite`; thus it converts the locally finite conclusion of 02SG to the finite conclusion of this item. I checked the clauses for the trivial line bundle on an affine curve (`s=f`), for `s=1` (empty support), and for a nontrivial invertible module (the trivializing open still exists). I also checked the cited nodes' actual statements, searched the DAG and whole imported blueprint for a duplicate, and found no new fact requiring a node. The correction made during review was to spell out the `D(ab)` construction and the finiteness argument that the Stacks proof leaves compressed. After preflight identified the external unit route, I removed repeated proof citations of `lem-sc-smooth-connected-curve-local-rings` and used the facts already included in the item's statement; I wrote out the dimension argument for `Z`.
