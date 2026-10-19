# Worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-nonfree-chain-completions.json`: item split into five direct finite-poset proof steps; no new nodes.
- `citations.json`: empty, because every proof step is an elementary case analysis from the item's explicit chain and product-order definitions.

## Attachments

No Lean declaration attachment found. A search of the source project for the item id, Kerodon tag, and the notions of free/nonfree chains, vertical pairs, and one-vertex insertion found no matching declaration.

## WANTED

- Archival copy of Kerodon Lemma 4.4.4.7 (tag 01DN), whose online proof is the source for this item.

## Existing-node and Mathlib searches

The whole DAG and blueprint were searched for `nonfree`, `chain completions`, `product chain`, `vertical pair`, and `01DN`; no existing node or blueprint node states this classification. Mathlib searches were run with `msearch.py` and read. LeanFinder and LeanSearch returned generic chain, insertion, and path lemmas; Loogle returned `SSet.prodStdSimplex.pairingCore` and related pairing declarations; source grep found `IsIndex`, `IsType₂`, and unique-face APIs in `UnionProd.lean`, `PairingCore.lean`, and `IsUniquelyCodimOneFace.lean`. None classifies the two explicit insertions in this statement, so the item is not a Mathlib leaf.

## What was wrong or changed

The imported item had an empty proof. I retained its statement and dependencies, filled the blueprint proof location, and supplied the complete argument. No statement correction was needed. The proof deliberately keeps the finite-poset case analysis in the item rather than creating child nodes that would merely restate clauses of the item.

## What could not be finished

The Kerodon source is online only in this environment; its archival copy is wanted as recorded above. No Lean code was written and no compiler or Lake tool was run, as required for stage 1.

## Review by Q147

I read the item node, the `sk-prop-sf-cbc` unit record, the `sec-smooth-purity` chapter record, and the existing parent node `lem-cbc-initial-prism-horn-filtration`. I checked the item statement against Kerodon 01DN, especially the final missing-face paragraph (lines 119–129 of the online text), and verified that its hypotheses include all first coordinates, all positive second coordinates, and the absence of a vertical pair. I also checked the edge cases $p=0$, $p=1$, $m=0$, and $n=1$ directly.

For step 1, the first second-coordinate-1 vertex and coordinatewise order force all earlier first coordinates to appear as $(a,0)$, while the no-vertical-pair hypothesis excludes $(p,0)$. Step 2 uses only the definition of a free chain and the fact that the old chain already has all required projections. Step 3 uses the required partner $(b,1)$ to get $b\geq p$, then excludes $b>p$ by incomparability with $(p,1)$. Hence only $(p,0)$ remains. Step 4 uses the required partner $(b,0)$ and the initial segment to get $b<p$, then excludes $b<p-1$ by incomparability with the existing $(b+1,0)$. Only $b=p-1$ survives, and this is impossible for $p=0$. Step 5 verifies directly that the two surviving insertions preserve strictness, surjectivity, uniqueness of the vertical pair, and the claimed zero-based positions. Every step is a direct finite-order argument from the definitions displayed in the item, so no external statement is cited and `citations.json` is correctly empty.

I reviewed the Mathlib search results rather than treating generic `UnionProd` pairing declarations as an exact match. I found no duplicate node, no source declaration, and no hidden hypothesis used by the proof. The only correction to the imported record was replacing its empty proof with these explicit steps and recording the exact blueprint place.

## Not duplicates

No new node was created. The existing parent uses this item for the missing-face classification; it does not replace it. Blueprint searches returned no matching blueprint node.

Finite edge-case enumeration: a direct Python enumeration checked 110 admissible strict chains for $0\leq m\leq3$ and $1\leq n\leq3$. For each it verified the initial segment, all possible one-vertex insertions, uniqueness of the vertical pair, and both zero-based indices. All checks passed.
