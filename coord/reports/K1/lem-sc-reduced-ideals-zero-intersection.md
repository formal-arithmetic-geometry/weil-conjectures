# lem-sc-reduced-ideals-zero-intersection

## Files written

- `dag/nodes/sec-curve-estimates/lem-sc-reduced-ideals-zero-intersection.json`: split the item in three steps; no new nodes or Mathlib leaves.
- `citations.json`: verbatim statements used in steps 1 and 2.

## Attachments

None. No matching Lean declaration was found in the read-only source.

## Sources and issues

I read Stacks Varieties Remark 09NW (remark-conductor) and Algebra Lemma 00E0 (lemma-Zariski-topology), parts (7) and (9), at their official tag pages. The local `literature/stacks-project/` source tree is absent, so I checked the exact tag labels and text online. The item's statement agrees with 09NW: reduced commutative ring, two ideals whose zero loci cover the spectrum, zero intersection, and the quotient-map isomorphism. No new statement was needed. The original item had no proof; its Mathlib searches already recorded the absence of an exact declaration. The blueprint search found no matching imported node, and the two needed facts already had DAG nodes.

WANTED: `literature/stacks-project/varieties.tex`, Varieties Remark 09NW (varieties-remark-conductor), for lem-sc-reduced-ideals-zero-intersection; source read at https://stacks.math.columbia.edu/tag/09NW.

## What remains

Nothing in the split. The local literature source tree should be restored by the maintainer; the official tag pages supplied the source text for this delivery.

## Review by K1

I compared the item with Remark 09NW and checked Algebra Lemma 00E0 (7), (9) for its two non-elementary inputs. Step 1 cites `lem-weil-pbc-zero-locus-ideal-intersection`: its statement says verbatim that the zero locus of the intersection is the union of the two zero loci, so the covering hypothesis gives all primes. Step 2 cites `lem-weil-pbc-zero-locus-eq-iff-radical-eq`: its statement says the radical of an ideal is the intersection of prime ideals containing it. Applied to the zero ideal, it makes every element of the intersection nilpotent; reducedness, explicitly in the item, makes it zero. Step 3 uses the quotient map itself: its image is `IB`, and its kernel on `I` is exactly `I ∩ J`, so the isomorphism is elementary. The two cited nodes are Mathlib leaves and are used only for facts their statements actually contain. I checked the special cases `I=0`, `J=0`, `A=0`, and `A=k[x,y]/(xy)` with `I=(x)`, `J=(y)`; each gives zero intersection, including the empty spectrum case. The removed gap was the absent proof, not a false source statement. No new node required testing or source comparison.
