# lem-weil-pbc-nl-presentations-homotopy-equivalent

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-nl-presentations-homotopy-equivalent.json`: split the existing item into five proof steps; no new nodes.

## Attachments

None. The item has no source Lean declaration in its audit.

## Sources and split

Read Stacks `algebra.tex`, Section 00S0 (`section-netherlander`) and Lemma 00S1 (`lemma-NL-homotopy`), especially the proof at lines 35295-35392. The item is the specialization to two presentations of the same $R$-algebra. Step 1 lifts each polynomial generator through the other surjection, using the existing polynomial-ring universal-property node. Step 2 constructs the induced degree-one and degree-zero maps and checks the chain-map square using the existing Kähler-differential definition. Step 3 constructs the difference derivation for two maps of presentations. Step 4 expands the calculation omitted in Stacks: on $f\bmod I^2$ the homotopy gives $(a_1-b_1)(f)$, and on $s\otimes\mathrm dp$ its differential gives $(a_0-b_0)(s\otimes\mathrm dp)$. Step 5 uses composition on these generators to apply that homotopy to the identity and the two composites.

All objects and hypotheses in the statement agree with 00S1 under $R'=R$, $S'=S$, and the identity base maps. In particular neither a finite variable set nor finite presentation is used. The empty variable set and the identity presentation $P=S=R$ cause no exception: lifts and derivations exist, and the displayed equations reduce to zero maps or identities. The source's omitted calculation is written explicitly in step 4. Existing cited nodes `def-weil-pbc-mv-polynomial-ring` and `def-weil-pbc-kahler-differentials` publicly state the universal properties used; no new node or off-route tool is needed. I also read the current Mathlib and a local v4.33.1 source of `Mathlib/RingTheory/Extension/Cotangent/Basic.lean`; its homotopy declarations match the item's recorded candidates, but several declarations plus a composition argument are needed for the full item, so it remains a split rather than a Mathlib leaf.

## WANTED

None.

## Corrections and checks

The imported item had no proof. I retained its statement and wrote the source's proof, including the omitted homotopy calculation. `python3 tools/review_split.py lem-weil-pbc-nl-presentations-homotopy-equivalent` passes. `python3 tools/check_dag.py --cycles` reports zero cycles and seven unrelated reachability warnings in the existing tree; none names this item. No Lean was written or built.

## Unfinished

None for this one-level split.

## Review by F1

I read Stacks Algebra 00S1 (lemma-NL-homotopy), including its omitted homotopy calculation, and the cited public statements of def-weil-pbc-mv-polynomial-ring and def-weil-pbc-kahler-differentials. The item is exactly the same-base specialization of 00S1 to two arbitrary polynomial presentations. Its statement adds neither finite presentation nor a restriction on the variable sets. There are no new nodes, so the new-node checks B1-B8 and duplicate-node check C5 are vacuous.

Step 1 uses the polynomial universal property to lift each variable and prove agreement with the surjection. Step 2 constructs both term maps and checks the differential square by the derivation relation, which the cited Kähler definition states. Step 3 uses that same universal property for the difference derivation into I'/I'^2. Step 4 calculates both homotopy equations on f mod I^2 and s tensor dp; this fills the calculation Stacks omits without appealing to an uncited theorem. Step 5 calculates composition termwise and applies the homotopy to each composite, leaving the earlier chain-map identities intact (C1-C4, D1-D5).

I checked an empty variable set, an identity presentation, zero ideals and arbitrary infinite sets of generators; the maps and calculations still make sense (E1-E6). The proof does not assert the item's entire conclusion in a helper. The worker supplied no off-route tool or source correction to send back. review_split passes, and check_dag finds no new cycle; its seven reachability warnings concern unrelated nodes (A, F).
