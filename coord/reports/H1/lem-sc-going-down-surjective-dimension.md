# Stage-1 report

Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-going-down-surjective-dimension.json`: item split in three proof steps; no new nodes.
- `citations.json`: verbatim quotes for the dimension-definition citations.

Attachments: none.

WANTED: `literature/stacks-project/algebra.tex`, Algebra Lemma Tag 00OH (the local checkout contains only the citation index, so the proof was checked against the imported Tag 00OH description and the node's source metadata).

The item had no sorry-free declaration in `WeilConjectures/`. Its statement is the Tag 00OH going-down plus surjective-spectrum implication. The imported node was unsplit and had no proof; I retained its statement and dependencies.

## Review by H1

I checked the item against the imported Tag 00OH source reference and the exact statement in the node. The proof follows the source's chain argument. Step 1 uses only the existing Krull-dimension definition to choose an arbitrary finite prime chain and then applies the item's explicit spectrum-surjectivity hypothesis to obtain a prime over its last member. Step 2 applies the item's explicit going-down hypothesis repeatedly; the contractions are the prescribed distinct primes, so each lifted inclusion is strict. Step 3 uses the definition node's supremum characterization to transfer every finite chain length from R to S and conclude the dimension inequality. The zero-ring case is stated separately because the definition assigns dimension -infinity when there are no primes. I read the cited definition node and verified that it states both the chain notion and the supremum characterization quoted in `citations.json`. I searched the existing DAG and blueprint for a stronger or duplicate going-down dimension node; none exists. Required Mathlib searches were run: LeanFinder returned only general Krull-dimension/surjective results, Loogle and grep found no direct theorem, and LeanSearch was unavailable.

## Second reading by H1

- Item statement: checked against Stacks Algebra Tag 00OH (Lemma 10.112.1); the going-down specialization, surjective spectrum hypothesis, and Krull-dimension conclusion agree hypothesis by hypothesis.
- Step 1: checked against Tag 00OH's endpoint-prime construction and `def-weil-pbc-krull-dimension-ring`; the chain and zero-ring cases are stated and the surjectivity use is explicit.
- Step 2: checked against Tag 00OH's repeated going-down argument; the contraction equalities force strictness, so the lifted chain has the same length. This is elementary from the item's going-down hypothesis.
- Step 3: checked against the supremum clause of `def-weil-pbc-krull-dimension-ring`; transferring every finite chain length gives the stated inequality, including the zero-ring case.
- New nodes: none; the existing dimension definition is the only dependency, and a DAG/blueprint search found no duplicate helper node. The definition node's statement and its citation quote were checked verbatim.
- Edge cases checked: the zero ring has dimension $-\infty$; for a field, only length-0 chains occur and surjectivity supplies a prime upstairs; lengths $n=0$ and $n=1$ lift exactly as described. No Mathlib declaration matches the full arbitrary going-down plus surjective-spectrum theorem; the recorded LeanFinder, Loogle, grep, and unavailable LeanSearch searches were retained.

Changes made: corrected the split node's `created.item` metadata to this item; no mathematical statement or proof step required repair.
