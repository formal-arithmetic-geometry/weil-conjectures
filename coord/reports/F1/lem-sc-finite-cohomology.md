# Stage 1 report: lem-sc-finite-cohomology

## Files written

- `dag/nodes/sec-picard-framework/lem-sc-finite-cohomology.json`: statement node, split.
- `citations.json`: empty citation list because all proof steps are elementary from the witness definition.

## Attachments

No Lean declaration attaches to this item. A search of `WeilConjectures/` found no declaration tagged `lem-sc-finite-cohomology` and no sorry-free declaration with the same statement.

## WANTED

None.

## Not duplicates

No new nodes remain after review. The finite-free truncation argument is an elementary step of this item, not a separate node restating Tag 064S.

## Review by F1

I read the item source, More on Algebra Tag 064S (`literature/stacks-project/more-algebra.tex`), and checked the statement against the imported node. The witness step uses only the definition of m-pseudo-coherence and the stated vanishing hypothesis: the isomorphisms above m transfer vanishing from K to E. Step 2 cites the new bounded finite-free top-cohomology node; its statement exactly supplies finite generation of H^m(E), including the same ring, degree, boundedness, and vanishing hypotheses. Step 3 uses the surjection in the definition and the elementary fact that quotients of finite type modules are finite type. The new node's two steps follow the Tag 064S proof: split contractible top summands using finite freeness, then identify the remaining top cohomology as a quotient of a finite free term. I searched Mathlib with LeanFinder, Loogle, and source grep for both the item and the new node; all returned no matching theorem. No statement or hypothesis was weakened.

## What was wrong or incomplete

The imported item had no proof and no proof dependencies. It also lacked a blueprint `split_report`. I supplied the Tag 064S proof directly in elementary steps. An attempted child node was removed after preflight identified it as a forbidden restatement of the item (delivery-errors D1/D2).

## Could not finish

There are no unfinished child nodes.

## Second reading by F1

- Item statement: checked against More on Algebra Tag 064S (`more-algebra.tex`, `lemma-finite-cohomology`), including the ring, complex, degree, pseudo-coherence, vanishing, and finite-type hypotheses; corrected finite free to finite projective and the ring-level derived-category citation.
- Step 1: checked against the opening of the Tag 064S proof; the witness choice and transfer of vanishing are elementary and match the corrected statement.
- Step 2: checked against the finite-projective splitting and induction in Tag 064S; repaired the prior finite-free wording and explicitly described the contractible summand and finite-generation conclusion.
- Step 3: checked against the final surjection and quotient argument in Tag 064S; the finite-type quotient fact is elementary.
- New nodes: none; the split contains only the item node, so no child-node statement or Mathlib leaf required review.
- Small cases: the zero complex gives zero cohomology; over a field finite projective equals finite free; for m=0 and m=1 the same top-degree cancellation applies; no empty-object exception arises for complexes of modules.
- Blueprint and duplicate search: checked the nearest blueprint ancestor `lem-sc-finite-duality`, its finite-generation proof place, and existing finite-cohomology/pseudo-coherence nodes; no child node is needed and no duplicate was retained.

### Changes made

- Corrected the item metadata and statement to the ring-level Tag 064S formulation with finite projective witnesses.
- Repaired Step 2 so its splitting argument remains valid over an arbitrary ring.
- Added this second-reading record; citations remain empty because every step is elementary.
