Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-glue-component-line-bundles.json` — statement, split proof, Stacks source, and split report.
- `dag/nodes/sec-curve-estimates/lem-sc-glue-component-reduced-cover-sections.json` — statement node; Mathlib search verdict: no match.
- `dag/nodes/sec-curve-estimates/lem-sc-glue-component-transition-cocycle.json` — statement node; Mathlib search verdict: no match.

Attachments:

- None.

WANTED:

- None. The cited Stacks sources were read from the local review checkout at `/home/ubuntu/c1-stacks-review/varieties.tex`; the repository's literature checkout is not materialized, but the node's canonical document paths are retained.

What was wrong or incomplete in the imported node:

- The item had no proof at all, although its source proof contains several non-elementary gluing arguments. I split out the reduced-cover restriction identity and the Cech transition-function construction rather than hiding them in an elementary step.
- The statement itself matches Varieties Lemma 09NE: reducedness, set-theoretic closed-subscheme cover, discrete pairwise intersections, invertible sheaves, and the nonvanishing hypothesis on prescribed sections were all checked against the source.
- I searched the whole DAG and blueprint for both supporting statements and found no existing node stating either one. No Lean declaration carrying this item tag or its theorem was found in slopmaster2.

What I could not finish:

- No Lean implementation was attempted, as required for stage 1.

## Review by E1

I read the complete source proof of Varieties Lemma 09NE in `/home/ubuntu/c1-stacks-review/varieties.tex`, lines 7990--8088, and checked the item statement clause by clause against its three hypotheses and both conclusions. Step 1 follows the source's definition of the discrete locus `T`, its use of reducedness to identify the complement with the scheme-theoretic union of the component opens, and the resulting structure-sheaf restriction statement; that last assertion is recorded as `lem-sc-glue-component-reduced-cover-sections`. Step 2 checks the source's separate choices of one-point neighborhoods at `T`, local frames for each invertible module, and the open cover away from `T`; in the section case I verified the additional nonvanishing shrink and normalization to `1`. Step 3 follows the source's three overlap cases: overlaps inside one component use the component transition functions, different component opens are disjoint, and overlaps of two `T`-neighborhoods decompose over the disjoint component pieces. The cocycle construction is isolated as `lem-sc-glue-component-transition-cocycle`, sourced to Schemes Lemma 01JB, and step 3 cites both supporting nodes. Step 4 checks the source's final normalization argument: the local section `1` on each `U_t` and the prescribed local expressions on each `U_{ij}` agree under the transition maps, so the sheaf axiom yields the global section with the required restrictions. I tested the edge cases conceptually: `T=empty` reduces to ordinary componentwise gluing, a single component has no cross-component overlap, and an empty pairwise intersection imposes no nonvanishing condition. I also checked every new node for duplicate IDs/statements in the DAG and recorded LeanSearch/LeanFinder or Loogle/grep searches; neither statement is present in Mathlib.
