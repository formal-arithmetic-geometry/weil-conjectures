Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-conductor-sections.json` — item, statement, split proof; no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-conductor-ideal-restriction.json` — new unsplit statement; no Mathlib match.

Attachments:

- None. No sorry-free slopmaster2 declaration states the item or the new node.

WANTED: `literature/stacks-project/varieties.tex`, Varieties Remark 09NW (varieties-remark-conductor), for `lem-sc-conductor-ideal-restriction` and the first proof step of `lem-sc-conductor-sections`.
WANTED: `literature/stacks-project/varieties.tex`, Varieties Lemma 09NX proof (displayed conductor equality of global sections), for the second proof step of `lem-sc-conductor-sections`.

What was wrong or incomplete in the imported item: it was unsplit and had no proof. The parent proof text cited `lem-sc-conductor-sections`, but that node did not exist as a split proof in the checked-out DAG. I did not change the mathematical statement. The new node is strictly smaller: it states only the sheaf-level conductor restriction isomorphism, while the item proves the global-sections extension statement for every tensor power and its nonvanishing-locus consequence.

What I could not finish: the Stacks source files named by the node are not included in this repository, so I could not inspect their prose directly. The proof follows the imported source places and records the missing files above. Lean compilation is outside stage 1 and was not run.

## Review by E1

I checked the item against its imported source citation, Varieties Remark 09NW and the conductor paragraph of Lemma 09NX, as recorded in the node. The item hypotheses introduce the reduced scheme, its finite reduced component cover, the reduced union of the other components, both ideal sheaves, the invertible module, and the tensor exponent; the statement uses each of those objects. I checked the new node separately: it introduces the same scheme-theoretic data but concludes only the restriction isomorphism/conductor equality, so it does not restate the item. I searched all DAG nodes and the blueprint for an existing conductor restriction node and found none.

Step 1 uses the new node's conductor restriction statement and the invertibility definition to tensor the isomorphism. Step 2 uses the closed-immersion ideal-sheaf meaning to pass to global sections and obtain the unique preimage section; this is the displayed global-sections equality cited from 09NX. Step 3 uses only the ideal-sheaf vanishing meaning and the definition of a section's nonvanishing locus to identify the open on the remaining component. The first two steps are marked non-elementary because they invoke the cited Stacks conductor/global-sections argument; the final step is a direct check from the definitions.

For small cases I checked: one component (`r=1`, so the other-component ideal is the unit ideal and the restriction is tautological), a reduced point, two disjoint reduced components (the section extends by zero on the other component), and two reduced components meeting at a point (the extended section vanishes at the intersection). These checks exposed no change needed in the statement or proof. The Mathlib searches recorded in both nodes cover LeanSearch, LeanFinder, and source grep; none found a matching conductor theorem.
