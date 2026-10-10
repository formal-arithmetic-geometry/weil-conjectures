1. Files written

`dag/nodes/sec-abelian-varieties/lem-pc-scheme-dimension-local-rings.json`: the item, now split into three proof steps; no new nodes.

2. Attachments

None. I searched the slopmaster2 source for the item id and for declarations involving scheme Krull dimension and stalk dimensions; no sorry-free declaration states this equality exactly.

3. WANTED:

WANTED: `literature/stacks-project/properties.tex`, Properties Lemma Tag 04MU (equality of the topological dimension and the supremum of local-ring dimensions), for `lem-pc-scheme-dimension-local-rings`.

4. What was wrong in the node, blueprint, or brief

The imported node had the correct statement and source but no proof split. I supplied the missing chain argument. The proof uses the existing Mathlib leaf `lem-sc-scheme-stalk-dimension-generalization-chains` for stalk dimensions, `lem-sc-scheme-sober` for unique generic points, `lem-weil-pbc-irreducible-closure` for irreducibility of closures, and `def-weil-irreducible-components` and `def-kun-topological-krull-dimension` for the chain definitions. No statement or route change was needed.

5. What I could not finish, and why

The full Stacks TeX checkout is not present in this clone, so I could not inspect the cited lines directly. The proof is written from the cited Tag 04MU argument and records the missing document above.

## Review by G1

I checked the item statement against the imported source citation Properties Tag 04MU and retained it verbatim, including the empty-scheme convention. I searched the read-only slopmaster2 checkout by item id and by the relevant dimension/stalk names; the only nearby declarations are inequalities or ingredients, so there is no attachment. Step 1 uses exactly the existing statement of `lem-sc-scheme-stalk-dimension-generalization-chains`, which identifies the stalk ring dimension with generalization-chain lengths. Step 2 uses the statement of `lem-sc-scheme-sober` for unique generic points, `lem-weil-pbc-irreducible-closure` for closures remaining irreducible, and the irreducibility definition; it explicitly checks both directions and strictness of the chain correspondence. Step 3 unfolds `def-kun-topological-krull-dimension`, takes the two suprema, and handles the empty case. I verified every cited id exists and is unmerged in the repository DAG, preserved the blueprint fields, and recorded all Mathlib searches already present on the item. No new node or Mathlib leaf was needed.
