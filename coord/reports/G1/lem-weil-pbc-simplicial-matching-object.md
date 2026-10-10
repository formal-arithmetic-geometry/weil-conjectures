files written

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-simplicial-matching-object.json`: statement node, no new Mathlib leaf.

attachments

- `lem-weil-pbc-simplex-face-face-identity` is the existing DAG node used for the simplicial face relation.

WANTED:

what was wrong in the node, the blueprint, or the brief

The item was unsplit and had no proof steps. I kept its statement and dependencies unchanged. The source's finite-limit argument and universal-property argument are now explicit. The existing face-face identity node was searched for and cited instead of creating a duplicate. I found no statement error and no source error.

what I could not finish, and why

Nothing remains unfinished in the requested stage-1 split.

## Review by G1

I read the item source in `literature/stacks-project/simplicial.tex`, Lemma 0186 (label `lemma-formula-limit`), including the displayed compatible-tuple functor and the construction of the matching morphism. I also read Lemma 0167 (label `lemma-relations-face-degeneracy`) for the face-face relation, and `literature/stacks-project/categories.tex`, Section 4.18 (tag 04AS) and Lemma 002O for finite-limit existence. The blueprint ancestor is `lem-weil-pbc-hypercover-refinement`, fourth proof paragraph; the three steps realize its matching-object and matching-map prerequisite.

Step 1 checks that the diagrams are finite by their explicit finite index sets, then uses the statement of `def-galois-finite-limits-colimits` for the limit. The empty and two-object cases were checked separately, giving a final object and a product. Step 2 uses only the limit universal property stated by that dependency: projections give compatible tuples, and compatible tuples give a unique cone; the n=1 case has no equations. Naturality is direct from precomposition. Step 3 uses the statement of `lem-weil-pbc-simplex-face-face-identity`, which is exactly the relation required by Lemma 0186, then applies Step 2 to the tuple of face maps; n=1 and n=0 were checked separately.

I searched the whole DAG and blueprint before writing: the face identity already exists as `lem-weil-pbc-simplex-face-face-identity`, and no existing node states the matching-object lemma itself. The Lean source was searched by the item id, matching-object terminology, and simplicial terminology; no declaration, with or without `sorry`, states this item. Mathlib searches recorded on the item found only coskeleton infrastructure and no matching-object theorem. Small cases checked were n=0 (empty diagram/final object), n=1 (two-object product with no compatibility condition), and n=2 (three faces with the single family of pairwise compatibility equations).
