# Stage 1 report: lem-coef-ordinary-directed-cover-colimit

Files written:

- `dag/nodes/sec-six-functors/lem-coef-ordinary-directed-cover-colimit.json`: item statement retained and split into five proof steps; no new nodes or Mathlib leaves.
- `citations.json`: one verbatim citation for the existing colimit definition at each proof step.
- `report.md`: this worker report.

Attachments: none. I searched the read-only slopmaster2 project for the item id, its blueprint tag, and the ordinary directed-cover terminology. No sorry-free project declaration states this item. The existing `def-weil-pbc-category-colimit` node is a Mathlib leaf and is cited as the sole dependency.

WANTED: none. The proof uses the locally archived Stacks Categories Definition 002F and the agent-formulated directed-cover argument recorded in the blueprint ancestor proof. No document was downloaded.

What was wrong or changed: the imported item was unsplit and had only a source note. I retained its statement, source, statement dependency, blueprint ancestry, and existing Mathlib search records. I expanded the proof into explicit construction of transition maps and the total cocone, gluing of compatible families using finite upper bounds and fullness, the converse factorization, the universal-property comparison isomorphism, and the empty cases. No clause was moved into a new node. The existing infinity-categorical directed-cover nodes are not duplicates: they concern coherent simplicial diagrams and do not state this ordinary-category cocone bijection.

Nothing remains unfinished in this stage-1 split.

## Not duplicates

`lem-coef-ordinary-directed-cover-colimit` vs `lem-coef-directed-cover-colimit-assembly`: the existing node concerns colimits of coherent simplicial diagrams in an infinity category, whereas this item concerns ordinary categories, full subcategories, and an explicit bijection of ordinary cocones.

`lem-coef-ordinary-directed-cover-colimit` vs `lem-coef-infinity-directed-union-local-colimits`: the existing node gives a mapping-space comparison for quasicategorical local colimits without assuming global cocompleteness; this item gives an ordinary universal-property proof with chosen ordinary colimit cocones.

`lem-coef-ordinary-directed-cover-colimit` vs `def-weil-pbc-category-colimit`: the existing node defines a single colimit and its canonical map; this item proves assembly of colimits over a directed cover by full subcategories.

## Review by NY

I read the current item node, the `sec-six-functors` chapter record, the `sk-prop-sf-biduality-general` unit record, the blueprint ancestor `prop-coef-integral-exceptional-adjoint` and its proof, and Stacks `categories.tex` at the `definition-colimit` label (Definition 002F, lines 1310–1329). I also read the complete statement of `def-weil-pbc-category-colimit` and the two existing infinity-directed-cover statements listed above. The item statement is unchanged: the index poset is nonempty and finitely directed, the subcategories are literal increasing full subcategories covering all objects, all small colimits exist in the target, and empty ambient or stage subcategories are allowed.

Step 1 uses exactly the cited definition's colimit universal property to construct each $u_{ij}$ and $v_i$ and to prove identities, composition, and cocone compatibility by equality on all colimit legs. Step 2 uses the same statement to define a global cocone from a compatible family; I checked that finite upper bounds handle two choices and both endpoints of every arrow, while fullness places that arrow in the common stage. Step 3 uses the cited factorization and uniqueness clause to recover each $f_i$ from a global cocone and to prove the two constructions are inverse. Step 4 applies the definition again to the $I$-diagram, identifying the compatible-family bijection with the universal property of $(L,(v_i))$ and hence with the canonical comparison isomorphism. Step 5 checks empty $C$ and empty $C_i$ directly from the same initial-object universal property.

I verified every citation quote is verbatim from the existing node, and `proof_deps` is exactly the union of the five `uses` lists. I tested the argument on a singleton index, repeated stages, empty $C$, all-empty stages, empty early stages followed by a nonempty stage, incomparable indices with a common upper bound, and categories with parallel arrows. No hidden lemma, compiler, Lake build, Lean edit, or live-project write was used; every proof step is under 2000 characters and the route has no cycle.
