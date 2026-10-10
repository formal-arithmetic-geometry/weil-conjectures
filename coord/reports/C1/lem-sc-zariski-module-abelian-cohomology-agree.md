Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-zariski-module-abelian-cohomology-agree.json` — statement, two proof steps, and split report; no new nodes.
- `citations.json` — verbatim citations for every step dependency.

Attachments:

- None.

WANTED:

- None. The item follows Stacks Tag 03FD, whose citation and label are recorded in the existing reviewed comparison node.

What was wrong or incomplete:

- The item was unsplit even though the DAG already contains the reviewed node `lem-sc-module-abelian-zariski-cohomology`, which states the same canonical natural comparison for the small Zariski site. I reused that existing statement rather than creating a duplicate child node.
- The item additionally requires the degree-zero comparison to be the identity, so I added a separate elementary step using the two global-sections definitions.

What I could not finish:

- Nothing.

## Review by C1

I checked the item statement against Stacks Tag 03FD (label `lemma-cohomology-modules-abelian-agree`) and read the existing reviewed node `lem-sc-module-abelian-zariski-cohomology`, including its statement and proof dependencies. Step 1 cites only that node, and its statement explicitly says that the right-derived global sections in module sheaves and in underlying abelian sheaves are canonically isomorphic in every degree and natural in the module sheaf; this is exactly the non-elementary comparison used here. Step 2 cites `pqf-def-cohomology`, whose statement defines module cohomology as the right derived functors of global sections, and `def-sc-zariski-cohomology`, whose statement defines Zariski cohomology as the right derived functors of evaluation at $X$; after forgetting the module structure, both degree-zero functors are the same section group, so the comparison is the identity. I verified that all cited node ids exist, that every citation quote is verbatim, that `proof_deps` is the union of the step uses, and that no new node or Mathlib leaf is needed. The small edge case $q=0$ was checked explicitly; for a one-point scheme the two theories both reduce to the underlying module's abelian group, and for the empty scheme both section groups are zero.
