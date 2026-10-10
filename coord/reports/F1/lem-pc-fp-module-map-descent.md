1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-fp-module-map-descent.json`: split statement.
- `dag/nodes/sec-picard-framework/lem-pc-fp-module-map-descent-affine.json`: new unsplit statement node; Mathlib searches found no match.

2. Attachments: none.

3. WANTED: none.

4. The imported item is the qcqs scheme form of Stacks Limits Lemma 01ZR. I checked the statement against the source and retained its Noetherian affine specialization. The source's first proof explicitly reduces affine schemes to the ring lemma `algebra-lemma-colimit-category-fp-modules`; that narrower ring statement is the only new node. Step 1 uses exactly its module, map, and equality clauses. Step 2 uses the same clauses for the finite affine cover, pairwise overlaps, and triple-overlap compatibility; directedness supplies a common stage before gluing. Step 3 is the direct unpacking of the resulting glued data into clauses (1) and (2), with base-change associativity supplying the canonical identifications. I checked that the finite affine-cover argument uses quasi-compactness and quasi-separatedness as required by the source. The imported blueprint mentioned finite-presentation and differential data but did not spell out this module-map split; the item source 01ZR supplies the route.

5. I could not find a sorry-free declaration of this geometric inverse-limit module descent statement in `WeilConjectures/`. The affine ring theorem is not in Mathlib, so it remains an unsplit DAG node.

## Not duplicates

`lem-pc-fp-module-map-descent-affine` vs existing module colimit nodes: the new node concerns modules over a filtered colimit of rings and extension-of-scalars between different affine bases; existing nodes concern filtered colimits of sheaves on one fixed scheme, so their statements differ.

`lem-pc-fp-module-map-descent-affine` vs `lem-pc-fp-complex-descent`: the new node is the affine ring-level theorem for arbitrary finitely presented modules, maps, and equalities; the existing node is a bounded complex statement over Noetherian affine schemes and cites the target item.
`lem-pc-fp-module-map-descent-affine` vs `lem-pc-finite-flat-proper-support-descent`: the new node is a ring-level colimit theorem; the existing node descends a bounded finitely presented flat complex together with proper support over a scheme system.
`lem-pc-fp-module-map-descent-affine` vs `lem-pc-fp-relation-descent`: the new node gives affine object and map descent over a ring colimit; the existing node assumes already descended sheaf modules and only descends finitely many relations between their maps.
`lem-pc-fp-module-map-descent-affine` vs `lem-pc-flat-bounded-complex-descent`: the new node is a ring-level module/map/equality theorem; the existing node concerns eventual flatness of terms of a bounded complex on a scheme system.
`lem-pc-fp-module-map-descent-affine` vs `lem-pc-noetherian-approximation-data`: the new node has no scheme, Noetherian, flatness, support, or perfectness hypotheses and states only the affine algebra input; the existing node packages all of those geometric approximation conclusions.

## Review by F1

I read `/home/ubuntu/c1-stacks-review/limits.tex` at the full proof of `lemma-descend-modules-finite-presentation` (Tag 01ZR), including the affine reduction and the sentence invoking Zariski gluing. I also read the target node, its blueprint ancestor, and the existing fixed-scheme module-colimit nodes before creating the affine node. For Step 1 I verified that the new node states all three ring-level facts used: object descent, map descent between fixed models, and eventual equality. For Step 2 I verified the hypotheses where they are used: finite affine covers come from quasi-compactness, quasi-compact pairwise intersections from quasi-separatedness, and a single later index exists because the cover and compatibility data are finite and the index is directed. The gluing sentence follows the source's stated Zariski-gluing construction and applies equally to modules, maps, and comparison isomorphisms. Step 3 only unpacks the two requested clauses and the canonical base-change identifications. I ran the required Mathlib searches for the item and the new affine node; LeanSearch was unavailable and is recorded as unavailable for the item, while the new node's LeanFinder, Loogle, and grep searches all found no matching theorem. I corrected the new node's JSON escaping before validation and added verbatim citation quotes.
## Second reading by F1

- Item statement: checked hypothesis by hypothesis against Limits Lemma 01ZR (Tag 01ZR); the Noetherian affine-base and finitely presented scheme specialization is valid, including the zero module, field, empty scheme, and trivial directed-system cases.
- Affine node: checked against the affine clause of Tag 01ZR and Algebra Lemma algebra-lemma-colimit-category-fp-modules; it is strictly smaller than the item, self-contained with definition dependencies, and its LeanFinder, Loogle, and grep searches are recorded.
- Step 1: checked the affine reduction against Tag 01ZR; corrected the affine object from S_i to X_i and made the coordinate-ring colimit and extension-of-scalars identification explicit.
- Step 2: checked the general gluing route against the Zariski-gluing sentence in Tag 01ZR and the qcqs hypotheses; corrected the invalid implicit assumption that pairwise intersections are affine by adding finite affine refinements of pairwise and triple intersections and spelling out finite cocycle descent.
- Step 3: checked extraction of clauses (1) and (2) against the item statement and Tag 01ZR; expanded the construction so it no longer relies on proof shorthand.
- Citations: verified each non-elementary step's verbatim affine-node quote against the node statement; no uncited non-elementary fact was added.
- New-node form: verified statement-only form, self-contained definitions, TeX escaping, Tag 01ZR source label, blueprint metadata, and no duplicate existing node; no Mathlib declaration matches the ring descent theorem.

Changes made: repaired the affine reduction target, made finite affine overlap refinements and cocycle equalities explicit, and expanded final clause extraction.
