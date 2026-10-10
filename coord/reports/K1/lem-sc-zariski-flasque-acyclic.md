1. Files written:

- `dag/nodes/sec-smooth-purity/lem-sc-zariski-flasque-acyclic.json` (item, split)
- `dag/nodes/sec-smooth-purity/lem-sc-zariski-injective-flasque.json` (statement, Mathlib no match)
- `dag/nodes/sec-smooth-purity/lem-sc-zariski-flasque-quotient-sections.json` (statement, Mathlib no match)
- `citations.json`

2. Attachments: none.

3. WANTED: none.

4. The imported proof was one compressed paragraph. I checked Stacks Cohomology, Lemma 09SY and Section 01FT, and verified that its two substantive inputs are injective sheaves being flasque and the flasque short-exact-sequence section-surjectivity/quotient lemma. I searched the full DAG and found no abelian-sheaf node for either input; the existing ringed-space module restriction lemma is a different statement. The item proof now uses those two new nodes, the existing site-sheaves-enough-injectives statement, and the imported Zariski cohomology definition. The empty sheaf and one-point space give the expected zero cases; the statement is unchanged.

## Review by K1

I read the item source and both source locations used for the new nodes in `literature/stacks-project/cohomology.tex`. Step 1 cites exactly the restriction-surjectivity sentence of the injective-flasque node and both conclusions of the flasque-quotient node. Step 2 verifies the hypothesis of enough injectives from the existing site-sheaves node and uses the quotient node at every iteration, so each section complex is exact in positive degrees. Step 3 uses the exact resolution formula in `def-sc-zariski-cohomology` and is an elementary application at the object X. I checked that the new statements introduce all their objects and that neither duplicates the existing module-sheaf or topological-specialization nodes. Mathlib searches were run for the item and each new statement with LeanFinder, Loogle, and Mathlib grep; no exact theorem was found (LeanSearch for the item was unavailable and recorded as such). `citations.json` quotes the relevant portions verbatim.

## Not duplicates

`lem-sc-zariski-injective-flasque` vs `lem-sc-ringed-space-injective-restriction-surjective`: the new node is for injective objects in the abelian category of abelian sheaves, while the existing node assumes a ringed space and injective module sheaves; the constant-ringed-space specialization is not the same stated category.

`lem-sc-zariski-injective-flasque` vs `lem-sc-ext-coherent-hom-injective-flasque`: the existing node concerns the specific sheaf-Hom from a coherent module into an injective module, whereas this node concerns arbitrary injective abelian sheaves and all open restrictions.

lem-sc-zariski-injective-flasque vs lem-sc-topological-flasque-acyclic: the existing node states the final vanishing theorem for a flasque sheaf on the opens site, while this new node states the separate intermediate fact that an injective abelian sheaf has surjective restrictions.
lem-sc-zariski-flasque-quotient-sections vs lem-sc-topological-flasque-acyclic: the existing node states the final vanishing theorem, while this new node states the short-exact-sequence section-surjectivity and flasque-quotient lemma used to construct the resolution.

5. Nothing remains unfinished.

## Second reading by K1

- Item statement: checked against Stacks Cohomology Tag 09SY (`lemma-flasque-acyclic`) and the cohomology-over-an-object definition; the vanishing statement and $q>0$ range agree.
- Step 1: checked against Tag 09SY's flasque-resolution argument and the new abelian-sheaf injective restriction node; the quotient node supplies both section surjectivity and flasqueness.
- Step 2: checked against Tag 09SY's injective-resolution iteration and the existing enough-injectives node; the section complex exactness follows degree by degree from Step 1.
- Step 3: checked against Section 01FT and `def-sc-zariski-cohomology`; applying exactness at the object $X$ gives the claimed positive-degree vanishing.
- `lem-sc-zariski-flasque-quotient-sections`: checked against the explicit Zorn/gluing proof in Tag 09SY; the statement is self-contained and its hypotheses match.

Changes: retained the abelian-sheaf injective restriction node because the existing Tag 01EA node is specifically for ringed-space modules; clarified its source as the abelian-sheaf extension-by-zero argument and updated the item citation. The quotient node remains the only non-duplicate auxiliary statement.
