# Stage-1 worker report

## Files written

- `dag/nodes/sec-smooth-purity/fin2-lem-lisse-trivialized-finite-etale.json`: item split, no new nodes, Mathlib search found no exact scheme/sheaf declaration.
- `citations.json`: verbatim step-to-node citations.

## Attachments

None. No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` states this item, and the keyword/docstring searches found no declaration tagged `(blueprint: fin2-lem-lisse-trivialized-finite-etale)`.

## WANTED

None.

## What was wrong or incomplete in the imported node

The imported proof was a single paragraph and did not make the connected-component reduction, the linear monodromy action, or the passage from an open kernel to a finite etale cover explicit. It also omitted the finite-type-to-Noetherian input and had no statement dependency for the lisse finite-stalk notion. I retained the statement and supplied those missing proof steps. The existing `cor-galois-open-subgroups` statement has the needed pointed formulation, so no duplicate node was created.

## Review by Q41

I read the item source in `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/fin2-lem-lisse-trivialized-finite-etale.md`, the chapter and unit records, and the statements of every cited node. Step 1 uses the existing Mathlib leaf for finite-type algebras over a Noetherian ring and the existing Mathlib leaf for finitely many irreducible components of a Noetherian closed subset; from these statements I checked the finite open-and-closed component decomposition. Step 2 uses the constructible-complexes definition for “lisse” finite stalks, then the two existing Galois equivalences; I checked that addition, zero, and scalar multiplication are sheaf morphisms and therefore the fibre action is Lambda-linear. Step 3 uses only continuity supplied by the fundamental-group equivalence and the finiteness of the fibre, so the kernel is a finite intersection of open stabilizers. Step 4 uses the exact pointed open-subgroup clause of `cor-galois-open-subgroups` and the base-change compatibility clauses of both Galois equivalences; this gives trivial restricted action and hence the constant module sheaf. Step 5 uses the scheme-conventions definitions of finite and etale and checks surjectivity from nonempty finite etale maps to connected components via open-and-closed image. I checked the empty-scheme edge case (the empty finite etale map to the empty scheme is vacuously surjective) and the connected case (one fibre module serves every component of the cover). I ran the required Mathlib searches in both original and second phrasings; LeanSearch was unavailable and is recorded as such. No statement, source hypothesis, or cited-node quote was changed after this review.

## Not duplicates

None: no new nodes were created.


## Second reading by Q41

The literature source files are absent from the read-only shared checkout. I opened the isolated archive `/home/ubuntu/weil-launcher-nt/literature/`: the item's blueprint file at `blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/fin2-lem-lisse-trivialized-finite-etale.md`, Stacks `morphisms.tex`, `properties.tex`, `algebra.tex`, `schemes.tex`, `pione.tex` and `etale-cohomology.tex`. The item agrees verbatim with its blueprint statement: finite type over any field, a finite commutative coefficient ring, finite locally constant modules, a finite etale surjection, componentwise constancy and a common finite fibre when connected. There is no freeness hypothesis or assertion.

- Step 1: checked the original ring-level citation against 00FN (`algebra-lemma-Noetherian-permanence`) and replaced it by the existing scheme-level `lem-weil-pbc-finite-type-over-noetherian`, whose statement is 01T6 (`morphisms-lemma-finite-type-noetherian`); checked `lem-sc-noetherian-closed-subset-finite-components` against 0BA8 (`properties-lemma-Noetherian-irreducible-components`). Verdict: repaired; the field base is Noetherian, the finite-type hypothesis gives the scheme theorem's hypotheses, and the finite union argument explicitly gives closed and open connected components, including the empty case.
- Step 2: checked the complete statements of `def-weil-pbc-constructible-complexes`, `thm-galois-lc-etale` and `thm-galois-fundamental` against the blueprint and Stacks 03RV (`etale-cohomology-lemma-characterize-finite-locally-constant`), 0DV5 (`etale-cohomology-lemma-locally-constant-on-connected`) and 0BND (`pione-theorem-fundamental-group`). Verdict: sound, expanded the product and equivariance equations so linearity is explicit; the base is a nonempty connected component with a geometric point and the stalk is finite.
- Step 3: checked continuity in the complete `thm-galois-fundamental` statement and the action convention of `def-galois-fibre-functor`. Verdict: elementary as written after repair; the inverse image of each singleton is an open stabilizer and their finite intersection is the action kernel. Replaced the right-action homomorphism wording by the actual kernel subgroup, avoiding the opposite-group convention.
- Step 4: checked the pointed clause and degree clause of `cor-galois-open-subgroups`, both Galois equivalences' base-change clauses, and `def-weil-pbc-constant-sheaf`; also read Stacks 0BND and `pione-section-finite-etale-under-galois`. Verdict: sound after expansion; the image of the cover's fundamental group is exactly the specified stabilizer, the restricted action is trivial, and faithfulness makes the identity-on-fibre isomorphism preserve addition, zero and every scalar map. The trivial-action/constant-sheaf identification is now explained by finite coproducts of the terminal object.
- Step 5: checked `cor-galois-open-subgroups` and `def-pc-finite-locally-free` for positive constant degree, `lem-weil-pbc-scheme-coproduct-family` against 01JB/01JC (`schemes-lemma-glue`, `schemes-lemma-glue-schemes`), `lem-weil-pbc-finite-local-on-target` against 01WI (`morphisms-lemma-finite-local`), and the affine-local etale characterization in `def-weil-etale-morphism` against 02GI/02GJ (`morphisms-definition-etale`, `morphisms-lemma-etale-characterize`). Verdict: repaired; nonzero-dimensional global sections rule out an empty fibre at every base point, target locality proves finiteness, and the etale affine charts on the open summands remain affine charts of the assembled morphism. No uncited assertion that a finite etale image is open and closed remains.
- New nodes: none. B1–B7 introduce no new obligations; all additional citations are existing nodes. Searched the entire DAG/blueprint by finite locally constant, trivialization, finite type/Noetherian, coproduct, target locality and the cited tags; no duplicate node was created. The existing scheme-level Noetherian and finite-target-locality nodes are Mathlib leaves; the scheme-coproduct and constant-sheaf inputs are existing nodes.

Changes and reasons:

- Replaced the ring-only Noetherian input with the existing scheme-level theorem, which states exactly the fact the step needs.
- Replaced the final definitions-only citation with actual coproduct existence and finite-target-locality inputs; proved surjectivity directly from the already cited positive degree and the definition of degree.
- Expanded linearity, subgroup formation, the constant-sheaf identification, and compatibility of all module operations. Preserved the original five-step route and the item's statement.
- Completed statement dependencies for scheme/morphism conventions, constant sheaves and connectedness. Regenerated `citations.json` with one complete verbatim statement per step-node citation, replacing the previous cut-off mid-word snippets and duplicate citation.
- Kept the first worker's sections, including `## Review by Q41`; its earlier verdict about the sufficiency of the ring input and of definitions for step 5 is superseded by this reading. Moved proposed cross-unit tool edges into this report rather than installing maintainer `tool_uses`: `thm-galois-lc-etale` and `thm-galois-fundamental` supply the generic finite-monodromy classification explicitly required by the item's own blueprint proof. The coproduct construction is also a generic scheme-existence tool; no unit-specific replacement route is used.
- Ran independent Mathlib searches with a broader monodromy/covering-scheme phrasing, a global grep, and the valid Loogle query `"IsConstant", "Sheaf"`; actual outputs are appended to `searches.jsonl`. Read `CategoryTheory/Sites/ConstantSheaf.lean:212–233`: the generic criteria require a pre-existing constant underlying sheaf and cannot construct the finite etale trivializing cover. The grep hits concern ordinary topological monodromy. No exact Mathlib declaration or newly attached upstream proof was found. Corrected the earlier unknown-identifier Loogle verdict to unavailable rather than treating it as evidence of absence.

Edge cases checked: the empty scheme uses its identity map; over a field a nonempty connected component has a geometric point; a zero module (also the sole module over the zero ring) has a singleton underlying set and full action kernel, so degree one is allowed; a constant sheaf gives the same full kernel; a nonfree finite module such as Z/ell over Z/ell^2 needs no change in the argument; disconnected bases may have different fibre modules, and the coproduct keeps these separate. No characteristic restriction, normality, separateness or freeness is introduced.

Search provenance correction: the first worker grep with subdirectory `Mathlib` actually searched the nonexistent `Mathlib/Mathlib`; its verdict is now unavailable/invalid path. The other recorded grep searched only `AlgebraicGeometry`, so its displayed scope was corrected. The second reader global grep above is the actual replacement search; no missing-path zero count is used as evidence.
