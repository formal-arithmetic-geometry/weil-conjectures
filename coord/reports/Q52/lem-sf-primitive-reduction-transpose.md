# Q52: lem-sf-primitive-reduction-transpose

## Files written

- `dag/nodes/sec-six-functors/lem-sf-primitive-reduction-transpose.json`: statement node, split; statement and statement dependencies unchanged. No Mathlib match for this geometric assertion.
- `citations.json`: one verbatim statement excerpt for every step/node citation.
- `report.md`: worker report and direct-delivery self-review.

No new nodes; no new Mathlib leaves. The sandbox initially contained only dispatcher brief markers, with no previous split, report, citations or search log to recover. The original imported search records have been retained. `write_split.py` is the sandbox-only construction script; `searches.jsonl` is the unmodified search tool log.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag, primitive/transpose combinations, semilinear systems, reduction/counit combinations and completed pullback. Existing completed-exchange and coefficient results cover other assertions; none states all four primitive whole-system identities of this item. I also read the existing DAG realization node's recorded Lean signature rather than treating its existence theorem as a proof of the present map identities.

## WANTED

None. The item is an agent refinement of the blueprint, not a theorem stated verbatim in Stacks. The source blueprint and the existing supporting construction nodes are available locally.

## Corrections and scope

The statement was not changed. The empty proof was replaced with seven steps. The primitive pullback/tensor Roos realization and the finite canonical reduction map already have nodes, so neither was recreated. The elementary inversion of the specified open comparison and the three-line counit/triangle calculation are proof steps, not new lemmas. There is no new node restating a clause of the item.

The canonical coefficient map is never defined afresh as the desired transpose. Steps 2–4 use the existing independent quotient-complex models, their projection normalization, and the actual scalar action on a representative. Step 1 supplies the existing strict-system representative of the actual counit. Their chain maps agree, including the quotient transition squares, before localization. Equality of separately evaluated derived morphisms would not be sufficient, and is not used.

The unit is `sk-thm-sf-compatibility`, and the nearest blueprint ancestor is `fix-prop-coherence`, maps-used sentence in the package proof. I read the chapter and unit records. This is its primitive coefficient-comparison argument, not a replacement of the unit route. `lem-pur-completed-primitive-counit-comparison` and `lem-pur-integral-operation-roos-effectivity` are recorded as generic tool uses: they supply the already specified Roos construction and canonical finite-projection formula. No chapter or unit file was edited.

## Mathlib searches and duplicate checks

I ran every new search through `/home/ubuntu/weil-launcher-all/batch2/msearch.py Q52 lem-sf-primitive-reduction-transpose`, and read the returned hits and `searches.jsonl`. The first LeanFinder query returned scheme pullback and ordinary sheaf adjunction results; the second returned ordinary sheaf global-section/limit and sheafification limit lemmas. Neither concerns completed coefficient operations or whole semilinear systems. Loogle `"Adjunction", "counit"` returned general adjunction constructors and the counit definition, without the required geometric normalization. The grep query `completed.*(pullback|tensor).*counit|reduction.*total.limit.*adjunction` in `CategoryTheory` returned zero hits. LeanSearch returned an explicit service rate-limit error and is recorded as unavailable. General adjunction calculus alone does not identify the independently specified geometric comparisons, so these results do not make the item a Mathlib leaf.

Before choosing the proof I searched the DAG by counit, primitive, projection, transpose, total-limit and realization vocabulary, and read the potentially matching nodes. Whole-blueprint searches included `transpose`, `counit`, `primitive reduction`, and `total-limit projection`; the latter two had zero matches. The exact smaller realization, cochain-transpose and Roos-effectivity nodes are reused. No imported blueprint statement duplicates the whole primitive assertion, so `blueprint.same_as` remains empty. There are no new-node/existing-node duplicate pairs requiring a `## Not duplicates` table.

## Review by Q52

I read the item against `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md`, especially its maps-used sentence. That sentence motivates coherence but does not itself prove the strict-system identification. The proof is therefore explicitly marked agent-written. I read Stacks `sites-cohomology.tex`, Tag 07A6 (`lemma-adjoint`), Tag 0FPI (`lemma-adjoints-push-pull-compatibility`), and Tag 0941 (`lemma-derived-limit-is-ok`). They explain derived adjunction, its K-flat/K-injective counit normalization, and total limit on the sequence site; they are not claimed to state the varying-ring comparison on their own. There are no new nodes with unverified source attributions. No SGA source is used.

Step 1 uses `lem-coef-derived-system-evaluation-calculus` for the actual reduction/limit adjunction, unit and counit, and `lem-coef-sequence-adjunction-cochain-transposes` for the exact formula for its representative on a flat-term K-flat resolution of the limit of a K-injective system. I checked that this statement expressly allows the system resolution without asserting that its scalar restriction or its individual evaluations are K-injective. The strict transition equation is written out, with the scalar reduced from level m to n. Thus the argument uses a chain map of systems, not faithfulness of derived evaluation.

Step 2 uses `def-pur-integral-derived-operations` for the actual quotient-complex/Roos formulas for pullback and tensor, `lem-coef-semilinear-derived-sections` for simultaneous inverse image and tensor, and `lem-pur-completed-primitive-counit-comparison` for the natural projection-compatible realization isomorphisms with the zero shifted-coordinate normalization. I checked the direction: that node's r_F and r_T go from the completed operation to total limit, so they are d_A inverse in this item's coordinates. The item assumes normalization and all bounds at every intermediate; I do not infer those bounds from a definition.

Step 3 uses `lem-pur-integral-operation-roos-effectivity` for the canonical reduction map as the adjoint of the actual projection, including its transport under a realization isomorphism. This is a statement of that node, not an assertion taken only from its proof. Its good complexes are precisely the flat-term K-flat input representatives already specified in step 2. `def-sf-integral-system-canonical-bridge` pins the comparisons on whole representatives and fixes the ordinary maps independently; it is used for that normalization data, not as a theorem proving coherence. The scalar adjoint formula of `lem-coef-sequence-adjunction-cochain-transposes` then gives exactly the same system chain map as the counit. I checked the two tensor inputs remain separate and that no flatness of a finite quotient is assumed.

Step 4 uses `lem-coef-semilinear-derived-sections` for the actual derived direct-image system and its scalar-mate transition formula. `def-weil-derived-direct-image` explicitly defines the integral image by that tower's total limit and explicitly defines its finite coefficient map as the projection adjunct. `def-sf-integral-system-canonical-bridge` fixes the projected-section identity and adjoint-conjugation normalization. The same cochain-transpose lemma supplies the representative, so the conclusion concerns the specified system map. Properness, finite type and the bounded constructible input hold by the item; no unproved assertion that every direct-image system is normalized is inserted.

Step 5 uses exactly the displayed formula for d_j in `lem-sf-integral-open-reduction-comparison`. Its hypotheses are satisfied: j is quasi-compact open, ell is invertible on the schemes, and K is derived complete. That node also states completeness of j_!K and invertibility of its actual unit. The inverse formula follows by inversion of a composite, so this step is elementary. Step 6 uses the counit naturality and triangle identity supplied by the actual adjunction of `lem-coef-derived-system-evaluation-calculus`. The object in the triangle is X=j_!K: e_(R X) followed by R(u_X), in the indicated order. This verifies both requested open equations with no further geometric lemma.

Step 7 uses the naturality clauses of the cochain-transpose, primitive-realization, direct-image-definition and open-comparison nodes. I checked that these are natural comparisons of functors on the original derived categories, rather than arbitrary choices at the individual levels. The stated hypotheses retain etale-origin witnesses and uniform finite cohomological/Tor intervals throughout. None is dropped or silently replaced by site-perfectness.

I checked delivery-errors B through E: self-contained unchanged statement; all cited IDs already exist; no new proof sketches masquerading as statement nodes; literal TeX; no fabricated search records; no use of a cited proof in place of its statement; no reliance on derived evaluation to detect equality; no circular citation of the parent generator-coherence theorem; no relocation of a primitive clause into a fresh node. The retained new proof dependencies were inspected for back-edges to this item, and the server checks will independently test the graph. Every step is shorter than 2000 characters. Small-case checks included zero inputs, identity morphisms, the empty open, identity open, equal levels m=n, and arbitrary ramification of E: all formulas reduce to zero or identity/unit/counit as appropriate. The scalar transition computation also covers every m>=n, not only adjacent indices. No disputed statement was found.

## Unfinished work

None in this one-level split. Existing unsplit dependencies remain their own items. The required server dry run and direct push are the final delivery checks.
