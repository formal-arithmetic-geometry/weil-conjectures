# Stage-1 worker report: lem-pur-completed-line-tensor-coherence

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-completed-line-tensor-coherence.json`: statement; split into eleven proof steps using existing nodes; not a Mathlib leaf.
- `citations.json`: one verbatim statement quote for every node citation in every proof step.
- `report.md`: this report.

No new nodes, no Mathlib leaves, no unit record changed. The item's statement, source, statement dependencies, origin metadata, blueprint ancestry and previous Mathlib searches are preserved. New actual searches were appended to its search record. This is a first split, not a returned delivery. The sandbox initially contained no item or report.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, completed-line tensor names, and completed tensor/coherence notions. The hits concern ordinary algebraic completions, scalar categories, or other tensor coherences; none states all clauses for arbitrary compatible lines and the specified strict completion cone. Existing line-tensor declarations alone would not attach this item. No Lean was written or compiled.

## Literature

WANTED: none.

Read the current blueprint `main-20261015`, `sec-smooth-purity/sk-prop-an/sk-def-sp-tate-twist-locally-free.proof.md`, particularly (3), the final evaluation/termwise-tensor paragraph. Read the chapter and unit records: this item is a detail of the line inverse used in the model-purity unit, not its key statement, so its unit realization is not edited. The proof does not replace any affine-line, trace, frame-independence or descent step of the unit.

Read Bhatt–Scholze, Definition 3.4.10 and Lemma 3.4.12, pp. 22–23, Proposition 3.5.1 and Definition 3.5.2, p. 24. These give the completed tensor and reduction-tower completeness context. The authors do not state this eleven-part line/coefficient coherence as a numbered result. Accordingly `proof_origin.by` is `agent`.

Read Stacks `sites-modules.tex`, tensor-product section, especially the sectionwise algebra/sheafification formulas before Tag 0GMW, Tag 03EL (`lemma-tensor-product-pullback`) and Tag 03EO (`lemma-internal-hom-adjoint-tensor`). Read `sites-cohomology.tex`, Tags 06YY (`lemma-derived-base-change`) and 07A4 (`lemma-pullback-tensor-product`), including their K-flat computation arguments. These explain the ordinary comparison formulas. No SGA source is used.

## Faults and corrections

No statement dispute or statement correction was needed. The original item already specifies the strict quotient-tower cone, zero shifted-product component, comparison by conjugation in the derived category, and non-strict identity-extension unit. Its empty proof was the unfinished part. The split now proves the ordinary squares before completion, uses equivalence preservation of products for completeness, and expands both completed equations by naturality and cancellation. It does not identify the completed functor with the identity before normalization, claim finite quotient projections detect arbitrary derived maps, or assert a chain inverse of the completion map.

I made the ring-map notation explicit as `r_{ji}`: the item's `rho_{ji,n}` is a finite-quotient map, so it must not be used as an unindexed map to the completed coefficient ring. The pentagon calculation explicitly considers a fourth field and uses `r_{31}(s) r_{32}(t) u`. These are proof-notation corrections only.

## Existing-node and Mathlib searches

Searched the whole DAG by line/invertible tensor, scalar extension, completion, associativity and evaluation, and searched the whole blueprint with `tools/blueprint_refs.py search` for `invertible tensor`, `completion coherence`, `scalar extension`, `line`, and `tensor scalar`. The ancestor command identifies `det-def-sp-tate-twist-locally-free`. Existing nodes already give all substantial ingredients, so there is no statement-only child to add. In particular:

- `lem-sp-invertible-tensor-scalar-extension` gives powers, duals, associators, unitors and iteration of ring maps on any site.
- `lem-pur-line-unbounded-derived-tensor` gives termwise tensor, the specified evaluation and a triangulated inverse equivalence on arbitrary unbounded complexes.
- `lem-sfb-successive-derived-quotient-normalization` gives the balanced scalar associator, its naturality, representative formula and coherent iteration for arbitrary coefficient maps.
- `lem-weil-finite-free-completed-scalar-comparison` gives exactly the required natural completion map, its cone normalization, invertibility on complete inputs, preservation of completeness and the repeated-field map.
- `lem-galois-equivalence-preserves-limits` is already a Mathlib leaf and provides the product-preservation fact. No duplicate leaf was created.

All six additional searches were made with the prescribed `msearch.py` command and are recorded in `searches.jsonl` and the item, with unchanged query texts. LeanFinder was tried with two different phrasings, as well as LeanSearch, Loogle and two grep patterns. All services answered. Loogle returned zero hits. The natural-language results include free-sheaf formulas, underived sheaf evaluation, ordinary module dual base change, finite-dimensional evaluation, and ordinary adic tensor-completion results. None states this completed derived sheaf coherence. Read Mathlib `Algebra/Category/ModuleCat/Monoidal/Adjunction.lean` (ordinary module extension's monoidal structure and tensor formula), `Algebra/Category/ModuleCat/Sheaf/Free.lean` (the deprecated free-sheaf aliases at 218), and `RingTheory/AdicCompletion/AsTensorProduct.lean` (the finite-Noetherian ordinary-module equivalence at 328). Those results have different objects or omit the strict derived completion and coherence clauses; the item is not a one-line specialization of them.

## Not duplicates

No new nodes. The more restricted `lem-weil-integral-twist-scalar-coherence` concerns Tate lines, constructible inputs and a scheme on which the prime is invertible; it is not used to prove the present arbitrary-line, arbitrary-complete-input statement. `lem-weil-integral-line-tensor-completeness` has an exact Lean interface with extra exactness hypotheses and a separate legacy completeness predicate; this split instead transports the actual Roos triangle, so it does not silently identify those predicates.

## Review by Q44

I read sections B–E of `coord/delivery-errors.md` whole and checked the actual statements of every cited node against the proof, rather than using their titles or their internal proofs. There are no new-node hypotheses or source assertions to audit beyond the unchanged item. Each step is below 2000 characters. The proof's difficult inputs are existing nodes; the conjugation identities are elementary calculations explicitly written in the item, not child nodes restating its clauses.

1. Step 1 uses the powers/dual/iteration statements of `lem-sp-invertible-tensor-scalar-extension` and the slice-linear meaning of `def-pur-sheaf-hom`. The dual formula is evaluated on `b(l tensor t)`, so it has the correct variance and scalar factors. Local bases prove that signed powers remain lines. This step verifies negative and zero powers, not merely positive powers.
2. Step 2 reads `lem-pur-line-unbounded-derived-tensor` for exact termwise tensor, inverse evaluation and unboundedness; `lem-pc-kflat-resolution` for a flat-term representative; `def-pc-kflat-complex` for the acyclic-tensor test; and `lem-pur-kflat-change-of-rings` for flat-term K-flat base change. `lem-pur-derived-change-of-rings` explicitly computes the derived functor on these representatives and preserves quasi-isomorphisms between them. `lem-weil-pbc-site-derived-tensor-descent` explicitly says localization of the flat-term K-flat class is equivalent to the derived category. Thus it licenses descent of the displayed chain isomorphism and its naturality. `lem-pc-sheaf-modules-tensor-closed` supplies the actual sheaf tensor constraints. There is no boundedness or flatness assumption on a general complex being silently introduced.
3. Step 3 uses the normalized associator and coherent-iteration clauses of `lem-sfb-successive-derived-quotient-normalization`; the sheafified tensor and its constraints are the statements of `def-pur-sheaf-tensor-product` and `lem-pc-sheaf-modules-tensor-closed`. Equality is checked on presheaf pure tensors and then localized using the same equivalence as in step 2. Both paths use the given tower equality on the line factor; the evaluation computation gives exactly `r(f(l))s`. These are ordinary chain-level equalities, so no invalid descent test for arbitrary derived arrows is used.
4. Step 4 uses the precise first-map condition in `def-weil-derived-complete`, the triangulated inverse equivalence in the line lemma, the all-limits clause of `lem-galois-equivalence-preserves-limits`, exact countable products from `lem-weil-proetale-countable-products-exact`, and clause 2 of `lem-weil-derived-limit-existence` for derived products represented termwise. These hypotheses hold for the completed coefficient sheaf on this small pro-etale site. The tensor constraints give the displayed reduction-tower map, whose transitions and quotient maps are checked. This proves completeness with the prescribed first map; it does not choose an arbitrary map to a derived limit.
5. Step 5 uses precisely the naturality, complete-input invertibility and complete-output clauses of the finite-free comparison statement. Step 4 supplies completeness of the twisted input. Thus every inverse in beta and in `z` is justified in its actual coefficient category. Completeness of the completed output follows by its isomorphism with the ordinary output. The definition of completeness is invariant under that isomorphism by transporting its triangle.
6. Step 6 quotes the explicit zero shifted-product component in that same comparison statement and the exact strict-cone definition of `def-weil-integral-scalar-extension`. The finite quotient formula is obtained by reducing only the scalar, and its compatibility with transitions is written out. No theorem about uniqueness from projections is being smuggled into this step.
7. Step 7 uses the ordinary square proved in step 3 and the definitions of beta and `z` from step 5. I checked the two resulting expressions have source `B21 B10 T0 K` and target `T2 C20 K`. Naturality moves the inner comparison past beta and the intermediate inverses cancel; the remaining expressions are exactly the ordinary tower square followed by `T2 chi20`.
8. Step 8 uses the ordinary evaluation square from step 3, the defining conjugation from step 5, and naturality of evaluation and chi. Precomposing at `T_-m T_m K` gives the correct ordered source; step 4 makes this chi invertible. Its final expression is `chi_K B(epsilon_K)` on both sides.
9. Step 9 uses coherent iteration of the ordinary associator and the repeated-field clause of the finite-free comparison, both explicitly in their statements. The ordinary pentagon reduces to the one scalar product on a pure tensor; the specified comparisons turn the completed pentagon into that one by cancellation. Its explicit three-arrow comparison makes this transport precise. Multiplication defines the ordinary unit and chi defines the completed unit. The source's repeated-field map is therefore respected even when uniformizers differ.
10. Step 10 uses exactly the constructibility assertion of `lem-weil-integral-scalar-extension-constructible`, the same-objects/localized-Hom formula of `def-weil-rationalization-karoubi`, and the canonical scalar composition stated by `lem-weil-scalar-extension-composition`. Preservation by twists remains the item's conditional hypothesis, not an assertion being inferred from a weaker source. All comparisons are module-linear maps. The construction sends integral representatives by the prescribed integral extension, so the rational comparisons are the canonical scalar comparisons. Naturality on arbitrary localized Hom sums is explicitly checked. No Karoubi completion or new objects are introduced.
11. Step 11 is substitution in the unit square already proved: `T(u) beta = u_T`. Consequently the normalized repeated-field component is identity. Both associator degeneracies follow from the proved unit laws. Conjugating the two equations and then applying rationalization preserves them; this checks the precise normalized, rather than unnormalized, assertion.

Small cases checked: `K=0`; `m=0,1,-1` and arbitrary negative powers; all three fields equal; just one repeated adjacent field; repeated fields with different uniformizers; genuinely ramified coefficient extensions (the proof uses the ordinary completed-ring map and the already normalized same-index quotients, never identifies the two uniformizers); nontrivial line cocycles (the maps use `b`, not a chosen global frame); empty scheme; and unbounded complexes. The integral part does not assume the prime is invertible on the scheme. Rationalization is used only in the coefficient categories specified in the item's conditional final paragraph.

I checked the dependency closures of all proposed substantive citations: none depends on this item. Generic off-unit tools are declared in `split_report.tool_uses`; none replaces the model-purity route. No external source is cited in place of a proof step. Every cited statement has a verbatim quote in `citations.json`. No compiler, Lake, local DAG-check or local preflight command was run.

## Unfinished work

None in the stage-1 split. Independent proof of the existing unsplit tools remains their own queued work, as required by a one-level split.

## Validation

Server `review_split` passed: eleven steps, zero new nodes; declared tool uses accepted. The first full preflight rejected the phrase “the item’s” in step 8 as a standalone-node wording fault (B2); replaced it with “the displayed evaluation formula.” The mathematics and statement are unchanged. Full delivery dry run and push follow this repair.
