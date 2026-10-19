# det-sp-unique-right-adjoint — stage 1

1. Files written

- `dag/nodes/sec-smooth-purity/det-sp-unique-right-adjoint.json`: existing statement, now a Mathlib leaf, statement unchanged. Match: `CategoryTheory.Adjunction.rightAdjointUniq` with the transpose, inverse-component and counit lemmas listed with source lines in `mathlib_match.how`.
- `citations.json`: empty list, because a Mathlib leaf has no proof steps or DAG-node citations.
- `report.md`: this report. No new nodes; one Mathlib leaf (the item). `searches.jsonl` is the search command's own log.

2. Attachments

None. I searched the read-only slopmaster2 and master `WeilConjectures/` trees for the blueprint id, uniqueness/right-adjoint terminology, and the upstream declaration-name index. The hits concern particular geometric functors or derived functors, not this generic theorem with its arbitrary-family uniqueness clause. No project declaration was used as an attachment. Master was only reference material.

3. Wanted literature

None. I read the current main-20261015 statement and all four paragraphs of `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-unique-adjoint/sk-prop-sp-unique-adjoint-categorical.proof.md`, its `_section.md`, and the enclosing proposition's proof. I also read Stacks `literature/stacks-project/categories.tex`, Tag 0037 (`definition-adjoint`, especially the paragraph giving the unit/counit formulas for the Hom bijection), and Tag 0B65 (`lemma-transformation-between-functors-and-adjoints`). These confirm the convention for transposes and counits. The leaf match itself was checked in the pinned local Mathlib source, not inferred from search-service summaries.

4. Findings and changes

The imported statement is correct as written. Its four imported proof steps had `elementary: null` and did not name the adjunction machinery; the entire statement is already covered by Mathlib, so keeping a split would create unnecessary work. I removed those steps and retained the blueprint source and every imported metadata field. The first dry run rejected a null `proof_origin` even though this is a Mathlib leaf; I restored the agent-written blueprint proof provenance with its exact companion proof-file path. This bibliographic field does not replace the checked Mathlib match or add proof dependencies.

Mathlib source read: `Mathlib/CategoryTheory/Adjunction/Unique.lean`, lines 102–140, and `Mathlib/CategoryTheory/Adjunction/Basic.lean`, lines 159–182. All named declarations occur in those files. Mathlib composes left to right (`a ≫ b`), so its `F.map a ≫ counit` is precisely the blueprint's `counit ∘ F(a)`; no coefficient-category or geometric identification is involved.

The imported item has neither `chapter` nor `unit`, and there is no `dag/units/sk-prop-sp-unique-adjoint.json` in this snapshot. I read `dag/chapters/sec-smooth-purity.json` and the actual current blueprint unit `_section.md`. I did not invent or edit maintainer-owned bindings. This leaf does not replace a unit route by a different geometric argument.

Blueprint-wide searches using `tools/blueprint_refs.py search` for right-adjoint and counit terminology, and DAG text searches, found the enclosing specialized proposition, `det-sf-existence-brown` (a specialized clause), and `lem-trf-adjoint-mate` (triangulated categories and an isomorphism of left adjoints). None is a second node with exactly this general statement and its uniqueness of arbitrary families. Accordingly `blueprint.same_as` is `[]`; `blueprint.from` remains null for this imported blueprint node. No new definitions or statements were introduced.

Every Mathlib search in the JSON is an executed `msearch.py` query. Two early grep calls supplied an extra `Mathlib/` prefix in the optional subdirectory and returned no hits; the records say so, and the corrected `CategoryTheory/Adjunction` searches found the declarations. One Loogle pattern used the unqualified identifier `Adjunction.rightAdjointUniq` and returned an unknown-identifier diagnostic; the record preserves it. A single-file grep output had misparsed line prefixes; the file was read directly to resolve them. LeanFinder, LeanSearch, fully qualified Loogle and corrected directory greps all worked. No search outage is represented as a negative result.

5. Unfinished work

None for this stage-1 item. No Lean was written or compiled, no compiler/Lake/build tool was invoked, no git command was run in the shared repository, and nothing was pushed. The second reader must review the leaf match and deliver it.

## Not duplicates

No new nodes. The existing item is recognized directly as a Mathlib leaf.

## Review by NZ

I checked the item against its current blueprint statement and proof, then checked each logical clause against the actual pinned Mathlib statements and definitions. The precise identification is as follows.

For the blueprint's first paragraph (Transposes), `Adjunction.homEquiv` at Basic.lean:160 is an equivalence, with inverse exactly `a ↦ F.map a ≫ counit` at line 163. Thus the prescribed gamma and delta exist uniquely for every object, with no further representability assumption. `homEquiv_symm_rightAdjointUniq_hom_app` at Unique.lean:105 states that the inverse J-Hom equivalence of the canonical component is the G-counit. It therefore identifies the canonical component with exactly the gamma in the item, rather than merely some isomorphism between its endpoints.

For the second paragraph (Naturality), `rightAdjointUniq` at Unique.lean:102 returns an isomorphism in the functor category. Its hom and inv are natural transformations, so after the preceding component identification the given gamma and delta are natural. No Yoneda or mate theorem is being silently cited as an additional DAG node.

For the third paragraph (Inverse), `rightAdjointUniq_inv_app` at Unique.lean:138 identifies the inverse component with the canonical hom component obtained by swapping the adjunctions. Apply the same transpose theorem with G and J exchanged: this is precisely delta, with its specified G-transpose. The two inverse identities are the fields of this functor-category isomorphism. This checks both directions, rather than assuming the reverse comparison equals the inverse.

For the fourth paragraph (Uniqueness), let a(K) be any family satisfying the counit equation. The inverse J-Hom equivalence sends both a(K) and the canonical component to the very same G-counit, by Basic.lean:163 and Unique.lean:105 (also the explicit counit equation at Unique.lean:127). Injectivity of that equivalence gives equality for each K. This argument does not assume a is natural or invertible, so it covers the item's stronger parenthetical clause. This is a one-line use of equivalence injectivity, not a missing categorical theorem.

The only hypotheses of the cited Mathlib declarations are categories, the functors of the indicated variance, and the two chosen adjunctions. They are exactly the item's data. In particular I did not add smallness, faithfulness, fullness, triangulated structure, coefficient restrictions, or compatibility between the two chosen adjunctions. I tested the identity functor with identical adjunctions (the canonical comparison is the identity), the same underlying right adjoint with different adjunction counits (the comparison need not be the identity, so the counits must stay part of the data), and empty categories whenever the functors/adjunctions exist (all objectwise clauses are vacuous). The argument works in each case and nowhere cancels F as if it were faithful.

Against delivery-errors B–E: this delivery creates no new node and therefore no statement-only, tag-overlap or relabelling issue. All of the non-elementary content is in the explicitly named Mathlib declarations; the sole extra inference is injectivity of an equivalence. The item has no proof-step citations, so C1/C4 cannot conceal an unstated result in another node; `citations.json` is empty for that reason. There are no DAG dependencies or possible new cycles. I corrected the initial grep-directory mistakes in the searches, preserved their actual negative outputs, checked every line reference in the match against the source, and left the mathematical statement untouched.


## Second reading by NZ

- Item statement: checked verbatim against main-20261015 `sk-prop-sp-unique-adjoint-categorical.md`, its four-paragraph companion proof, and the chosen-adjunction/counit convention in Stacks 0037 (`categories.tex`, `definition-adjoint`, lines 3343–3390); PASS, identical hypotheses and conclusion. Stacks 0B65 (`lemma-transformation-between-functors-and-adjoints`, lines 3541–3578) also confirms the direction of the counit equation.
- Step 1 (Transposes, source paragraph 1; no delivered DAG proof step): checked Basic.lean:160–171 and Unique.lean:105–108; PASS, the inverse Hom equivalence is exactly `a ↦ F.map a ≫ counit`, so its bijectivity supplies the stated unique gamma and delta without extra assumptions.
- Step 2 (Naturality, source paragraph 2; no delivered DAG proof step): checked Unique.lean:102–103 and the component identification in :105–108; PASS, `e.hom` and `e.inv` are natural transformations. Explicitly, counit naturality gives epsilonJ(K') F(Ju) F(gammaK) = u epsilonJ(K) F(gammaK) = u epsilonG(K), while epsilonJ(K') F(gammaK') F(Gu) = epsilonG(K') F(Gu) = u epsilonG(K); injectivity gives gamma naturality. For delta, epsilonG(K') F(Gu) F(deltaK) = u epsilonG(K) F(deltaK) = u epsilonJ(K), while epsilonG(K') F(deltaK') F(Ju) = epsilonJ(K') F(Ju) = u epsilonJ(K); injectivity gives delta naturality.
- Step 3 (Inverse, source paragraph 3; no delivered DAG proof step): checked Unique.lean:138–140 and :105–108 with `adj1 = adjJ`, `adj2 = adjG`; PASS, the G-Hom inverse sends `e.inv.app K` to `adjJ.counit.app K`, hence it is delta. Both inverse identities are fields of `e`. Directly, epsilonG F(delta gamma) = epsilonJ F(gamma) = epsilonG, and epsilonJ F(gamma delta) = epsilonG F(delta) = epsilonJ; the respective inverse Hom equivalences send the identity to the same counit, so injectivity proves both identities.
- Step 4 (Uniqueness, source paragraph 4; no delivered DAG proof step): checked Basic.lean:163 and Unique.lean:105–108, :127–130; PASS, every compatible `a(K)` and `e.hom.app K` have the same inverse J-Hom image, hence are equal by injectivity. No naturality or invertibility of the competing family is assumed.
- New nodes: NONE; B1–B7 and removal of unnecessary new nodes are vacuous. The sole changed existing node is the item, a Mathlib leaf; its declaration, file and line references were independently read in the pinned local Mathlib source. No DAG proof citations occur, so `citations.json = []` is correct and there are no new dependency edges.
- Duplicate and attachment review: independently searched the full blueprint and DAG for right-adjoint terminology, and the read-only slopmaster2/master project sources for the item and `rightAdjointUniq`; PASS, the closest imported `lem-trf-adjoint-mate` assumes exact functors between triangulated categories, while `det-sf-existence-brown` clause 3 specializes to geometric functors. Neither replaces the present general statement. Project hits use the Mathlib construction for specific tensor, scalar or geometric adjunctions; master is reference material only. Independent differently phrased LeanFinder and local grep searches are preserved in `searches.jsonl` and recorded with their actual results in the item.
- Edge cases: PASS for the empty categories (objectwise assertions vacuous), the terminal category (all maps forced), and the identity functor on vector spaces over a field with two adjunctions having nonzero scalar counits a and b: gamma is multiplication by a/b and delta by b/a, so counit compatibility and both inverse identities hold even for distinct adjunction structures on the same functors; the zero vector space causes no exception. No numeric n or scheme hypothesis occurs in this categorical statement.

Changes: expanded the inverse-component identification in `mathlib_match.how` into the explicitly instantiated transpose equation, removing the compressed swapped-adjunction argument (E5); added independently executed search records and this second-reading audit. The statement, leaf classification, original review sections, and empty citations were retained. No new nodes, Lean files, compiler invocations, or live-project/launcher writes.
