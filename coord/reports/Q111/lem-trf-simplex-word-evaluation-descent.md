## Worker report

Group Q111, stage 1, item lem-trf-simplex-word-evaluation-descent, 2026-10-23.

### Files written

- dag/nodes/sec-trace-formula/lem-trf-simplex-word-evaluation-descent.json: the unchanged statement now has a complete five-step elementary proof, status split, proof origin, split report and the additional searches already recorded by Q111.
- citations.json: [] because no proof step invokes another node's theorem or definition. All notions needed for the argument, including the presentation and its congruence, are explicitly recalled in the item's statement. The existing statement dependency remains unchanged.
- report.md: this report and the signed reading below.

### New nodes

None: 0 new nodes and 0 Mathlib leaves. Word recursion, its concatenation induction, the six substitutions, the equality-of-values congruence and the descended functor laws are elementary steps, not separate lemmas.

### Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for simplex presentation, word evaluation and SimplexCategoryGenRel. SimplexPresentationFaithful.lean:248 states only faithfulness of the presentation functor. ModuleCupGodementCosimplicialExists.lean:95 constructs a covariant cosimplicial object for the specific category of module sheaves and Godement operators. Neither states arbitrary-category contravariant word evaluation, so neither can attach this item.

### Literature wanted

WANTED: none. The relevant Stacks source is present.

### Defects and repairs

The item had no proof. Its statement is well typed with its explicit restriction to typed instances and agrees with the evaluation portion of Stacks 016B(2). No statement correction was required. I retained the existing statement dependency on lem-sc-module-cup-godement-simplex-presentation-faithful as the identification of the presentation being discussed; its faithfulness conclusion is not used. I supplied the argument omitted by the cited universal-presentation passage rather than assuming the whole reconstruction theorem. The proof is marked agent-written because these elementary details are an expansion of the abbreviated source proof.

The sandbox initially contained searches.jsonl but no item copy or report. I read and reused its four records, preserving the item's earlier Q138 search history as well. They are precisely the grep query "def lift|theorem lift|lemma lift|SimplexCategoryGenRel" in CategoryTheory/Quotient.lean; the LeanSearch query "construct a simplicial object from objects face and degeneracy maps satisfying the simplicial identities"; Loogle "CategoryTheory.Quotient.lift"; and the LeanFinder query "Contravariant evaluation of coface and codegeneracy words satisfying the simplicial identities factors through the category presented by the simplex relations". No unrun search is claimed.

I read Quotient.lean:230-300, PathCategory/Basic.lean:90-145, and SimplexCategory/GeneratorsRelations/Basic.lean:190-270 for the relevant hits. Quotient.lift still requires a functor and the proof of compatibility with all relations; Paths.lift alone does not descend; toSimplexCategory is the particular covariant functor to the ordinal category. Definitions of simplicial objects and the individual simplicial identities from the semantic searches do not supply the prescribed arbitrary-category evaluation. The earlier item searches include alternate phrasings and reach the same candidates. Hence the item is not a one-line Mathlib specialization.

### Unfinished work

None in this one-level split. No Lean was written or compiled.

## Not duplicates

No new-node pairs arise. The whole DAG was searched for 016B, 0168, word evaluation, category congruences, quotient categories and path functors. Blueprint searches for "simplex", "word evaluation" and "category congruence" returned, respectively, only def-weil-pbc-finite-split-hypercover, no nodes, and no nodes. That hypercover definition does not state this evaluation theorem. The existing lem-coef-category-quotient-relations is a Mathlib leaf about quotient category construction, which I opened and read; the argument here needs only the least-congruence definition already in the item's statement, and proves its descent directly. No duplicate or off-unit tool node was created or invoked. The presentation-faithfulness and unique-lifts nodes do not state this item's result.

## Review by Q111

I read literature/stacks-project/simplicial.tex at lemma-face-degeneracy-category (Tag 0168), lemma-characterize-simplicial-object (Tag 016B), and the surrounding generator relations. The former states the universal presentation and omits its proof; the latter's part (2) reconstructs a simplicial object from exactly these opposite identities, and its proof refers to the former. Our item is the earlier stage, evaluation on the presented category P, and does not need the harder identification P = Delta. All degrees, the arbitrary ordinary category, and all face and degeneracy hypotheses are retained. The identity clause is treated as two relations, giving six checks in total.

I opened the statement of lem-sc-module-cup-godement-simplex-presentation-faithful. It recalls the same category P and proves faithfulness of J. I did not take a universal property or any word-evaluation theorem from that faithfulness assertion. I also read the full statements of lem-trf-simplicial-operators-reconstruction, lem-trf-simplex-presentation-unique-lifts and lem-coef-category-quotient-relations to distinguish their conclusions and avoid a cycle or accidental appeal to the parent reconstruction. No proof step cites any of them. Thus citations.json is genuinely empty, not a substitute for missing quotation evidence.

For step 1, I checked the direction explicitly: a:[m] to [n] is evaluated to U_n to U_m, and appending a on the left of a word evaluates by composition with v(a) on the right. Empty and one-letter words give the required identity and generator values. The recursion is on finite word length and introduces no existence theorem or external node.

For step 2, I checked both induction cases for concatenation: an empty q uses the identity law, and q=a composed with q' uses the induction hypothesis and category associativity. This proves the general formula rather than assuming anti-functoriality as a black box. The words remain composable at every induction step. This step has no cited statements because the displayed induction is its entire argument.

For step 3, I compared each displayed image pair against its corresponding hypothesis. The face-face relation reverses to d_i composed with d_j = d_(j-1) composed with d_i. The low mixed relation reverses to d_i composed with s_j = s_(j-1) composed with d_i. The two adjacent relations give d_j composed with s_j = 1 and d_(j+1) composed with s_j = 1 separately. The high mixed relation reverses to d_i composed with s_j = s_j composed with d_(i-1). Finally the degeneracy relation reverses to s_i composed with s_j = s_(j+1) composed with s_i. The inequalities are unchanged. These are substitutions of the item's hypotheses, without any uncited simplicial theorem.

For step 4, I checked reflexivity, symmetry and transitivity come from equality in the fixed Hom set D(U_n,U_m). For a contextual relation b composed with w composed with a, its value is V(a) composed with V(w) composed with V(b). Substitution of V(w)=V(w') therefore proves stability under both contexts, not just one. The congruence is the least composition-stable equivalence relation containing the listed relations by the statement's definition of P; inclusion in the explicitly constructed relation R is consequently definitional. This does not use an unquoted quotient-descent theorem. It is an elementary congruence argument, with all closure properties checked in the text.

For step 5, I checked representative independence uses precisely step 4. An arrow w:[m] to [n] represents an opposite arrow [n] to [m], which is sent to V(w):U_n to U_m. The formula V(q composed with p)=V(p) composed with V(q) from step 2 is exactly preservation of composition in the opposite category. The empty word and singleton word computations prove the remaining functor and generator clauses. No conclusion is left to a node that merely restates the item.

I checked degree zero explicitly: there are no faces with source U_0, while s_0:U_0 to U_1 is allowed and the two mixed identities d_0 composed with s_0 = d_1 composed with s_0 = 1_(U_0) have precisely the stated types. The smallest degeneracy relation is s_0 composed with s_0 = s_1 composed with s_0 from U_0 to U_2; the smallest face-face relation is from U_2 to U_0. Boundary indices never call an operator outside its declared range because relations are only imposed when typed. Empty contexts in step 4 reduce to the identity case, and the terminal category gives a consistent degenerate example. No cancellation, faithfulness, invertibility, additive structure or commutation of arbitrary operators is used.

I read the chapter and unit records and the current literature/blueprint/latest chapter, unit, and lem-trf-local-term-locality statement and proof (snapshot 7284bb09daf97437d544c51882b325f9c52cd345). The inherited blueprint.from.place describes the standard-resolution/reconstruction auxiliary chain below that ancestor. This split supplies only its terminal word-evaluation component and changes no chapter or unit route. I checked delivery-errors B through E: no new nodes need statement-only or search repairs; no citation takes content from another node's proof; no non-elementary fact or circular parent reconstruction is hidden; the variance, source and target degrees and six index conditions match. All five steps are below 2000 characters. This is the direct-delivery worker's own reading, with the maintainer's independent review still to follow.
