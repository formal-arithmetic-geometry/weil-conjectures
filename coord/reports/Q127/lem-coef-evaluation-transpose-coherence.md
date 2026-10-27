# Q127: lem-coef-evaluation-transpose-coherence

## Files written

- `dag/nodes/sec-six-functors/lem-coef-evaluation-transpose-coherence.json`: statement item, now split into eleven explicit calculations. The original statement is unchanged. No new nodes and no Mathlib leaves were created.
- `citations.json`: sixteen step/node citations, with quotations copied verbatim from the existing statements.
- `searches.jsonl`: actual wrapper search records; these searches are also appended to the item's existing search history.
- `report.md`: this report.

## Attachments

None. Searching the live `lean/WeilConjectures/` by the blueprint tag, evaluation/transpose terminology, and internal-Hom comparison names found partial results in `Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean` (the project extension, not Mathlib itself). In particular `CategoryTheory.Functor.LaxMonoidal.ihomComparison_ev`, `ihomComparison_app_eq_curry`, `ihomComparison_comp_app`, `ihomComparison_app_comp_map_app` and `map_pre_app_comp_ihomComparison_app` cover several relevant laws. They do not together state every clause of this item: the internal-Hom composition identity and the specified arbitrary-transpose compatibility are not declarations identified by that search. Module-object transpose-pairing and the adic pullback comparison have additional hypotheses and different conclusions. I therefore make no exact-attachment claim.

## WANTED

None. The source named by the item is present in the master blueprint. The corresponding path is absent from the current main-20261015 snapshot; the item has no blueprint_update, and its current parent still binds the master source and expressly uses this abstract lemma in its step 4. I read that parent and retained this binding rather than invent a replacement source.

## Problems found and changes

The item was an unsplit extracted argument, with no proof. I supplied the uncurrying calculations rather than moving its clauses into new nodes. No statement dispute or missing hypothesis was found. The proof explicitly keeps the associator in the internal-composition equation. It first proves the composite-functor identity and then checks monoidal-natural-isomorphism transport by cancelling the tensor of h_K; this fixes the inverse and variance without assuming that an internal-Hom comparison is invertible.

The argument is agent-written, expanding the final paragraph of the item's blueprint source. Stacks categories.tex, Tags 0FFK (definition-monoidal-category) and 0FFL (definition-functor-monoidal-categories), supplies the structural conventions, not an unquoted coherence theorem. There is no appeal to strictification or to a general coherence theorem. The explicit associativity axiom is enough.

## Search record and existing nodes

I ran blueprint_refs.py ancestor and searches for “currying”, “strong monoidal”, “evaluation transpose” and “successive coefficient”, and searched the whole DAG by the tensor-Hom, closed-category, adjunction and comparison terminology. The ancestor is thm-coef-finite-hom. I read the statements of lem-pod-closed-uncurry-laws, lem-sfb-adjunction-transpose-square, lem-coef-closed-adjunction-naturality, lem-coef-closed-adjunction-enriched-isomorphism, lem-trf-closed-evaluation-naturality, lem-sfb-monoidal-adjunction-mates and lem-sfb-internal-scalar-mate-transitivity. None duplicates the item. In particular the two coef adjunction lemmas assume an adjoint to F, which this item does not assume; the uncurry leaf uses tensor-left conventions. No such extra hypothesis or change of convention enters this proof.

The required msearch wrapper was used for two LeanFinder phrasings, Loogle, grep and LeanSearch; all five completed successfully. Their exact queries and results are in searches.jsonl and mathlib_searches. I read Mathlib Closed/Functor.lean:44–110: the comparison hits assume CartesianMonoidalCategory, which an arbitrary symmetric monoidal category does not satisfy. Mathlib Closed/Basic.lean:150–194 contains individual curry/uncurry identities. The second LeanFinder phrasing also returned rigid tensor-Hom equivalences (which require ExactPairing), and compTranspose. These do not supply this item for arbitrary objects and functors. Thus the item remains a split, not a Mathlib leaf.

## Not duplicates

No new nodes, hence no new/existing pairs or shared-tag collision to justify. The existing monoidal-category and strong-monoidal-functor definitions are reused directly.

## Review by Q127

I read the chapter and unit records, GOAL.md, the worker/stage-1 contracts, the three-level route requirements and both copies of delivery-errors.md B–E. The unit has no proof-step list to realize here, and this extracted coherence lemma is not its key statement. I read the full master blueprint source thm-coef-finite-hom.md, especially its last paragraph, and the current parent's five-step split. This work serves precisely the parent's evaluation, composition and successive-coefficient-change step. For the only structural sources I read categories.tex around definition-monoidal-category and definition-functor-monoidal-categories and checked their tags in tags/tags. There are no new-node sources.

For each proof step I checked the following mathematical content against the cited statements and the assumptions actually available:

1. def-sfb-monoidal-category supplies tensor as a bifunctor; def-nagata-category supplies associative composition. The stipulated natural adjunction bijections themselves give the inverse-evaluation formula and the displayed three-variable naturality equation. I derive that equation by applying the bijection, rather than quote another node for a stronger statement than it has.
2. def-sfb-strong-monoidal-functor really gives the tensorator from FV tensor FK to F(V tensor K), in the direction needed for the definition of v. Applying the inverse bijection proves evaluation and uniqueness. No invertibility of v is used.
3. The tensorator naturality formula in that same node, with the first morphism a-sharp and second the identity, is exactly the middle equality displayed. Cancellation of transpose/uncurry is available from step 1.
4. The naturality equation is applied to H(1,b) tensor 1; tensorator naturality then gives the displayed F(b) composite. All morphisms have source F H(K,M) tensor FK and target FM'.
5. The same tensorator equation is now applied in both factors, with a:K' to K and H(a,1) in the contravariant Hom slot. The two uncurried maps have source F H(K,M) tensor FK' and target FM. The direction of a is checked explicitly.
6. Both structural nodes were read in full: def-sfb-monoidal-category has alpha from (A tensor B) tensor K to A tensor (B tensor K), and def-sfb-strong-monoidal-functor states exactly the displayed associativity equation for s^F. The definition of internal composition in the item's hypothesis is expanded by two evaluations. No theorem about composition is cited without a statement.
7. The strong-functor node's tensorator naturality is used with mu_C as an ordinary morphism. This calculates the left side's uncurry, not a new assumption about preservation of internal composition.
8. Naturality of alpha is in def-sfb-monoidal-category, and tensorator naturality and associativity are in def-sfb-strong-monoidal-functor. After substituting the two evaluation equations, the displayed intermediate formula rewrites to exactly step 7, with the same parentheses. The proof here has fewer than 1000 characters; it is one direct rewrite calculation, not a concealed comparison lemma.
9. The composite tensorator is written down, and the cited strong-functor node supplies the naturality used to move G(v^F) across t^G. The final expression is the defining evaluation for GF. The source is GF H(K,M) tensor GFK, so no unmentioned associator between categories is required.
10. h's monoidality and naturality are hypotheses, and their exact equations are written down before use. def-sfb-monoidal-category supplies tensor bifunctoriality, giving the explicit inverse of 1 tensor h_K; def-nagata-category supplies cancellation by composition with that inverse. The second equality uses H(h_K inverse,h_M), with its contravariant argument going from JK to GFK as required. The result follows by two cancellations, never by cancelling v.
11. The canonical identity monoidal structure has identity tensorator, and step 1 identifies the uncurry of the identity with evaluation. The cited structural definitions are sufficient, and uniqueness closes this last case.

Every step's citations are quoted in citations.json; their statements say precisely which structural data or axiom is used. Every other operation is a substitution into the assumed natural adjunction, or functor/tensor bifunctoriality. Therefore each step is marked elementary: each is a direct short calculation with no black-box lemma. All proof steps are below the 2000-character review threshold. No proof dependency leaves the unit for a non-definition tool; all three dependencies are existing Mathlib definitions.

I checked the small cases: the identity functor forces v to be the identity; zero modules and zero morphisms in module categories cause no cancellation failure because only the adjunction bijection is cancelled; tensor extension from Z-modules to F_2-modules is strong symmetric monoidal, and K=Z/2, M=Z gives the noninvertible comparison 0 to F_2. The proof still applies in that example because it never inverts v. For two successive scalar extensions its tensorator order agrees with (x tensor b) tensor c mapping to x tensor bc. These checks test the potentially problematic missing-dualizability and inverse-variance issues.

B–E self-check: no new-node schema or source issues; no per-degree derived reformulation; no fabricated searches; no copied clause nodes; all citations read and quoted; no circular or missing node; no source statement changed; no unsupported exactness, rigidity, adjoint to F, or invertibility used. I corrected the initial citation selection for step 6 to include the actual associativity formula, instead of quoting only naturality from the same node.

## Unfinished work

None in the split. Required server checks and delivery results are recorded below after they run.

## Validation

Server review_split passed with 0 new nodes. The full deliver.py --no-push invocation exited successfully and printed `OK (not pushed)` at 035b2f9ee3b, with maintainer preflight passed. An independent local JSON comparison confirmed that the statement and all maintainer-owned fields are unchanged, that the proof dependencies are exactly the union of step uses, and that every one of the sixteen citation quotations is a verbatim substring of the cited live statement. No Lean was written and no compiler, Lake or build command was run.
