# Worker report

## Files written

- dag/nodes/sec-poincare-duality/lem-pod-reindexing-completion-unit-tensor.json: statement, split into eight proof steps using existing nodes. Mathlib searches give no match for the entire assertion.
- citations.json: one verbatim statement extract for each cited node in each proof step.
- No new nodes, Mathlib leaves, unit records or Lean files.

## Attachments

None. Searches of lean/WeilConjectures by the blueprint tag and by reindexing/completion/strict-tower/Roos concepts found no declaration stating the item. Existing Roos and tensor code covers different general constructions, not this full normalization assertion. No compiler or Lake command was run.

## Wanted

None. The blueprint proof, Stacks sources and the needed DAG statement interfaces are present locally. The enhancement is an agent proof, not attributed verbatim to the blueprint or Stacks.

## Audit findings and changes

The imported item was statement-only. Its mathematical statement, statement dependencies, creation metadata and blueprint ancestry are unchanged. The source blueprint has brief automorphism-operation assertions in Steps 1 and 5; it does not prove the enlarged strict-system and two-coordinate normalization. The split now gives that argument explicitly. There is no established statement error and no statement weakening.

The canonical comparison is checked on whole system maps and on both cone coordinates. Equality of finite evaluations or projections alone would not identify a morphism in the derived system category; the proof instead transports the actual derived adjunction and compares representative-normalized natural transformations. No countable-product exactness is assumed without its pro-etale-module theorem. No K-injectivity of arbitrary reductions or tensor exactness from flat cohomology is used. Completeness is used only for the quotient unit and the completed-operation domain.

Blueprint searches: tools/blueprint_refs.py ancestor identified prop-pod-dual-tate-data-compatibility through lem-pod-derived-automorphism-hom-evaluation; searches for reindexing, derived limit and pullback tensor found no blueprint node stating the whole item. Whole-DAG searches found the existing resolution, exact-product limit, quotient-unit and total-tensor lemmas used here; these are reused instead of introducing duplicate lemmas. The item is not the key statement of sk-def-weil, so the unit realization fields are not changed. Generic off-unit tools are declared in split_report.tool_uses; the geometric route remains the automorphism pullback/tensor route of the blueprint.

Mathlib: the actual new leanfinder, loogle, leansearch and grep calls are in searches.jsonl. A second semantic phrasing was read. AdicCompletion results concern ordinary module completion, Pi.equivalenceOfEquiv concerns families of categories, and site-equivalence and sheaf-pullback hits do not state the derived quotient-unit/completed-tensor assertion. The source of ofTensorProductEquivOfFiniteNoetherian_symm_of (AsTensorProduct.lean:344) and the Pi reindexing construction (Pi/Basic.lean:323ff) were read to exclude these as whole-item matches. The earlier searches in the item were retained unchanged as inherited history, not presented as new calls by NN.

## Not duplicates

No new nodes were created. In particular, lem-pod-reindexing-hom-resolution-model supplies ordinary coefficient-module reindexing and its resolution invariants; lem-cbc-exact-product-functor-strict-limit supplies the generic total-limit/Roos comparison; lem-weil-finite-free-completed-scalar-comparison supplies the quotient-completion unit at L=E. None was copied into a new node. The item adds their assembly with the actual reduction/limit adjunction and the specified completed tensor comparison.

## Review by NN

I read the current blueprint's prop-pod-dual-tate-data-compatibility proof in full, especially its Steps 1 and 5. I also read Stacks sites-modules.tex lemma-tensor-product-pullback (03EL), sites-cohomology.tex lemma-pullback-tensor-product (07A4), and lemma-derived-limit-is-ok (0941), including their proofs. The Stacks tensor argument specifically replaces the inputs by flat-term K-flat complexes and totalizes the underived comparison; the derived-limit argument uses K-injective towers, not an arbitrary cone choice. These distinctions determine this split. There are no new nodes whose sources need a separate audit.

For step 1 I opened lem-pod-reindexing-hom-resolution-model and used exactly its coefficient identifications, exact equivalence, product/colimit preservation and K-flat/K-injective preservation. The strict semilinear category and componentwise exactness are stated in lem-coef-derived-system-evaluation-calculus. Extending the equivalence to systems is componentwise and reverse reindexing is its inverse. The K-injective argument for systems is written out using the null-homotopy criterion of def-pur-kinjective-complex; I do not silently apply a module-only preservation statement to the system category.

For step 2 I checked lem-pc-kflat-resolution supplies flat terms even for unbounded inputs, and the same-unit reindexing lemma preserves both properties. The derived-system calculus explicitly supplies a functor represented by the strict quotient system. The generator computation checks all quotient transitions before descent, so the comparison does not require conservative evaluation to manufacture an unproved lift.

For step 3 I checked the hypotheses of lem-cbc-exact-product-functor-strict-limit one by one: both categories are module sheaves on small pro-etale sites, countable products are exact by lem-weil-proetale-countable-products-exact, and F is additive, exact and product-preserving by the same-unit reindexing lemma. The cited comparison explicitly states its resolution normalization, both product coordinates, projections, connecting map and augmentation equation. I checked its (x,y) signed convention against the usual shifted-cone convention (y,x): (x,-y) converts the two. The diagonal product map is unaffected by this conversion. The n-th component calculation proves the 1-s square, with no boundedness assumption.

For step 4 I reread the actual adjunction, unit and counit clauses of lem-coef-derived-system-evaluation-calculus. The ordinary transpose p tensor b maps to b h_n(p) and its inverse respect the entire compatibility condition. Applying exact equivalences to the source and target resolution models gives equality of the derived Hom bijections. Units and counits are transposes of identities. This supplies actual system-map equality, stronger than merely checking their evaluated maps; it uses no assertion that finite projections determine a derived morphism.

For step 5 I read the L=E clause and zero shifted-coordinate normalization in lem-weil-finite-free-completed-scalar-comparison. The field extension is the identity, and K has exactly its required derived-completeness hypothesis; no constructibility is needed. The actual unit clause of the calculus and the augmentation clause of the generic limit lemma identify this map with the pulled quotient augmentation. def-pur-integral-derived-operations states that completed pullback is the limit of the finite pulled reduction tower. Hence the displayed two-isomorphism composite has the required source, target, direction and projections.

For step 6 I read lem-pur-kflat-change-of-rings and lem-pur-kflat-total-tensor-model, which apply to arbitrary sheaves of commutative rings and possibly doubly unbounded complexes. These statements supply valid derived reductions and a valid total tensor, respectively. def-pc-tensor-complex-sheaves supplies the direct-sum degree formula and (-1)^p differential. The reindexing lemma preserves the needed direct sums. I explicitly checked the two differential terms and both quotient-transition composites on each tensor summand.

For step 7 I opened def-pur-integral-derived-operations, lem-pur-integral-operations-well-defined and def-pur-completed-pullback-tensor-comparison. The first gives exactly the limit of the tensor-reduction system; the second gives functorial representative identifications and independence; the third fixes the canonical comparison on the same representatives and both Roos coordinates. Thus the equality is justified by that full defining representative square and the adjunction comparison, not by finite evaluations alone. The ordinary reindexing of the completed tensor is therefore invertible, with reverse reindexing as inverse.

For step 8 I read the associativity/symmetry clauses of lem-pur-isomorphism-inverse-image-tensor-hom and the whole-expression and substitution clauses of lem-pur-completed-operation-tower-substitution. I checked the latter's normalized-input hypothesis using lem-pur-normalized-actual-reconstruction-maps, which states that every simultaneous reduction system is normalized and that its reconstructed limit is complete. This also ensures the completed tensor objects fall in the completed domain when comparing them with pullback in step 7. The proof writes the homogeneous symmetry sign and the cone-shift sign explicitly; reindexing preserves both. Identity and composition use the same section relabeling and quotient-normalized coefficient maps. Taking limits of these entire system equations gives the specified completed constraints, as the substitution theorem asserts.

I checked delivery-errors B through E against the split. Every non-elementary imported fact has a node citation and every citation has a literal statement quote. No new node is elementary, duplicate, a restated clause, or an unsearched potential Mathlib leaf because no new node is created. No step exceeds 2000 characters (maximum 1544), and no hidden comparison lemma was moved out merely to relabel the item. Small cases checked: empty schemes and zero objects give zero complexes; g=id gives identity relabeling and the actual completion unit; n=1 still has the same quotient tensor maps; degree-zero representatives give ordinary tensor balancing; negative and odd shifts preserve the explicitly displayed signs; doubly unbounded complexes use direct-sum totalization and exact countable products. The proof does not claim an incomplete K has an invertible unit.

## Unfinished work

None in this one-level split. Existing unsplit dependencies remain their own items. Maintainer independent mathematical review remains part of the delivery process.

## Validation

The server-side review_split check passed. The first full deliver.py --no-push completed successfully at c155d42c68e with server preflight passed. Every citation quote was also checked locally for exact containment in the cited statement, and every proof-step use has a quote. The final dry run is repeated after this report update before pushing.
