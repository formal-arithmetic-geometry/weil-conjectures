# Worker report: lem-sp-strict-line-heart-assembly

## Files written

- dag/nodes/sec-smooth-purity/lem-sp-strict-line-heart-assembly.json: statement node split into five proof steps; no full Mathlib match. The statement, original citations, original searches and blueprint provenance are retained.
- citations.json: one verbatim statement quotation for every step/node citation (16 entries).
- report.md: this report. searches.jsonl is the search command's own log.

New nodes: 0. Mathlib leaves added: 0. No unit realization is edited: this auxiliary created node is not its unit's key statement.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint id and the strict-line/heart/tower notions found no declaration stating this item. The NormalizedTower module concerns normalized tower realization, not this lifting theorem. No Lean file was written or compiler run.

## WANTED

None. The argument uses sources already in literature/ and existing DAG statements.

## Errors and corrections

The imported node had no proof; its assertion that the maps lift needed the reduction-to-transition argument. The proof now explicitly transposes the derived reduction equality and records that the target is restricted to the source coefficient ring. It never treats the quotient R_n -> R_m as flat. No statement dispute or change of hypotheses was necessary.

The source metadata of the existing ordinary-adjunction tool lem-pur-sheaf-ring-coefficient-ordinary-adjunction lists 03D7 and 03DA. Its stated scalar Hom formula is the one needed here, but the direct scalar-tensor adjunction source is Stacks 03CZ, sites-modules.tex, lemma-adjointness-tensor-restrict (read at lines 933 onward). The item step records this direct tag. The other existing node is not edited.

## Unfinished work

None in this one-level split. Existing dependencies retain their own states; this delivery does not claim to complete their proofs or the Lean theorem.

## Not duplicates

No new node is proposed, so there are no new/existing pairs. The DAG search found and reuses the existing single-degree concentration, single embedding, exact derived cohomology, system-level evaluation, locally-free scalar, and normalized scalar Hom tools. Whole-blueprint searches included heart, concentrated, strict, single-degree, shifted line orientations, and rank-one tower sheaves; no imported blueprint node states this lifting theorem in another form, so same_as remains [].

## Mathlib searches

The five Q146 calls in searches.jsonl were run and their returned hits read; every query is appended verbatim to the item's existing search history. LeanFinder's second formulation found DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE, while Loogle found the singleFunctor full/faithful instances and its cohomology comparison. These are already represented by lem-sf-derived-concentrated-single and lem-weil-pbc-derived-single-fully-faithful; they do not state the strict semilinear transition and prescribed-evaluation clauses. I read Mathlib/Algebra/Homology/DerivedCategory/FullyFaithful.lean (the single/cohomology comparison and both instances), and the grep hit Ext/Basic.lean around mk₀_bijective. These facts are reused through existing leaves, not delivered as duplicate nodes. LeanSearch returned general derived-category existence and left/right degree-zero derived functors, which do not give the item. Both natural-language formulations therefore support no full match; no unavailable service is recorded as no match.

## Review by Q146

I read the chapter and sk-prop-sp-integral-adjunction unit records, the current blueprint's tower-geometric-gamma proof (1), and its nearest ancestor det-sp-integral-adjunction-bijection proof, particularly Purity. The source's map of tower sheaves after removing the shift is exactly the point justified by this auxiliary item. I read Stacks derived.tex, remark-truncation-distinguished-triangle (08J5), lemma-negative-exts (06XS), lemma-right-derived-exact-functor (015F) and lemma-derived-adjoint-functors (09T5); sites-cohomology.tex, lemma-derived-base-change (06YY) and lemma-adjoint (07A6); sites-modules.tex, lemma-adjointness-tensor-restrict (03CZ); and Zheng Construction 4.1 on printed page 21. The argument is marked agent-written because it expands the blueprint using these general results, rather than pretending that the blueprint already gives the full proof. There are no new node sources to review.

For step 1 I opened the actual statements of lem-pur-system-level-left-extension, lem-sf-exact-functor-derived-triangulated, and lem-pur-exact-derived-cohomology-coherence. The first explicitly supplies componentwise cohomology and joint detection of cohomological bounds for arbitrary commutative ring-sheaf towers; the second supplies shift/single compatibility; the third supplies the cohomology identification natural for all derived morphisms. The quotient coefficients here fit those general hypotheses. No finite-type, constructibility, or boundedness condition is imported. The vanishing at every level yields concentration of K itself, not just an unrelated family of heart objects.

For step 2, lem-sf-derived-concentrated-single states concentration in any abelian derived category, and lem-weil-pbc-derived-single-fully-faithful states the full Hom bijection, not merely faithfulness. They apply both to the Grothendieck abelian tower category and to each coefficient module category. The exact-evaluation coherence statement identifies the H^0 normalization under evaluation. I explicitly normalize a chosen isomorphism by the inverse of its induced H^0 automorphism; full faithfulness then makes the normalized map unique. The inverse of each b_n is also lifted, so the resulting alpha_n is proved invertible rather than assumed so.

For step 3, det-sp-coefficient-towers-abelian clause 3 says the reduction maps are natural in the actual derived tower. This is applied to the global iota constructed in step 2; it is not an assertion that every compatible levelwise derived family lifts. det-sp-scalar-extension-functor clause 1 supplies triangulated scalar extension, and lem-sfb-locally-free-derived-scalars supplies the canonical derived-to-ordinary scalar comparison for locally finite free modules, natural in the input and without flatness of the target ring. Rank one is a special case of finite rank. Substitution and cancellation are displayed. No inverse limit or adic reconstruction equivalence is used.

For step 4 I opened def-coef-semilinear-system-models: it actually defines derived reduction by transposing the horizontal semilinear transition with its ordinary-unit/K-flat normalization. I use this as a definition of the canonical reduction, not as a substitute theorem asserting compatibility. The theorem lem-pur-sheaf-ring-derived-hom-comparison states precisely that the derived Hom correspondence on an ordinary morphism preceded by the universal derived comparison is the localization of the ordinary transpose. lem-pur-sheaf-ring-coefficient-ordinary-adjunction states the sheafified pure-tensor formula used to identify that ordinary transpose. The K-flatness needed for its source is supplied by the already cited locally-free scalar lemma, and the fully faithful single embedding proves equality of the actual restricted-module maps. I checked the equation with the restriction of alpha_m inserted: it lives in R_n-modules on both sides, not in a nonexistent common coefficient category. The two pure-tensor values are written explicitly.

Step 5 is elementary from the strict-tower morphism definition in sk-def-sp-coefficient-towers: composition and identities are componentwise. Multiplying the proved transition equality gives the inverse equation; no new theorem about derived towers is hidden here. def-weil-abstract-derived-category supplies localization and shift, so the strict inverse maps give the final derived isomorphism. The last displayed equation checks that evaluation returns the prescribed a_n, not merely some isomorphism at level n.

I checked small cases: s=0 and s=1 have the stated cohomological sign (V[-s] is in degree zero); m=n gives the identity square; the empty scheme gives the zero sheaf category and the unique map; the constant free-line tower with V=L[s] gives alpha_n=1. Over a geometric point with E=Q_l, the quotient Z/l^2 -> F_l is not flat, but each L_n is free over its own R_n, so the K-flat computation still applies. If a_n is multiplication by units u_n, the derived square says u_n mod l^m = u_m and the proved strict equation is exactly that condition. Incompatible units fail the hypothesis. Nontrivial line sheaves require no global basis: the scalar lemma is local, and the maps alpha_n are recovered globally by the Hom bijection. This also checks that the argument is not silently choosing compatible frames.

I checked delivery-errors B--E against the files: no new elementary or duplicate nodes, no clause restatement, no unintroduced new-node objects, no added hypotheses, no appeal to a cited proof instead of its statement, and every non-elementary input is in the step's uses and has a verbatim quotation. The five step lengths are 397, 623, 689, 1042, and 603 characters; none exceeds 2000. The off-unit statements are generic tools with the reasons recorded in split_report.tool_uses; they do not replace any unit purity argument. No SGA source is used.
