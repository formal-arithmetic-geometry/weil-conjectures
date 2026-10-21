# Stage-1 delivery: lem-weil-pbc-constant-tower-pushforward-normalization

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-constant-tower-pushforward-normalization.json`: statement, split into eight proof steps, reusing existing nodes. Statement and statement dependencies unchanged. Mathlib verdict: no exact match, and no one-line specialization covering the specified limit and counit normalizations.
- `citations.json`: nineteen step/node citations, with verbatim statement excerpts.
- `searches.jsonl`: the search command's own log, retained as produced. The existing four search records in the item are retained; six actual searches from this attempt are appended with their queries unchanged.

New nodes: 0. New Mathlib leaves: 0. No Lean was written, no compiler or Lake command was run, and the shared repository and launcher files were read only.

## Attachments

None. Searches in `lean/WeilConjectures/` for the exact blueprint tag and the notions constant/tower, constant/K-injective, constant/derived and constant/pushforward found no declaration giving all of this item. The existing homotopy-limit results concern triangulated cones and the splitting of `1-t`; they do not state this comparison, its normalized constant-limit composite, or its counit identity. No project declaration was treated as finished just because it has a docstring.

## WANTED

None. The relevant Stacks source and the current blueprint proof are available locally.

## Corrections and scope

The imported statement is valid; there is no statement dispute and no mathematical statement change. The previously empty proof is supplied. In particular, the cited strict-tower homotopy-limit node gives the K-injective model, but its statement does not assert the constant-tower identification. Step 6 proves that identification, using the identity cone. This avoids taking an extra clause from a cited node's proof.

The proof follows the first, diagram-topos proof of Stacks Tag 0A07, `sites-cohomology.tex`, `lemma-Rf-commutes-with-Rlim`. It expands its specialization to constants with Tags 08BJ, 070K/070Y, 070I and 09T5 in `derived.tex`, and Tag 079P in `injectives.tex`. The construction and normalization argument are marked agent-written: the source does not state this full normalized constant-tower theorem verbatim.

The current blueprint `main-20261015/.../sk-prop-pbc-complete/prop-weil-pbc-direct-image-limits.proof.md` was read, as were the chapter record and `sk-thm-properbasechange` unit record. The blueprint's final completion-map normalization is the place served by this item. The unit/chapter route is unchanged, and the item is not the unit's key node, so no unit record is edited. The existing `blueprint.from.node` is retained and its place made precise.

## Mathlib and duplicate searches

The prescribed command ran LeanFinder twice with different conceptual phrasings, Loogle once, LeanSearch once, and grep twice. Every service answered successfully. The log records exact queries and results. The first grep and Loogle returned no hits; the second grep returned generic derived-functor construction files. LeanFinder returned exact derived descent, ordinary right-derived cohomology and bounded-below K-injective results. LeanSearch returned the generic derived counit and constant/colimit adjunction APIs. I read `Mathlib/CategoryTheory/Functor/Derived/RightDerived.lean` (the universal right-derived comparison and its extension API), `Derived/Adjunction.lean` (the derived counit and its factorization equation), `Limits/HasLimits.lean` at `constLimAdj` (593) and `colimConstAdj` (967), and `Algebra/Homology/DerivedCategory/ExactFunctor.lean` (termwise exact descent). These are tools for the argument, not an exact or one-line instance of this item. No new leaf is proposed.

I searched the whole DAG and the imported blueprint for constant towers, constant diagrams, direct-image normalization and K-injectives, including `blueprint_refs.py ancestor` and searches for `constant tower`, `constant-tower`, `constant diagram`, `constant inverse`, `direct image`, `pushforward normalization` and `K-injective`. Existing nodes for all non-elementary tools were opened and reused. In particular, the constant-functor preservation fact is an immediate application of the existing exact-left-adjoint theorem after the explicit two-line `e_1` adjunction; it does not warrant a new node.

## Not duplicates

No new nodes were created. The related existing `lem-sf-cbc-constant-tower-direct-image-normalization` was opened: it treats constant Noetherian adic coefficients on small pro-etale scheme sites and also has an augmented projection-formula clause. It does not cover arbitrary ring sheaves on arbitrary small ringed-topos presentations, and cannot prove the generality of this item. Neither node is copied or newly created here.

## Review by NI

I read delivery-errors B through E in full and checked the split against the actual node statements and the sources above. There are no new statement-only nodes to audit under B, no hidden intermediate node restating a clause under D, and no unperformed search recorded under B7. All eight non-elementary steps are shorter than 2000 characters. The proof gives chain maps and their equations, rather than inferring equality of maps in the derived tower category from equality at every evaluation.

For step 1 I opened `lem-weil-pbc-small-module-diagrams-grothendieck`, which permits an arbitrary small index category and arbitrary ring sheaves; singleton and inverse-sequence indices satisfy its size assumptions. Its conclusion supplies the Grothendieck property needed by `lem-weil-pbc-kinjective-functorial-existence`. I deliberately used this abstract existence node rather than applying a commutative-ring-specific resolution statement to an unspecified ring sheaf. `lem-weil-tower-category-levelwise-abelian` actually states the levelwise kernel/cokernel computation and exact evaluations. Its statement makes exactness of constants and of termwise F a direct check. `lem-weil-pbc-exact-functor-derived-factorization` really supplies the termwise derived descent and its comparison on every complex. F's exactness and adjunction are part of the item's setup; no flatness or exact countable products are introduced.

For step 2 the explicit formulas for maps into a constant tower prove `e_1` left adjoint to constants: the arrow is n to 1, not the reverse. Exactness of `e_1` is in the levelwise node's statement. I checked the hypotheses of `lem-weil-pbc-right-adjoint-preserves-kinjective`: the right adjoint is constants, the exact left adjoint is `e_1`, and both are additive. Tag 08BJ states precisely this preservation theorem. The elementary adjunction construction is written as part of the step rather than made into a node.

For step 3 the same preservation node applies to F left adjoint to G, with the given exactness of F. It yields GJ K-injective, then step 2 yields both constant complexes K-injective. The strict equality of image towers includes transitions and differentials. `lem-weil-pbc-kinjective-total-derived` explicitly says a K-injective computes the total right derived functor; it therefore licenses the representative computations being used.

For step 4 I checked the total-derived node's universal comparison, not merely its existence conclusion. Its comparison is invertible on the two chosen K-injectives. The formula for chi includes both comparison maps in the required directions. `lem-weil-pbc-kinjective-hom-derived` gives the full Hom bijection for arbitrary source complexes and K-injective targets, and also the homotopy equivalence assertion for changes of K-injective resolution. `lem-weil-pbc-termwise-adjunction-homotopy` states that the additive termwise functors preserve homotopies. Consequently naturality for chain maps really descends to all derived maps, with no unstated choice of tower-derived morphism from evaluated components.

For step 5 I opened `lem-weil-pbc-tower-derived-evaluation-normalization` and copied its exact beta/eta formula into the step. Its Grothendieck, levelwise-exactness, additive-adjunction and exact-F hypotheses have been checked in step 1 and the setup. Substituting the constant K-injective tower gives the displayed cancellation. This uses exactly its statement, not an assertion that evaluation is faithful on derived morphisms.

For step 6 I opened `lem-weil-pbc-ringed-strict-tower-homotopy-limit`: it explicitly computes total inverse limit from a K-injective tower. I use only this model, not its unrelated pro-zero consequence or any exactness of products. The canonical map from J is the identity cone; ordinary limit of that constant tower is J by the cone universal property. `lem-weil-pbc-kinjective-total-derived` and the Hom bijection justify the natural derived identification and its independence of the representative. The inverse of this map is the canonical Rlim-constant identification in the item.

For step 7 I opened `lem-weil-ringed-tower-pushforward-limit-comparison`. Its statement specifies the comparison as the one from the common underived direct-image composite; merely knowing some product-compatible isomorphism would not suffice. On the same constant K-injective representative, both the input of the outer G and the input of the outer limit are already K-injective. Thus the chosen common-composite comparison is the identity on the single complex GJ. The displayed b/chi/a equation records the directions of every map. It yields the claimed identity after the indicated source and target identifications; there is no assertion that maps out of a derived limit are determined by their projections.

For step 8 I again read the full Hom and termwise-adjunction statements. Their bijections apply to arbitrary B because only the targets J and GJ need be K-injective; F is computed exactly, so no K-flat or boundedness hypothesis is missing. The transpose of the identity is explicitly the ordinary counit. For towers the target is the already K-injective constant tower, and naturality of the ordinary adjunction gives a levelwise mate that commutes with every transition. The counit equation is consequently a localized equality of strict tower chain maps, including the F/constant identification. It is not deduced from the evaluation-counit clause of the normalization node. This is the canonical derived Hom construction of Tag 09T5 on these representatives.

I tested the reasoning on the zero ring and zero complex (all displayed maps are the unique identity of the zero object), the identity morphism of ringed topoi (chi, a and the counit reduce to identities), and unbounded K-injective complexes (the adjoint argument uses acyclicity rather than a bounded-below resolution). The index starts at 1 and is nonempty; this matters for both the `e_1` adjunction and the constant-limit identification. No discreteness of coefficients, constant-ring hypothesis, scheme hypothesis, enough-points hypothesis or exactness of countable products is used. The related constant-coefficient result was therefore not substituted for the general item. Off-unit results are listed in `split_report.tool_uses` as generic tools; no top-level `tool_uses` field was set.

## Unfinished work and validation

The split and citations are complete. The required server dry run and direct delivery will be run next; their final results are recorded below when available. Independent maintainer review remains part of the delivery protocol.
