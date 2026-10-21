# Stage-1 report: lem-pur-etale-kflat-support-comparison

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-etale-kflat-support-comparison.json`: statement item split into eight proof steps. The statement and inherited provenance are unchanged. Mathlib verdict: no exact match; general tensor and short-exact triangle results are reused through existing nodes.
- `citations.json`: 27 citations, one for each step/node use, with verbatim statement quotations.
- No new DAG nodes and no new Mathlib leaves. `write_split.py` is sandbox-only working material, not a delivered node.

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint id and support-sequence/K-flat comparison terminology. The ordinary-etale support rows in `SixFunctors/OpenClosed/Supports.lean` and the support cohomology triangles in `SixFunctors/Etale/SupportCohomologyTriangle.lean` provide parts, but do not state this coefficient-resolution diagram, its right-map identification, and its boundary compatibility together. They are not attachments for this item.

## WANTED

None. The blueprint source and the primary Stacks homological constructions are available locally. The proof origin is nevertheless `agent`: the blueprint locality/chart proof does not contain this support diagram verbatim. This delivery supplies its homological expansion, using cited existing statements.

## What was wrong or missing

The item was a statement-only extraction, with no proof. Its notation can invite an invalid interpretation of the replacement: `N = Tot(Q tensor I)` is only an A-module complex, so the replacement `a:N -> J` must be taken in A-module complexes. This is already the category of N and is made explicit in Step 1; no statement change is needed. In particular neither N nor Q is given a strict B-action, and a B-injective sheaf is never assumed A-injective.

Two further gaps that a loose proof could hide are now explicit. Infinite total-degree sums are exact because they are filtered colimits of finite exact biproduct rows, rather than because an unbounded spectral sequence converges. The last triangle square is supplied by the natural short-exact boundary, and the right map is identified by an equality of adjoint transposes, rather than by its source and target objects alone.

The inherited blueprint ancestor is null: `tools/blueprint_refs.py ancestor` reports this for the launcher's seed ancestry. Its existing detailed `blueprint.from.place` is preserved, and `same_as` is empty after whole-blueprint searches for support sequences, support triangles, K-flatness and coefficient comparisons. The imported support-triangle and scalar-change results are ingredients, not duplicate assertions of this item. No unit or chapter record is changed: this item is a prerequisite, not the key statement of `sk-thm-purity-transport`.

## Unfinished work

None within this one-level split. Existing cited nodes retain their own status and obligations. No Lean source was written and no compiler, Lake or build command was run.

## Not duplicates

No new nodes. The actual support-sequence item, general short-exact-complex triangle leaf, fixed-K-flat tensor lemma, cochain tensor/pullback comparison, derived chain-transpose lemma and scalar-mate identification are reused instead of being recreated. The support row alone does not assert the coefficient diagram, and the scalar-mate lemma alone does not construct its kernel and connecting maps.

## Searches and route

The item retains its inherited searches. Five additional searches were actually run with the prescribed `batch2/msearch.py` command and are recorded in `searches.jsonl` and the item: LeanFinder twice with distinct natural-language formulations, Loogle on `DerivedCategory.triangleOfSES`, a CategoryTheory grep for support triangles, and LeanSearch for the K-flat coefficient/support comparison. The services returned answers; none was treated as unavailable. The hits concern generic triangles, module flatness, scheme-module restriction, scalar adjunctions or localization. In particular the generic `DerivedCategory.triangleOfSES.map` result is already available through `lem-weil-pbc-complex-ses-triangle`, which is cited. No new search or leaf is invented from a remembered name.

The off-unit citations are generic homological, inverse-image, and coefficient-restriction tools, listed with their individual reasons in `split_report.tool_uses`. They expand the closed-factor coefficient comparison used by `lem-pur-finite-coefficient-adjoint-comparisons` Step 6 and the finite-stage compatibility of `sk-thm-purity-transport` Step 1; they do not replace the smooth-purity diagonal/deformation route. No SGA source is used.

## Review by NV

I read the current main-20261015 exceptional-reduction proof, the `sec-smooth-purity` chapter record, and all four steps of `sk-thm-purity-transport`. The current source gives coefficient compatibility by locality and smooth charts. This item is the subsequent ordinary-etale closed-support extraction below that compatibility, so I marked its explicit proof as agent-written. I read Stacks `sites-cohomology.tex` at 093X, 06YM, 06YS, 06YT, 06YU, 0G7E, 07A4, 07A6 and 0FPI; `sites-modules.tex` at 03DB, 03ER and 03EL; `derived.tex` at 0152 and 014A; `injectives.tex` at 079P; and the change-of-rings passage 0GL6 in `more-etale.tex`. These supply the actual support row, K-flat and flat-term distinctions, signed tensor construction, adjunction normalization and boundary naturality used here. There are no new nodes requiring separate source reviews.

For Step 1 I opened the statements of `lem-pur-etale-injective-support-sequence`, `lem-weil-pbc-kflat-fixed-tensor-triangulated`, and `lem-pur-etale-scalar-mate-projection`. The first gives the exact rows and canonical derived computation; the second computes tensor by a fixed flat-term K-flat coefficient resolution on arbitrary input complexes; the third explicitly states the canonical identification of restriction of scalar extension with tensor by B. The identification of J is chosen through the quasi-isomorphism a, so its middle component is indeed the identity. The step stays in A-modules.

For Step 2 I checked that `def-pc-flat-sheaf-modules` actually defines flatness by exactness of the tensor functor, and that `lem-pc-module-filtered-colimits-tensor` explicitly states exactness of filtered colimits of module sheaves. This is stronger evidence than merely citing the word flatness. Finite biproduct exactness and the filtered index of finite subsets are written out. The exact formula for the total differential comes from `def-pc-tensor-complex-sheaves`. No finite Tor dimension, bounded resolution or flatness of B over A is smuggled in.

For Step 3 I checked the statements of `lem-pur-cochain-pullback-tensor-coherence`, `prop-weil-pbc-inverse-image-modules-exact`, and `lem-weil-pbc-termwise-adjunction-homotopy`. They give an unbounded chain tensor/pullback isomorphism, the actual inverse-image/direct-image adjunction, and its chain-level unit/counit formulas. The comparison is constructed by adjunction and maps out of direct sums; it never needs direct image to preserve those sums. The sign in the differential is unchanged because all constituent maps have degree zero.

For Step 4 I used those same adjunction and cochain-comparison statements and the actual kernel in the support-sequence statement. I computed both transposes, reduced each by the adjunction triangle identity, and used kernel uniqueness for the first map and its differential equation. This is the elementary step, not an uncited recollement or support comparison theorem. Its naturality is checked after the monomorphism into J.

For Step 5 I checked the full statement of the Mathlib leaf `lem-weil-pbc-complex-ses-triangle`: it states naturality of the connecting arrow for a strict morphism of short exact complexes, not merely existence of some distinguished triangle. `lem-pur-etale-injective-support-sequence` identifies the target row with the specified support triangle. This is why the third square, with the shift of the first map, commutes.

For Step 6 I opened `lem-sp-etale-derived-chain-transpose` and checked both its displayed Hom-bijection equation and its particular counit equation. They apply to arbitrary complexes and canonical right-derived comparisons, so they do not require an unsupported claim that a restricted B-injective complex is A-injective. `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` explicitly includes preservation of K-flatness with flat terms; the cochain-comparison statement gives the normalized comparison on these models; the fixed-K-flat lemma computes the tensor objects. Finally `def-kun-projection-formula-map` defines exactly the transpose being calculated. I checked that the counit is at j-star L and that the coefficient is B_P, whose inverse image is B_U. The signed swap puts the coefficient second, matching that definition.

For Step 7 I checked every hypothesis of `lem-pur-etale-scalar-mate-projection` at j and j-star L: bounded-below input and scalar-extended input follow by exact j-star; the tensor/direct-image source bound is an explicit hypothesis of the item. The remaining direct-image bound is also retained. `lem-sbc-canonical-restrict-scalars-functor-comparisons` gives exactly the needed canonical bounded-below direct-image identification, not injectivity after restriction. Thus the right arrow is the specified restricted coefficient map. I read 0GL6 as context rather than claiming its proper-case isomorphism for arbitrary j: no invertibility or properness is used in this step.

For Step 8 I checked that `lem-sf-triangle-morphism-iso` applies to a morphism of distinguished triangles with any two invertible components, which are here the middle identity and the hypothesized right isomorphism. `lem-weil-pbc-complex-ses-triangle` gives functoriality of the boundary, and `lem-pur-kinjective-degreewise-existence` states a functorial replacement. These suffice for the claimed natural diagram.

I tested the extreme closed-open pairs: for empty Z the support kernels vanish and the right comparison is the identity case j=id; for empty U the third terms vanish and the first map is the middle quasi-isomorphism. For A=B with Q=A[0] the construction reduces to the natural support diagram of a. For the nonflat finite map Z/4 -> Z/2 the argument still uses a K-flat resolution Q with flat terms, never ordinary tensor by B as an exact functor. The zero object and zero coefficient ring also give zero complexes and zero triangles. All eight proof steps are below 2000 characters. I checked every cited statement and a transitive dependency search found no path back to the item from any of the additional tools. This is a genuine construction using existing smaller inputs, with no new clause-restatement node and no hidden comparison lemma.

## Validation

The required server dry run exited successfully: `OK (not pushed) deliver/NV/lem-pur-etale-kflat-support-comparison at 4585124e17c: preflight passed`. It ran the maintainer preflight including DAG and split checks. The initial citation check requested a longer quotation for the exact support row; I replaced the bare displayed row with its complete short-exactness and naturality sentence, then reran successfully. Local string checks also verified all 27 verbatim quotations, complete step/citation coverage, the proof-dependency union, and unchanged statement text. The final delivery command performs its own preflight before pushing.
