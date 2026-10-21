# Worker report — Q131

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-signed-line-scalar-pullback-square.json`: statement item, now split into eight proof steps; no Mathlib match.
- `citations.json`: nineteen step/node entries, each with a verbatim substring of the cited statement.
- `report.md`: this report. `searches.jsonl` is the unmodified search-command log.

No new nodes and no Mathlib leaves. The item's statement and statement dependencies are unchanged. All maintainer fields are retained from the repository copy.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id and for signed powers, signed lines, twist and pullback/dual terminology. No declaration gives this square with all signed exponents and arbitrary sheaf coefficient maps. Generic evaluation/derived-duality results do not attach this item.

## WANTED

None.

## Corrections and scope

The imported node was statement-only, not an erroneous statement. The blueprint's powers/internal-Homs paragraph motivates the claim but does not supply this general square proof. The proof is therefore marked agent-written, with its blueprint ancestor and the actual Stacks places read. There is no statement dispute and no alteration of a target, unit or chapter route.

The tensor and dual pullback nodes already supply the substantial ingredients. I did not introduce a duplicate signed-powers lemma, a new node for the elementary balanced reassociation, or a node restating the desired negative-degree square. The item's own proof constructs its families, proves uniqueness, and computes both sides on a common local generator. The signed scalar tensor tower is used only for its stated scalar/basis normalization, not for the pullback square being proved.

During self-review I replaced an implicit appeal to pulling local trivializations through a functor by step 6: the existing module-adjunction and unit-compatible localization statements justify precisely that passage. This avoids extracting an unasserted property from the proof of the dual-pullback node.

## Mathlib and blueprint searches

I read the inherited Mathlib records and preserved them, and ran six new searches through the required `msearch.py`, whose exact queries and actual results are appended to `mathlib_searches`. Both semantic services, Loogle and grep returned successfully. The second semantic phrasing searches the more general finite-free dual comparison. The resulting `IsBaseChange.dual` and `Module.Dual.baseChange` are algebraic module results; `SheafOfModules.pullbackComp`, `pullback_assoc`, and `pullbackObjFreeIso` concern composite pullback or free sheaves. None states the item's signed square for four specified lines, nor yields it by a one-line specialization.

I inspected `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean` at lines 48–110 and 158–210, `Sheaf/PullbackFree.lean` at lines 105–152, and `Mathlib/LinearAlgebra/Dual/BaseChange.lean` at lines 20–110. In particular the free-sheaf theorem does not itself identify the signed scalar square.

Whole-blueprint searches used `tools/blueprint_refs.py search` with `signed line`, `pullback tensor`, `scalar`, `dual pullback`, `signed tensor`, and `line scalar`; the nearest ancestor is `prop-weil-twist-preserves` via `lem-weil-integral-twist-base-change`. The general-purpose tensor, dual and localization statements found in the whole DAG are reused. No blueprint node states this entire signed scalar square in another form; `same_as` remains the searched empty list.

## Not duplicates

No new nodes. Existing `lem-pur-signed-line-scalar-tensor-tower` supplies scalar signed bases and coefficient towers on one site; the item additionally concerns geometric pullback between two sites and four ring sheaves. Existing `lem-pur-ringed-site-finite-free-dual-pullback` supplies the negative-map ingredient, not this compatible four-line square.

## Review by Q131

I read the current `main-20261015` proof `sec-six-functors-basics/sk-prop-sf-existence/prop-weil-twist-preserves.proof.md`, especially the tensor-powers/internal-Homs assertion and final levelwise/common-finite-stage sentence. I also read the unit and chapter records. This is an underived sheaf-module argument; it invokes no derived flat base-change statement and no SGA source.

The source checks were against `literature/stacks-project/sites-modules.tex`: Tag 03EL (`lemma-tensor-product-pullback`, lines 3649 onward), Tag 0GMX (`remark-pullback-internal-hom`, lines 3787 onward), Tag 0FNY (`example-dual`, lines 4886 onward), Tag 03D7 (`lemma-adjoint-pullback-pushforward-modules`, lines 1197 onward), Tag 04J0 (`lemma-localize-morphism-ringed-sites`, lines 2369 onward), and the tensor-product and internal-Hom definitions. I checked the tag/label mapping. I also read `sites.tex`, Tag 00X6, `proposition-get-morphism`, for the geometric inverse-image convention. No new node needs a separate source review.

1. Step 1 uses the statements of `lem-weil-pbc-left-exact-site-inverse-image-tensor` and `lem-weil-pbc-ringed-topoi-module-pullback-tensor` for the geometric and relative tensor comparisons. The former gives the geometric inverse image and tensor structure, the latter gives the natural relative tensor isomorphism. The explicit coefficient-unit map and inverse follow from the sheafified sectionwise tensor in `def-pur-sheaf-tensor-product`; their formulas do not require a flat ring map. I did not assume the tensor theorem's statement asserts unspecified coherence: the normalization and balancing argument supplies the unit/reassociation identities used here.
2. Step 2 specializes that same tensor theorem to the inverse-image coefficient ring and writes both directions of the scalar reassociation. The equality (b\alpha=\iota'a) is exactly what makes the two proposed maps balanced over (A). Balancing over (B) and (R') computes the inverse identities. This is a short tensor-relation argument, marked elementary and kept inside the item.
3. Step 3 uses the relative tensor theorem and recursive tensor definition to construct each positive comparison by induction. Local rank one of each positive power is proved by the multiplication chart and its inverse. Restricting the tensor comparison to a local chart is also its specialization to the localization morphism; no projective or flat hypothesis has been added.
4. Step 4 applies the exact statement of `lem-pur-ringed-site-finite-free-dual-pullback` twice. Both sites have the needed finite limits and common sheaf universe, the functor preserves coverings, the coefficient maps have the required direction, and step 3 supplies finite local freeness of the positive powers. The cited theorem explicitly says the evaluation-defined map is an isomorphism without flatness. `def-pur-sheaf-hom` supplies the genuine internal Hom on slices, so precomposition with the inverse positive comparison gives the negative map in the stated direction. Evaluating its displayed composite proves the requested pairing formula, not merely existence of some isomorphism of lines.
5. Step 5 uses `def-pur-sheaf-hom` for equality as local functionals. Positive recursion and the prescribed degree-zero/one maps force the positive family; the required negative formula forces the negative family. The argument is elementary and does not rely on uniqueness of an unspecified trivialization.
6. Step 6 cites the site inverse-image theorem, module-adjunction theorem and `lem-pur-ringed-site-pullback-localization-universes`. I checked the last statement's extra requirements: slice finite limits and coverings come from the underlying site diagrams; covering preservation ensures slice continuity; the module-adjunction theorem gives the actual tensor-formula functors as the global and slice left adjoints. Its statement expressly identifies the units, which is necessary for the pulled basis to be the unit image used in step 7. This is a generic tool use, recorded in `split_report.tool_uses` together with the other off-unit statements.
7. Step 7 uses covering preservation, the tensor definition, the localization statement, and the dual-pullback theorem's explicitly stated dual-basis formula. The initial square makes (q(\widehat v)=c'(p(\widehat e)\otimes1)). Consequently the four local signed bases really are compatible. For negative powers precomposition sends the pulled dual basis to the dual of the new positive basis; a covariant use of a dual map would have the wrong direction and is not used.
8. Step 8 takes only the signed local-basis formula actually stated by `lem-pur-signed-line-scalar-tensor-tower`, applied separately on the two sites. In each application its three-ring version can be specialized by repeating the target coefficient ring and using its identity map for the last arrow. Both composites send the one common (S')-basis to ((v')^m). Linearity gives their value on every section, and the sheaf uniqueness axiom gives global equality. Thus no assertion that arbitrary inverse-image sections are globally original pure tensors is needed.

For edge cases I checked (m=0), where all generators are (1) and the only compatibility is the coefficient ring square; (m=1), where the equality is the hypothesis; and (m=-1), where the transpose is precomposed with (p^{-1}), so its value on (p(w)) is the original pulled evaluation. On the point site, quotient maps such as \(\mathbf Z\to\mathbf Z/2\mathbf Z\) satisfy every formula despite nonflatness. If the degree-one comparison is multiplication by a unit \(\lambda\), positive degree gives \(\lambda^n\) and negative degree gives \(\lambda^{-n}\), checking the inverse direction. Zero coefficient rings also cause no difficulty: the zero module is the free rank-one module over the zero ring and the identities remain identities. No assumption that a coefficient map is injective, flat or invertible enters any step.

I checked delivery-errors B through E against the files. There are no new statements to hide a proof in, no duplicate nodes or unsupported Mathlib leaves, and no borrowed proof-only constructions. Every non-elementary input is a node citation, every cited statement was opened, and all nineteen quotes are literal substrings of those statements. The substantial proof steps are marked non-elementary; the balanced scalar formula and uniqueness are the two elementary steps. The proof dependency list is exactly the union of the uses. Each step is shorter than 2000 characters. No node on which this proof depends was created by this delivery, and no clause has been moved out as a restatement of the item.

## Unfinished work

None within the one-level stage-1 split. The reused unsplit scalar tensor tower remains its own independent item, as required by the DAG process. No Lean was written and no compiler, Lake command or local preflight/check script was run.
