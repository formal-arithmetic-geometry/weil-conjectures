# Stage-1 report: lem-pur-supported-hom-adjunction-transpose

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-supported-hom-adjunction-transpose.json`: statement, split; no exact Mathlib match. Six proof steps compare the supported-Hom map with the adjunction transpose on one injective resolution.
- `citations.json`: a verbatim statement quotation for every citation in each numbered proof step.
- `report.md`: this report.
- `searches.jsonl`: actual msearch.py results, retained with their timestamps and digests.

## New nodes

None. The existing DAG supplies the general homological algebra. Zero new Mathlib leaves.

## Attachments

None. Searched all of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag/id, supported-Hom terminology, `supported_cohomology_hom`, and supported-adjunction names. The matches concern the supported-away inclusion adjunction or ordinary supported products/localization; none states this equality of identifications. No compiler was run. The exact upstream master remains reference material, not finished-proof evidence.

## WANTED

None. The argument is agent-written, using the available current blueprint and Stacks sources, not attributed to a document that proves the normalization verbatim.

## Source error and statement clarification

STATEMENT-DISPUTED: the phrase “the natural isomorphism ... of lem-pur-supported-hom” does not by itself select an isomorphism: that node's statement asserts existence and naturality only. For example take coefficients A = F_3, X = Z = Spec(k), i = id, F = A_X[0], a = 0. Multiplying a natural supported-Hom isomorphism by -1 gives another one satisfying that node's existence/naturality statement, while it takes 1 to -id instead of id. Hence mere naturality does not imply the required equation.

The item's last sentence already states its intended normalization: both identifications derive the evaluation map at q_i(1). I made that normalization explicit in the sentence defining chi: derive the inverse of this underived evaluation bijection and apply the existing injective-resolution derived-Hom identification. No hypothesis, coefficient category, support, shift, conclusion, or geometry was changed. This makes the intended isomorphism precise rather than identifying an arbitrary natural isomorphism with the adjunction transpose. The statement dependency on `lem-sc-p1-rhom-hom-derived-roof` is consequently explicit.

The Stacks-source field of the existing generic node `lem-sc-derived-adjunction-from-underived` spells its file `derived-categories.tex`; the available source is `literature/stacks-project/derived.tex`. I read the actual deriving-adjoints section (labels lemma-pre-derived-adjoint-functors-general, lemma-pre-derived-adjoint-functors, lemma-derived-adjoint-functors), Tags 0FND, 0DVC, 09T5, and the matching Mathlib derived-counit equation. My steps cite the actual source file; the existing dependency was not edited. In the proof, composition is written in mathematical right-to-left order, so the typed counit equation is epsilon' composed with C_i(beta_I) equals Q(epsilon^0_I).

## What could not be finished

Nothing remains in the mathematical split. The delivery checks and push are recorded below after execution.

## Blueprint route and duplicate search

Read `dag/chapters/sec-smooth-purity.json`, `dag/units/sk-thm-regular.json` and the current main-20261015 proof file, especially Step 5. The node is a normalization tool below that step's equality of supported cup and exterior products, not a replacement of the purity proof. The blueprint ancestor is `sk-thm-regular`, via `lem-pur-exterior-product-frame`; its precise from.place is retained. Searches `blueprint_refs.py search supported`, `search supported-Hom`, `search adjunction transpose`, and searches throughout dag/nodes and the source found no other blueprint node stating this normalization equality. `same_as` is empty. The general supported-Hom theorem asserts an isomorphism, and the supported-exterior-product definition fixes an adjunction, but neither states their compatibility; both are reused rather than cloned.

## Not duplicates

No new nodes. The general resolution, right-derived-functor, derived-Hom and derived-adjunction nodes were found and reused. No clause of the item was moved into another node.

## Mathlib search results

Every new search was made with the prescribed msearch.py command, with the exact query and returned log record copied into the item. Both semantic services, Loogle and source grep worked. The second semantic wording was “Evaluation at one identifies morphisms from a free rank one object to a complex with its cohomology and commutes with a derived adjunction”.

The first wording returns ordinary sheaf cohomology, global-sections adjunctions and an injective-resolution Ext formula. LeanSearch returns `CategoryTheory.Adjunction.derived` and constant-sheaf adjunctions. Loogle returns the general `CategoryTheory.Adjunction.homEquiv` operations. The second wording returns complex-level single-object equivalences. These are ingredients, not the specified pro-etale supported-Hom compatibility. The support-specific grep has no hits. I read the relevant Mathlib source in CategoryTheory/Functor/Derived/Adjunction.lean (particularly derived', derivedε_fac_app and derived), CategoryTheory/Sites/GlobalSections.lean, and the sheaf-cohomology Basic file. The generic derived-adjunction ingredient already has a DAG Mathlib leaf, `lem-sc-derived-adjunction-from-underived`; no duplicate leaf is introduced.

## Review by NC

I read the item's full statement, its parent `lem-pur-exterior-product-frame`, the current blueprint sk-thm-regular proof, the unit and chapter, and both `lem-pur-supported-hom` (statement and explicit resolution construction) and `def-pur-proetale-supported-exterior-product` (statement and fixed normalization). I also read every statement dependency. The item needs the locally Noetherian hypothesis only to use the fixed C_i adjunction from that definition; the argument uses no constructibility, finite Tor dimension, smoothness, or projectivity of i_*A_Z. It stays in the ambient constant-finite-coefficient module-sheaf category, and does not replace it by an etale-origin, adic or constructible category.

For step 1 I checked that the cited definition really specifies precomposition with q_i and the constant-sheaf adjoint followed by the kernel inclusion. Evaluating that formula at 1 gives exactly v_M, not a scalar multiple. The free rank-one module calculation and additivity/naturality are written out. This is an elementary use of a fixed adjunction, not an appeal to the proof of the supported-Hom theorem.

For step 2 I checked the chosen-small-skeleton clause of `def-weil-pbc-proetale-site` against the small-ringed-site hypothesis of `prop-pur-kinjective-resolutions-exist` and `lem-sc-bounded-below-injective-resolution`. I read `lem-sp-grothendieck-enough-injectives`, which actually states the enough-injectives conclusion used. I read Stacks derived.tex Tag 013K, lemma-injective-resolutions-exist (including its bounded-below clause), 070J, lemma-bounded-below-injectives-K-injective, 05TH, lemma-injective-acyclic, and 05TI, lemma-enough-injectives-right-derived. Clause (2) of the cited right-derived node really gives the isomorphism beta_I on bounded-below injectives. The cited support-cohomology definition includes the pro-etale kernel construction and its right derived functor. Thus the represented cocycle is in Gamma_Z(I^a), rather than in an unrelated global-sections complex.

For step 3 the differential equality follows directly from step 1. The existence and uniqueness of derived transformations used to derive v and its inverse are explicitly clause (1) of `lem-weil-pbc-right-derived-plus-injective`, and clause (2) identifies the result on I. This step supplies the comparison instead of assuming a coherence between two unspecified derived functors. The additive Hom complex in the next step has exactly the same cocycles and boundaries as the underlying groups of the A-linear Hom complex here; no preservation-of-injectives assertion for a forgetful functor is used.

For step 4 I read the whole statement of `lem-sc-p1-rhom-hom-derived-roof`. It states the cocycle-to-localized-map formula, including postcomposition with the shifted inverse of the chosen resolution, for an arbitrary object M and every integer n. I verified its enough-injectives and bounded-below K-injective-resolution hypotheses in step 2. In particular it does not require P to be projective. I read Stacks 070I and the maps-into-injective-complex calculation in derived.tex, and the degree-n complex-map formula. This cites a statement that contains the needed representative formula, not only an existence of some abstract isomorphism.

For step 5 I read the statement of `lem-sc-derived-adjunction-from-underived` and the corresponding source and Mathlib equation. It supplies the underived/derived counit equation used here. The specified exact-left/right-derived adjunction and its comparisons come from `def-pur-proetale-supported-exterior-product`; I do not infer a new normalization from adjunction existence. Substituting beta_I and the representative s in that equation gives the displayed composite. Its only nonzero component is explicitly the same underived adjoint f_s as in step 1. The equality is proved on representatives, rather than asserted as “transport” or “standard compatibility”.

For step 6 I checked the cochain shift in `def-weil-abstract-derived-category`. The component of a degree-zero map does not acquire a sign when shifted. I wrote out the boundary homotopies both before and after shifting, with the (-1)^a factor in the latter. The conclusion is the equality of the two formulas from steps 4 and 5, not an additional lemma left hidden in the final step. All steps have fewer than 2000 characters.

I tested the actual formulas on X empty, Z empty (P and supported sections zero), Z = X (ordinary constant-sheaf/global-sections adjunction), F = 0, a = 0, a = 1 and a = -1, cocycles changed by a boundary, and coefficients of characteristic two. The odd-degree homotopy sign is necessary; it cancels the sign in d_{I[a]}, and there is no sign on f_s itself. The F_3 identity-support example detects the normalization ambiguity and prompted the explicit statement repair above.

I checked delivery-errors B–E point by point: no new unproved-definition, elementary-node, duplicate, or disguised-clause node is introduced; every non-elementary input has an existing cited node; the citation file quotes the actual statements in full; step hypotheses and coefficient categories are verified above. The proof relies on none of another node's proof-only conclusions. All off-unit inputs are declared in split_report.tool_uses as generic tools; the regular-purity unit route is preserved. There is no SGA citation and no Lean writing or compilation.

## Validation

The required `deliver.py NC lem-pur-supported-hom-adjunction-transpose --no-push` process exited 0 and printed `OK (not pushed)` at dc1e35df4a: preflight passed. This includes the server DAG and split checks. No second delivery invocation ran while it was active. The final push uses the same prescribed delivery tool and repeats its normal checks.
