## Worker report

Item: lem-sfb-proetale-locally-closed-generator-comparison. Group Q113. Stage 1 only. Date: 2026-10-22.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-proetale-locally-closed-generator-comparison.json: item, statement; nine proof steps, status split. The statement and all inherited metadata are preserved.
- citations.json: a verbatim statement excerpt for every dependency cited by every proof step.
- report.md and searches.jsonl: report and actual msearch log. Temporary preparation script write_split.py remains sandbox-only; the delivered node is the final authoritative artifact.

## New nodes

None. Zero Mathlib leaves added. All facts needed by the argument already have nodes.

## Attachments

No attachment for the whole item. Searching WeilConjectures for the blueprint tag found none. Reading the comparison modules found AlgebraicGeometry.ProEtale.isIso_lowerStarComparisonUpperStarBaseChange (SixFunctors/ProEtale/Comparison/LowerStar.lean:224), and ConstructibleSheaf.lean:117 contains isFiniteLocallyConstant_comparisonUpperStar_obj. These cover ingredients only, not all three clauses, especially not the geometric-stalk finite-projectivity assertion. Existing DAG nodes already record the relevant comparison and local-constancy ingredients; these are not proposed new attachments.

## WANTED

None. The actual item source, the existing comparison blueprint files and the relevant Stacks source are available locally.

## Findings and changes

The item was unsplit and the sandbox had no earlier item or report. Its statement is sound and unchanged. I expanded the exactness assertion, justified the complementary-open hypothesis, transported finite projectivity using the linear stalk comparison, and made the natural composite in clause 3 explicit. I also identified the left-Kan and sheafified-presheaf presentations of pro-etale extension by zero; they are not silently treated as identical functors. The direct-image comparison is used only for a degree-zero bounded-below complex, followed by H^0, so no unbounded comparison theorem is inferred from a bounded-below statement.

The unit JSON is an older snapshot in sec-smooth-purity and still mentions a forbidden old source in its historical text. The actual item's current source is the main-20261015 proof in sec-six-functors-basics. I followed that current proof's complement and first paragraph, as instructed, and used no SGA source. No chapter or unit record was edited.

## Searches

Read the whole current DAG for candidate statements and tags, including 09BM, 099Y, 0GLZ, 099R, and the seven input nodes named by the item's source. Also searched titles for projective implies flat, affine morphism permanence, Noetherian topology, module localization adjunction, and uniqueness of adjoints; each required fact was already present. The blueprint search commands were ancestor of this item, and searches for `proetale locally closed`, `comparison`, `projective flat`, `locally closed generator comparison`, `extension by zero`, and `locally constant origin`. No node states the full three-clause item, and the existing open and closed comparison nodes were reused.

Ran msearch with LeanFinder twice (different formulations), Loogle, LeanSearch and two grep queries. Exact queries and results are appended in mathlib_searches and recorded by the command in searches.jsonl. The services answered successfully in this attempt. LeanFinder returned scheme structure-sheaf pullback/restriction lemmas and algebraic etale localization results; these have different objects from the required module sheaves on the two sites. Loogle returned ellAdicSheaf, its empty-scheme vanishing, and a Grothendieck-abelian instance, not a comparison theorem. LeanSearch similarly returned scheme stalk and closed-immersion facts. I read Mathlib/AlgebraicGeometry/Sites/Proetale.lean and ElladicCohomology.lean: the former defines the site and topology, the latter a particular ell-adic coefficient sheaf; neither states the item. Inherited search records were retained as inherited evidence; none was relabelled as a new execution.

## Not duplicates

No new nodes; no new/existing node pairs require a duplicate justification. The projective-flat fact is the existing Mathlib leaf lem-weil-pbc-projective-module-flat, and the two comparison ingredients are the existing prop-weil-pbc-comparison-direct-image and lem-cbc-proetale-extension-zero-comparison.

## Review by Q113

I read the current source literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-sf-flat-model/sk-lem-sf-flat-model.proof.md, particularly the first paragraph and the complement's first sentence. The item isolates exactly its closed-pushforward exactness and transport of the stratum generators. I checked the source statements and proofs in proetale.tex at 09BM, 099Y, 0GLZ, 0993 and 09AF; derived.tex at 015F; topology.tex at 0053 and 04ZA; morphisms.tex at the affine-separated and closed-immersion-affine lemmas; and algebra.tex's projective-implies-flat explanation in the proof of 051G. I read the existing comparison-direct-image and extension-zero-comparison blueprint files, including their proofs. No new node needs a source check because none was created.

Step 1 uses pqf-def-locnoeth for its affine cover by Noetherian rings, lem-sc-affine-noetherian-underlying-space for the topology of each affine, lem-kun-finite-union-noetherian to assemble the finite cover, and lem-sfb-noetherian-space-compact-subsets for quasi-compactness of every subset. The extracted finite subcover is supplied by the item's quasi-compactness assumption. The conclusion applies to every intersection with the open complement, so the required retrocompactness is genuinely established, not inferred from separatedness. The affine-topology node's cited tag 0052 concerns subspaces, but its statement is the correct affine fact; algebra.tex 00FQ is the precise affine source, recorded in the step.

Step 2 reads the exactness assertions literally: lem-cbc-open-closed-recollement says that the etale closed direct image is exact, and lem-weil-pbc-proetale-ringed-open-closed says the module functor i_* is exact when its complementary open is quasi-compact. Step 1 verifies that hypothesis for g. The coefficient identification is supplied by the canonical constant-ring isomorphism of lem-pe-constant-left-module-inverse-image; its constant scalar normalization identifies the direct image action with the one in the item. This is a module assertion, not an unsupported inference from exactness of set-valued direct image.

Step 3 uses the actual statements of lem-weil-pbc-exact-functor-derived-factorization and lem-weil-pbc-exact-functor-derived-functor. The latter explicitly asserts invertibility of the canonical comparison for every complex. Applying it to (j_!M)[0] establishes the named map of clause 1 on the unbounded derived category as well as on the bounded-below subcategory. No resolution is chosen and no assumption on M is added.

Step 4 checks the finiteness requirement of lem-sf-proetale-locally-constant-origin before invoking its forward clause: the finite ring and finite generation give a surjection from a finite set Lambda^r to each stalk. The lemma asserts local constancy after comparison; it does not assert preservation of projectivity, which is handled in the next step.

Step 5 uses the Lambda-linear, fixed-ring module clause of lem-cbc-proetale-comparison-stalk. That clause is present in its statement. The finite generating set and finite-free splitting transport through the linear isomorphism, so finite projectivity is preserved. The existing Mathlib leaf lem-weil-pbc-projective-module-flat then supplies flatness. I did not use ordinary geometric points as a conservative family for all pro-etale sheaves: the Stacks discussion following 0993 specifically warns that they are not.

Step 6 checks the two definitions of j_!. The current layer-A definition has the left-adjoint-to-restriction assertion in def-sfb-finite-extension-by-zero-adjunction. The module localized-site construction is left adjoint to restriction by the actual statement of lem-pur-site-restriction-module-adjunction-exact, and lem-weil-proetale-weakly-etale-localization identifies the sites, restrictions and constant rings. The module version is essential here: the superficially similar lem-weil-pbc-site-restriction-adjunction only asserts the abelian-sheaf case and was not cited. The last parenthetical clause of lem-weil-pbc-conjugate-iso-unit-equation explicitly identifies two left adjoints of the same right adjoint. In preparing this step I replaced an unnecessary appeal to a closed complement inside C by these general localization statements, so it needs no extra construction or hypothesis.

Step 7 checks the two morphism hypotheses of comparison-direct-image: the affine clause of def-weil-closed-immersion applies to g, and clause (3) of lem-weil-pbc-affine-morphism-permanence gives quasi-compactness and quasi-separatedness. This has nothing to do with separatedness of X itself.

Step 8 uses the exact full natural derived isomorphism in prop-weil-pbc-comparison-direct-image, applied to N[0]. It lies in D^+, as required; g is qcqs by Step 7. Exactness of both g_* functors and the canonical all-complex comparison from lem-weil-pbc-exact-functor-derived-functor identify their derived values on single complexes. Lem-sf-comparison-pullback-exact explicitly asserts exactness and commutation with cohomology, so H^0 gives the sheaf isomorphism beta naturally. H^0 of a single complex is the original sheaf by the zero-differential calculation. I claim existence of this natural sheaf isomorphism; no stronger named-map normalization than clause 3 asks for is imposed.

Step 9 applies the sheaf-level, arbitrary-M, finite-commutative-ring statement of lem-cbc-proetale-extension-zero-comparison. It is used for the open j:S->C, with its pro-etale convention identified in Step 6, and then pushed forward and composed with beta. Naturality is the naturality of each of these two factors. This is the actual argument for the locally closed composite; no new node merely restates that clause.

I tested the empty stratum, zero sheaf, identity immersions, the closed-only case j=id, and the zero ring. Empty-stratum functors give zero sheaves and the unique isomorphisms; all modules over the zero ring are zero. For identity g or j the same composite is valid. The Noetherian assumption is used precisely to obtain the pro-etale closed-direct-image exactness hypothesis. No argument assumes a field coefficient ring, global freeness of L, a nonzero coefficient ring, separated X, or a conservative family of ordinary pro-etale geometric stalks. All nine steps are below 2000 characters; no long step conceals another comparison lemma. I checked B1–B10, C1–C8, D1–D5 and E1–E7 against these files. Every non-elementary input is a cited existing node, the quotes in citations.json are literal substrings, and the statement is unchanged.

## Tool uses

The report and split_report.tool_uses identify generic tools from other units: Noetherian topology, exact module open/closed direct image, constant coefficients, exact derived functors, comparison of local constancy and stalks, localized module adjunction and uniqueness, and the two comparison isomorphisms. They implement the current unit proof's own exactness and pullback assertions. They do not replace its flat-model route. No maintainer-only tool_uses field was written.

## Unfinished work

None in the requested one-level split. The existing dependency nodes retain their own proof obligations. Server dry run and delivery results follow from the required deliver.py invocations.
