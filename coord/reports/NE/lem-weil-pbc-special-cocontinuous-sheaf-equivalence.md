# Worker report

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-special-cocontinuous-sheaf-equivalence.json`: item, statement unchanged, split in six steps following Sites 03A0. Mathlib has a related dense-subsite equivalence, but the five family-cover assumptions require a bridge to its sieve-topology hypotheses.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-continuous-cocontinuous-topos-adjunction.json`: one new statement-only unsplit node, no Mathlib leaf. It supplies the sheaf-valued right Kan extension, its adjunction to restriction, explicit unit/counit, and the associated morphism of topoi assuming only continuity and cocontinuity. The search candidate is `CategoryTheory.Functor.sheafAdjunctionCocontinuous`, read in CoverLifting.lean lines 275–367. The covering-family-to-sieve translation and explicit compatible-family realization prevent marking this as a one-line specialization.
- `citations.json`: every citation in all six steps, quoted verbatim from the cited statements.

## Attachments

None. Searches of WeilConjectures/ in the read-only slopmaster2 source for the blueprint tag, item id, cocontinuity and the expected adjunction names found only particular functors and localization instances. They do not state this arbitrary-functor comparison theorem. Upstream master was read as reference material, not as evidence that its sorry declarations are proofs.

## Wanted literature

None. All source material is present in `literature/stacks-project/sites.tex` and its tag table.

## What was wrong

The imported item is correct. Its existing search records included an irrelevant localCohomology comment; I left those inherited records intact and appended the actual searches of this run. The split does not equate family-local fullness/faithfulness with Mathlib's target-topology predicates without proof. No hypotheses or coefficient categories changed: the theorem is about sets, not module or condensed coefficients.

## Source error

Sites 03A0 says the category of pairs $(A,\psi:u(A)\to u(U))$ has a final object $(U,\mathrm{id})$. That assertion is false in general: finality would require each $\psi$ to be the image of a unique arrow $A\to U$, whereas assumptions (3),(4) give only local existence and local equality. For an explicit small example, take $\mathcal C=B(\mathbf Z/2)$ (one object, two automorphisms), $\mathcal D$ the terminal category, and the functor killing both automorphisms. Give both categories the site structure in which every small family, including the empty family, covers. Fibre products exist since these are groupoids. All five assumptions hold: continuity and cocontinuity hold; local equalization can use the empty covering; all target arrows lift; cover-density holds. The category of pairs over the unique target object is $B(\mathbf Z/2)$ and its only object is not final, because its endomorphism set has two elements. Both sheaf categories are terminal because empty coverings force singleton sections, so the lemma's conclusion is still true.

The split uses the canonical projection/evaluation from the compatible-family set, as in Sites 00XG, without finality. It proves its bijectivity by local lifting and equalization. The source also writes $s_{(U,\psi)}=s$ at the end of the counit argument where the intended coordinate is $(U,\mathrm{id})$; the split uses that coordinate explicitly. These are errors in the proof wording, not disputes of the item's statement.

## Not duplicates

lem-weil-pbc-continuous-cocontinuous-topos-adjunction vs def-weil-pbc-special-cocontinuous-functor: the existing node defines cocontinuity and the five comparison hypotheses; its source mentions 00XO but it supplies no right Kan extension adjunction or section formulas. The new node assumes only the first two hypotheses and proves that infrastructure, not the equivalence conclusion.

lem-weil-pbc-continuous-cocontinuous-topos-adjunction vs lem-weil-proetale-weakly-etale-localization: the existing node identifies a particular pro-etale slice and its coefficient restriction; its 00XR citation does not state the general adjunction or its unit/counit formulas.

lem-weil-pbc-continuous-cocontinuous-topos-adjunction vs lem-weil-pbc-proetale-immersion-limit-preservation: the existing node is a theorem about inverse image for locally closed scheme immersions, and extension of scalars by a ring-sheaf isomorphism; it does not give general cocontinuous-site right Kan extension.

lem-weil-pbc-continuous-cocontinuous-topos-adjunction vs lem-weil-pbc-etale-inverse-image-restriction: the existing node gives restriction and the unit for an etale morphism of schemes. The new node is for arbitrary small sites and additionally constructs direct image and the counit from compatible families.

I searched the whole DAG by 00XO, 00XR, 00XK, 00XL, 00XF, 00XH, continuous/cocontinuous and right Kan extension, and the whole blueprint through blueprint_refs.py by tags and concepts. No node states the new generic infrastructure. The existing site-restriction-exact lemma mentions the Mathlib adjunction only in its proof, which cannot be cited as if its statement gave the adjunction. No proposed local-gluing or cover-detection nodes were created: those arguments belong in the item's steps.

## What could not be finished

Nothing at this one-level split. The new infrastructure statement remains unsplit by design, with the exact source and Mathlib candidate for its next worker. No Lean was written or compiled, no build tool was called, and no delivery was pushed.

## Review by NE

I read the worker brief, stage-1 rules, SETUP's three blueprint levels, GOAL, dag-sync, chapter and unit records, and delivery-errors B–E in full. The unit's proper-base-change route is untouched; this item supports the generic site replacement used below completed pullback. Its blueprint ancestor and via chain were checked with blueprint_refs.py ancestor. Same_as is empty after searches of the entire imported blueprint.

For the item I read Sites 03A0 (lemma-equivalence) from its five assumptions through the entire proof. For the new node I read the compatible-family construction in Section 00XF, the evaluation map 00XG, the presheaf adjunction 00XH, cocontinuity 00XJ, right Kan extension preserving sheaves 00XK, the left-exact adjunction 00XL, the topoi construction 00XO and restriction formula 00XR. The new node records statements only, with an empty proof and empty proof dependencies; it does not assume density and does not restate a clause asserting equivalence. Its definitions of families and restriction maps introduce every object, so a later worker can read it without the parent. The source tag 00XF was verified in tags/tags and corrected from an initial draft typo 00XC.

Step 1 cites the special-cocontinuous definition precisely for (a),(b), and the new node precisely for $L$, $R$, the associated topos adjunction, and its unit/counit formulas. Smallness holds by the item's hypothesis and the definition of sites. This is the only external non-elementary infrastructure invoked by the proof; local fullness, local faithfulness and density are not smuggled into that node.

Step 2 cites the special-cocontinuous definition for (c),(d) and continuity (b), and the sites definition for covering pullbacks and the sheaf equalizer condition. I checked that the two overlap maps have equal images using the actual preserved pullback; applying (c) requires that equality and produces a cover in the source category, exactly as its statement says. Separatedness and gluing are the injectivity/existence parts of the equalizer definition, not unidentified standard lemmas. Choice-independence is proved using common refinements and the same equalization calculation. This step is non-elementary because it carries an actual argument rather than a one-line definition application.

Step 3 uses the same two definitions and the new node's compatible-family criterion and evaluation counit. I checked the equality $a q_i=f_i\operatorname{pr}_2$ on the pullback and its image under $u$, then the compatibility identities for both arrows of pairs. This produces a genuine compatible family, and not just unrelated local sections. The identity covering proves the prescribed evaluation value. Uniqueness follows from the sheaf equalizer's injectivity on the lifting cover. The final-object mistake was removed here.

Step 4 uses only the new node's unit and counit formulas and the bijection proved in step 3. Evaluating the restriction family at the identity gives the identity on the section set; this is the few-line elementary argument declared in the node.

Step 5 cites (e) from the special-cocontinuous definition, the site/sheaf equalizer definition, and the new node for $H=RL\mathcal G$ being a sheaf and for unit naturality. I first checked injectivity on every object, using covers by image objects; only then used injectivity on the arbitrary overlap to match preimages of the local sections. Thus no false assumption that overlaps are themselves image objects enters. The source's final 'easily' is fully expanded. Every gluing and separatedness application is to a sheaf on the correct site.

Step 6 uses the naturality supplied by the new adjunction node. Componentwise bijections give natural inverse transformations by rearranging the naturality equations. These are exactly quasi-inverse equivalence data, so no uncited comparison theorem or target clause moved into a new node is used.

Small cases checked: identity functor gives the original section via evaluation and the identity unit; an equivalence of sites gives the usual restriction equivalence; empty sites and empty covering families cause no failure (the appropriate compatible-family products and sheaf section sets are singleton). For the new node alone, the unique functor from the empty category to the terminal category with only identity coverings is continuous and cocontinuous but not dense: $R$ is the terminal sheaf and $L$ is restriction to the empty site. Its adjunction exists without being an equivalence, verifying that the new statement is genuinely smaller than the item and needs no hidden density hypothesis.

B–E audit: source tags and labels read, all objects and notions introduced, single TeX escaping, no fabricated searches, unavailable LeanSearch recorded as unavailable. The two semantic phrasings and actual Loogle/grep hits were read in Mathlib CoverLifting and DenseSubsite. The new node retains only a candidate because of the family/sieve bridge. Every uses-list citation has its statement opened and a verbatim supporting quote in citations.json; proof_deps is their union. New nodes cannot form a cycle because the sole new node depends only on definitions already used by the item. No off-unit statement tools or unit-route replacement are used. No new elementary, duplicate, or target-clause nodes were left in the packet.


## Second reading by NE

- Item statement: read Sites 03A0 (lemma-equivalence), all five hypotheses and conclusion, against the item and both cited definitions; agrees without extra hypotheses or weakened conclusion.
- Step 1: read the new adjunction statement and Sites 00XO (lemma-cocontinuous-morphism-topoi), 00XR (lemma-when-shriek), and the special-cocontinuous definition (a),(b); the cited statements supply restriction, compatible families, and the adjunction under exactly the hypotheses available. Pass.
- Step 2: read 03A0's counit-surjectivity overlap diagram and the two definition statements cited here; the sheaf equalizer gives separatedness and gluing, covering base change gives every pullback, and (c),(d) apply to the displayed arrows with equal images. The common-refinement calculation proves choice independence. Pass.
- Step 3: read 03A0's counit argument and all three cited statements; the pulled-back lifts satisfy the required image equation, compatibility with both arrows of pairs forces the local values, and sheaf separatedness proves uniqueness. Evaluation at the identity coordinate is supplied by the new node. Pass.
- Step 4: read the unit/counit formulas in the new node; evaluation of the identity coordinate gives the identity and Step 3 gives the inverse, a few-line elementary calculation. Pass.
- Step 5: read 03A0's final paragraph, clause (e), and the sheaf equalizer definition; first establish unit injectivity on every object, then use it on arbitrary overlaps before gluing. Empty coverings force singleton sections. The generic adjunction supplies that both sides are sheaves and that the unit is natural. Pass.
- Step 6: read the adjunction statement and both previously established bijections; inverse components are natural by rearranging the naturality equation, giving quasi-inverse equivalence data. This elementary conclusion needs no additional comparison theorem. Pass.
- New node `lem-weil-pbc-continuous-cocontinuous-topos-adjunction`: read Sites 00XF (section-more-functoriality-PSh), 00XH (lemma-adjoints-pu), 00XK (lemma-pu-sheaf), 00XL (lemma-exact-cocontinuous), 00XO, and 00XR against each clause. The compatible-family indices, restrictions, unit/counit, and hypothesis directions agree. B1–B7 pass: statement-only; objects introduced; definitions cited; TeX singly escaped; tags and labels specified; no unsupported Mathlib leaf or tag-defined notion. This node does not assert equivalence and is not a restatement of a target clause.

Independent duplicate checks: searched DAG source tags 00XO, 00XR, 00XK, 00XL, 00XF, 00XH and right Kan extension, plus the whole blueprint with `blueprint_refs.py search cocontinuous`. Read the statements of the special-cocontinuous definition, site-restriction-exact, weakly-etale-localization, proetale-immersion-limit-preservation, etale-inverse-image-restriction, and sheaf-on-basis-extends. They define the hypotheses or concern particular localizations or bases, rather than this generic right adjoint with formulas. Thus none replaces the new node. Searches of slopmaster2 and upstream master for the item id, new id, 03A0 and special cocontinuity found no matching declaration.

Independent Mathlib searches: ran msearch.py with the more general pointwise-right-Kan-extension phrasing (LeanFinder), `CategoryTheory.ran_isSheaf_of_isCocontinuous` (Loogle), and a source grep for that declaration, the unit formula, and finite-limit preservation. Read CoverLifting.lean:275–365. Hits are genuine related infrastructure, but assume sieve-topology continuity/cocontinuity and do not state the family-model comparisons. The new node remains unsplit, with the candidate retained. Actual outputs are in searches.jsonl and appended to its mathlib_searches.

Small cases: identity functor gives evaluation and unit identities; the empty source site with nonempty terminal target and identity coverings satisfies the new node's two hypotheses but fails density, and yields restriction left adjoint to the terminal-sheaf functor without equivalence. Empty coverings force singleton sections, so all local-gluing arguments still hold. The B(Z/2) example in the worker's source-error section has all coverings and all pullbacks (all arrows are invertible), and verifies the stated failure of the source's final-object sentence. The split correctly avoids that sentence. No statement dispute was found.

Changes: made Step 5 explicitly quantify the preceding injectivity proof over all objects, replacing its unnecessary “same argument” phrase; appended three independent Mathlib search records and this step-by-step second-reading audit. No statement change or additional node was necessary. The existing item's created.item is its historical origin and was retained. Citations were checked against each cited statement and remain valid verbatim excerpts. The mandated command's trailing dot is unsupported by deliver.py; used its documented group/item/--no-push interface instead, with no script changes.
