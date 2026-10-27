# O2 stage-1 report: lem-sfb-generic-matrix-locus-subgroup-closure

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-generic-matrix-locus-subgroup-closure.json`: statement unchanged, split into seven proof steps; existing Mathlib searches preserved and actual O2 searches appended; no exact Mathlib match.
- `citations.json`: a verbatim statement extract (the full statement, to preserve the hypotheses) for every node used in every step.
- `report.md`: this report.

There are zero new nodes and zero new Mathlib leaves. All non-elementary inputs already have nodes. The elementary quotient and test-algebra calculations are written in the steps, rather than made into new nodes. The sandbox initially had dispatcher briefs only, no item, report, or search log; there was therefore no earlier split to dry-run or search history to reuse. The original item, citations and source provenance have been retained. Only the authorized sandbox was written. No git command, Lean writing, compiler, Lake, build or subagent was used.

## Attachments

None. I searched the live `lean/WeilConjectures/` for the exact item id and generic matrix, matrix locus, group closure and scheme-image terminology. I read the relevant project closure theorem in `WeilConjectures/RingTheory/HopfAlgebra/GeneralLinearGroup/HopfIdeal.lean`, especially the declarations around lines 435-479. Its hypotheses are an actual abstract subgroup and a family of rational points. It does not give the present generic partial-law conclusion, so it is not an attachment. Sorry declarations elsewhere were not counted as finished proofs.

## Literature wanted

None. The cited literature is available locally. This variant is expressly agent-proved, not attributed to Milne's theorem as an exact statement.

## What required correction

The item had no proof. Its hypotheses and conclusion are sound and were preserved verbatim. No statement dispute or weakening was necessary. The source's closure method inspired the proof, but Milne Theorem 1.45 starts from an actual closed subgroup of rational points, whereas our item starts from a geometrically integral affine locus with only generic operations. The proof therefore has `proof_origin.by = agent` and supplies the additional coordinate argument explicitly.

The item inherits a null blueprint ancestor and a long via chain. `tools/blueprint_refs.py ancestor` returned None; I retained the inherited fields rather than inventing an ancestor. I read `dag/chapters/sec-six-functors-basics.json`, `dag/units/sk-thm-sf-ctf-stability.json`, and the latest main-20261024 direct-images proof (3). That current proof routes through open direct images and compactification; this item is the inherited lower-level supporting closure argument in the parent Chevalley big-cell proof, step 5. It changes no unit or chapter statement or route and is not a key unit node, so no realization record was changed.

## Searches and reuse

I searched the whole DAG by titles and statement concepts for geometric integrality, tensor injectivity, restrictions into function fields, affine products, Hopf coordinates and image minimality. I ran whole-blueprint searches for generic matrix locus subgroup closure, Hopf, subgroup and integral. These found the existing general tools used here; no blueprint node states this generic partial-law closure theorem. Searches of the current Lean source supplied no exact attachment. In particular, the actual-subgroup closure node `lem-wf-zariski-closure-subgroup` and the existing perfect-field groupoid-image closure node have different hypotheses: neither applies before a group structure has been established on the source. I opened their statements rather than relying on titles.

Every O2 Mathlib search was executed using the required unmodified `batch2/msearch.py`. Two distinct semantic phrasings, LeanSearch, Loogle and a Mathlib source grep are recorded as returned in `searches.jsonl` and appended to the item's `mathlib_searches`. The returned `HopfAlgebra.Quotient.instQuotientIdeal` presupposes that the ideal is Hopf, which is the main work here. Integral-morphism hits use a different meaning of integral; integral-scheme and function-field hits are useful component tools already in the DAG. `specTargetImage` only constructs the image, not a subgroup structure. Topological or abstract subgroup closures assume an existing subgroup. Thus no returned result states this item or specializes to it in one line. No unavailable service was reported as absence.

## Not duplicates

No new nodes are proposed. The existing item's distinctions from actual-subgroup closure and perfect-field groupoid-image closure remain as in its creating report.

## Review by O2

I read Milne, Algebraic Groups (iAG2017), Section 1c, Lemma 1.40 and Theorem 1.45 on printed pp.18-19 (PDF pp.30-31). The former proves closure of an existing rational-point subgroup; the latter uses schematic density to restrict ambient operations. Neither asserts the generic-law variant, so my proof supplies exactly that missing argument and records its agent origin. I also read Stacks `morphisms.tex`, definition-scheme-theoretic-image, Tag 01R7, and lemma-quasi-compact-scheme-theoretic-image, Tag 01R8, together with `properties.tex`, lemma-characterize-integral, Tag 01ON. I read every cited DAG statement in full. There are no new nodes needing additional source checks and no SGA citation.

Step 1 uses `def-weil-pbc-algebra-hom-quotient` for the surjective quotient map with the stated kernel, `lem-sfb-affine-group-coordinate-hopf` for the coordinate maps of the GIVEN affine group (not a chosen abstract Hopf structure), and `lem-weil-pbc-fibre-product-affine-spectra` for the actual affine fibre product and its coordinate ring. The Hopf coordinate node expressly requires no smoothness or reducedness; G meets its sole group/affineness hypotheses. The injection p is the elementary kernel calculation displayed in the step.

Step 2 uses the exact flatness statement in `lem-weil-pbc-module-over-field-flat` and the injectivity-preservation statement in `lem-trf-flat-tensor-preserves-injection`, applied to the injection A into its fraction field and tensoring by A over F. The geometric-integrality hypothesis at L=K supplies a DOMAIN, not merely a reduced ring. The ring map is unital, so its source is nonzero. I checked `def-pc-integral-scheme`; the affine criterion is also the one in Stacks 01ON. Its few-line localization justification is included rather than hidden behind a new product-integrality lemma. This step is elementary relative to the cited tensor tools: tensor once, take a subring of a domain, then read the integral affine criterion.

Step 3 uses those same two flatness statements twice, now for D into A, to obtain p tensor p injective. It separately uses `lem-sc-integral-scheme-stalks-in-function-field`, whose first clause says the germ map of sections on EVERY open into ANY stalk on that open is injective. I apply it to the global open of the integral product from step 2 and a point v of the given nonempty V. This proves global vanishing without an unjustified pointwise argument or an assumption that V contains the identity. The coordinate factorization on V is the item's own hypothesis; it gives precisely the zero germ needed. The step does not cite a definition for injectivity or use a proof hidden inside a cited node.

Step 4 uses the same injective-germ statement on C and a point of the nonempty W. The identity evaluation is an explicit pullback along the stipulated c0, using j(c0)=1, not an assumption that inversion or multiplication was defined at c0. I checked that no density of F-points or perfection of F enters either step 3 or step 4.

Step 5 cites the quotient definition for surjectivity and kernel, the affine spectrum correspondence for actual morphisms from the descended algebra maps, the fibre-product theorem for the product source, and the affine quotient characterization in `def-weil-closed-immersion` for the closed immersion Spec q. The three representative formulas are explicitly written; independence follows from steps 3-4. This is a routine quotient construction, not an unstated Hopf-ideal theorem. It proves the morphism factorizations required for ALL test algebras.

Step 6 cites precisely the functor-of-points equivalence in `def-sc-group-scheme` and the all-algebras subgroup condition in `def-sc-group-scheme-subgroup`. The injection on R-points is proved by surjectivity of q. The group identities are inherited under this injection because each operation is the ambient one by step 5. This is the elementary restriction-of-group-identities argument; no assertion about only geometric points is used, and no missing comparison theorem is being cited as a definition.

Step 7 cites the closed-immersion affine description and affine spectrum correspondence to test a competing closed subscheme Spec(B/J). Factoring is equivalent to J subset I by the displayed representative formula. I opened `lemma-nagata-scheme-theoretic-closure-minimal`: its statement literally says the closure is the smallest closed subscheme through which the immersion factors and that the comparison is unique. Here j is indeed an immersion by hypothesis. This node is Lean-closed, so it is an allowed generic tool; the other proof inputs apart from group definitions are Mathlib leaves. `def-nagata-scheme-theoretic-image` identifies the closure of the given locally closed subscheme with its scheme image. Thus this last citation takes minimality from a theorem that actually states it, not from the creating report's looser paraphrase of the image definition. No off-route unclosed statement tool is used.

I checked the small cases G=1 and E=0, C a point, C an open neighbourhood of the identity, and nonreduced test algebras. For G=1, immersion and nonemptiness force the expected trivial image. For C=Spec F all maps and the quotient reduce to the identity subgroup. Empty V or W and the zero algebra are excluded by the explicit assumptions. A translated locus without an identity lift would not justify the counit step; c0 supplies exactly this. Over imperfect fields and in characteristics two and three the tensor-domain hypothesis still gives the required injection and vanishing; the proof does not assert the false claim that a product of arbitrary integral F-schemes is integral. Nonreduced ambient G is allowed because its coordinate Hopf maps exist without smoothness, and we check the final group laws on all R, not just on field-valued points.

Against delivery-errors B-E: no unsplit node carries a proof, no new statement repeats a clause, all operations are genuine scheme morphisms, every non-elementary input is a cited existing statement, and all hypotheses have been matched above. There is no citation of a descendant depending on this item. Every step is under 1000 characters (the long-step check at 2000 is vacuous); the only general inputs are already explicit DAG nodes. This self-review is the requested O2 signature, with the maintainer's independent review still to follow.

## Unfinished work

None for this stage-1 item. No stage-2 statement or Lean proof was attempted.

## Validation

Required delivery dry run and push are executed after this report is written; their final output determines the delivery answer.
