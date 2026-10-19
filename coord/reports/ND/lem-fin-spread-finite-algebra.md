# Stage-1 worker report: lem-fin-spread-finite-algebra

## Files written

- dag/nodes/sec-smooth-purity/lem-fin-spread-finite-algebra.json: item split into nine steps, with existing dependencies only. Mathlib searches found no exact result.
- citations.json: a verbatim statement quote for each step/node citation.

## New nodes

None. No new Mathlib leaves.

## Attachments

None. Searched WeilConjectures in the slopmaster2 source for the blueprint tag and spreading/finite-algebra concepts. EtaleTorsorSpreading concerns torsors, not arbitrary coherent finite algebras; no declaration stating the entire item was found. Master source was treated only as reference.

## WANTED

None. The blueprint and Stacks sources used are present locally.

## Corrections and route

The statement is unchanged mathematically. Its statement dependencies now name projectivity, coherent modules, algebra sheaves, localization, base change and Noetherian rings explicitly. The imported references to pqf-def-coherent and lem-pc-section-clearing-denominators did not supply descent of arbitrary algebra multiplication, gluing maps or their equations. Removed these proof references and reused the already existing global finitely presented module/map descent and eventual-zero-map descent nodes. These contain the global gluing argument as actual conclusions; the proof does not use their internal constructions. This is the same finite-presentation and finite-equation route as the item's blueprint, made precise by Stacks 01ZR. It does not replace the unit's compact-support base-change route. The item is not the unit's key theorem, so no unit realization record is changed.

Searches of the whole DAG for 01ZR, finite algebra and finite-presentation descent, and blueprint_refs searches for finite algebra, Spreading a finite algebra and projective, found the existing descent tools. They are reused instead of duplicated. No other blueprint node states this item; same_as is empty. Off-unit general tools are declared in split_report.tool_uses with reasons. There is no same-tag new-node pair requiring a Not duplicates entry.

Mathlib searches ran exclusively through msearch.py and are recorded in the item and searches.jsonl. Both semantic phrasings were read. The first found projective-spectrum/function-field facts; the second found structure-sheaf section descent and local finite-presentation definitions, not algebra descent. Loogle returned ordinary finite-presentation facts. The grep hits in SpreadingOut were read: that file spreads individual morphisms from stalks to neighbourhoods, not a finite algebra over the entire generic fibre. LeanSearch returned Internal Server Error, recorded as unavailable.

## What remains unfinished

No part of this one-level split. The cited existing nodes retain their own proof obligations; this task creates none and makes no claim to have proved the library in Lean.

## Review by ND

I read the item's master blueprint statement and both proof paragraphs, its chapter and unit records, and the Stacks source limits.tex at lemma-descend-modules-finite-presentation (01ZR), including all three clauses and both proposed proofs. The module-object/morphism and eventual-equality clauses are genuinely what this argument needs. The new proof supplies the finite algebra identities that the imported prose left implicit. No new source statement is introduced, and no source/statement dispute was necessary.

For step 1 I opened the full statements of localization-colimit-principal-localizations, limit-affine-transition, affine-scheme-qcqs and scheme-over-limit. They give directedness and the ring colimit, affine spectrum limits, qcqs of affine schemes, and the cartesian limit respectively. The module descent system is indexed by nonzero elements under divisibility, with initial element 1. Noetherianity of every localization is justified directly by the contraction-and-extension argument for ideals; it is not an unstated flatness or finiteness assumption. I read the affine-limit lemmas 01YW/01YX in limits.tex.

For step 2 I opened projective-proper, the definition of proper, separated-quasi-separated, lft-fp-locnoeth, qcqs-morphism-permanence and qcqs-over-affine. The proper lemma supplies finite type and separatedness through the cited definition; the separated lemma supplies quasi-separatedness, while the locally Noetherian hypothesis on Spec A makes the finite-type-to-local-finite-presentation lemma applicable. Combining those explicit properties is finite presentation, not just local finite presentation. The permanence lemma states base-change preservation; qcqs-over-affine supplies qcqs of the stage schemes. I read morphisms.tex's projective-is-quasi-projective-proper and noetherian-finite-type-finite-presentation (01TX), and checked these conclusions against the node statements. The proof does not assume an arbitrary proper map is projective.

For step 3 coherent-local-finite-presentation explicitly gives local finite free cokernel presentations of the given coherent module. The quasi-coherent-finite-type-affine statement explicitly includes that finite presentation implies quasi-coherence. The module-map-descent statement's clause (1) gives a global stage module and isomorphism, rather than merely modules on charts. Its base rings are Noetherian by step 1 and its initial scheme is finitely presented by step 2. I read modules.tex's coherent-finite-presentation and finite-presentation-quasi-coherent (01BO) as well as 01ZR(1).

For step 4 the tensor-affine-sections statement gives exactly quasi-coherence and the affine tensor computation. The finite-presentation criterion identifies finite ring-module presentations with sheaf presentations. The finite list of tensor generators and relations is written, so no separate tensor-finiteness theorem is hidden. Tensor-pullback-finite-presentation is valid for every scheme morphism, without flatness, and module-pullback-tensor gives the natural tensor comparison and its formula on pure tensors. I read modules.tex's pullback-finite-presentation and tensor-product-pullback (01CD), and properties.tex's finite-presentation-module (01PC). Rank-zero presentations also work.

For step 5 I used clause (2) of module-map-descent exactly for the multiplication, unit and optional idempotent maps. The sources and targets are finitely presented; they are not assumed locally free. Pulling earlier lifts to a common stage is licensed by the pullback finite-presentation statement. The tensor comparison identifies the lifted multiplication's generic domain with the domain of the prescribed multiplication. Directedness makes the finite number of simultaneous choices legitimate.

For step 6 fp-zero-map-descent states eventual vanishing for finite-type source, finitely presented target and quasi-compact initial scheme. All four algebra defects and the optional finite idempotent defects have precisely those hypotheses. The generic zero assertions are the original algebra identities; the pure-tensor formula from module-pullback-tensor identifies the associativity, symmetry and unit diagrams, so I have not silently used preservation of an unrelated chosen comparison. Subtracting maps reduces equality to this exact zero-map statement. I reread 01ZR(3). Every difference is a module map, including the maps from O for the idempotent identities. No ring equality is being imposed on just one chosen affine chart.

For step 7 the algebra-sheaf definition supplies the intended notion of commutative unital O-algebra; the finite-presentation/finite-type affine criterion supplies finiteness of the underlying module. Algebra structure and its generic isomorphism follow explicitly from the displayed operations, their linearity and the four laws; no relative-Spec equivalence or coherence theorem is tacitly invoked.

For step 8 the quasi-coherent-module-cokernel-image statement asserts both quasi-coherence of the image and its affine sections as the module-theoretic image. This is precisely the assertion used for e_i M, not a definition cited as a theorem. The affine finite-type criterion makes it a finite module using the displayed finite generators. The forward and inverse product maps are written and verified using all the imposed idempotent identities. On generic pullback, each image is the split summand of multiplication by e_i: its inclusion/projection identities persist under a functor, so preservation of arbitrary images by a nonflat pullback is not assumed. I checked the schemes.tex quasi-coherent image statements named by that node (01IB/01IC). The factor's unit is e_i; it need not be the original unit of M.

Step 9 handles the empty product as the zero algebra rather than assuming a nonempty family; a zero factor and empty scheme also satisfy the formulas. Products of nonzero denominators remain nonzero because A is a domain, and an already-field base permits a=1. Nonflat finite algebras are allowed throughout: every use of pullback needs only finite presentation, and no tensor-exactness claim is made. These edge cases test the potential missing-flatness and zero-unit errors.

I checked delivery-errors B through E against the final files: no statement-only child carries a proof, no elementary lemma or item clause is made into a node, no new duplicate exists, every non-elementary step uses explicit existing statements, and every cited statement has its verbatim quote in citations.json. The corrections above explain the substantive citation changes rather than treating the imported proof as accepted. The second reader should inspect the listed off-unit tool uses and the explicit finite-equation/product argument.

Final verification: corrected source annotations from 01BH to 01BW for coherent finite presentation, from the unrelated section 01CM to 01AO for tensor generators, and specified 01WC for projective properness. The dependency closure does not reach the item. The final delivery dry run is rerun after these annotation corrections.

## Second reading by ND

I reopened the blueprint node and the Stacks limits.tex, morphisms.tex and modules.tex passages named in the item. The statement agrees hypothesis by hypothesis: Noetherian domain and fraction field, projective base change, finite coherent algebra, principal localization, and simultaneous finite product decomposition; zero algebra, empty product, field base and empty scheme cases remain included.

Step 1: checked the localization colimit, affine inverse-limit and base-change statements (01YW/01YX/01YZ); the divisibility system and Noetherian localization argument supply the stated limit. Verdict: sound.

Step 2: checked projective-to-proper (01WC), proper definitions, separated/quasi-separated, finite-presentation and base-change permanence statements (01TX and cited nodes). Verdict: all hypotheses are present and no projectivity is inferred from properness.

Step 3: checked coherent finite-presentation (01BW), quasi-coherence (01BO) and module descent clause (01ZR(1)); the global finitely presented module and generic isomorphism are exactly supplied. Verdict: sound.

Step 4: checked tensor sections and finite-presentation matrix criterion (01CD, 01AO, 01BO, 01PC), pullback finite presentation and tensor comparison. The displayed finite generators and relations cover rank zero and triple tensors. Verdict: elementary and sound.

Step 5: checked module/map descent clause (01ZR(2)) and tensor pullback statement; multiplication, unit and each finite idempotent family are maps between finitely presented objects and are lifted to a common stage. Verdict: sound.

Step 6: checked eventual-zero-map descent clause (01ZR(3)) and the tensor comparison. Every associativity, commutativity, unit and idempotent defect is explicitly a module map with generic zero, and finite directedness gives one stage. Verdict: sound.

Step 7: checked the commutative unital algebra-sheaf definition and finite-type affine criterion. The lifted operations and four laws give the algebra and its generic algebra isomorphism. Verdict: elementary and sound.

Step 8: checked the quasi-coherent image lemma (01IB/01IC) and finite-type criterion. Orthogonal-idempotent sum/product maps are written explicitly; split projections justify generic identification, including zero factors. Verdict: elementary and sound.

Step 9: checked the zero algebra, empty product, nonzero denominator product in a domain, and empty-scheme edge cases. Verdict: elementary and sound.

There are no new nodes to audit (hence no Mathlib leaves). I retained the existing descent/tool nodes and their verbatim citation quotes. I corrected the source annotations to 01BW, 01AO and 01WC, and the report records why the prior clearing-denominators and coherent-module citations were insufficient. The delivery dry run passed preflight.
