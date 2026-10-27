# Stage-1 delivery: lem-trf-invertible-fp-tensor-models

## Files written

- dag/nodes/sec-trace-formula/lem-trf-invertible-fp-tensor-models.json: existing statement, now split in four steps; statement and statement dependencies unchanged. Retained the previous search records and added genuine logged searches for this session.
- dag/nodes/sec-trace-formula/lem-trf-fp-sheaf-tensor-product.json: one new statement-only unsplit node, the tensor-permanence assertion of Stacks 01CE(4) for arbitrary finitely presented scheme module sheaves. No Mathlib match.
- citations.json: one verbatim statement quotation for each uses edge of the item's proof.

New nodes: 1. New Mathlib leaves: 0.

## Attachments

None. Searching the project Lean by the exact item tag returned no declaration. Concept searches found the parent invertible_affine_limit_descent only in lean/Sheaf/AlgebraicGeometry/InvertibleAffineLimitDescent.lean, with sorry, and the finite-presentation tensor theorem in WeilConjectures/AlgebraicGeometry/Modules/ProjectionFormula.lean:170 requires its second factor to be invertible. It does not state the new arbitrary-factors tensor result. WeilConjectures/AlgebraicGeometry/TensorPullbackFinitePresentation.lean:38 already proves the pullback-preservation node, which is reused.

## WANTED

None. All mathematical sources used are present in literature/stacks-project/.

## Corrections and limitations

The item statement is correct and was retained. Its proof was empty. The older parent docstring's informal tensor-presentation argument is now represented by a genuine general tensor-permanence node rather than by citing only definitions for an exactness assertion. No statement dispute, change to targets, or departure from the unit route is needed. The general object-descent node lem-trf-fp-modules-affine-limit-descent already states exactly the required 01ZR(1) assertion; the more specialized Picard module-map-descent node assumes Noetherian affine bases and was not substituted for it.

No work remains in this one-level split; the new unsplit node is deliberately left for a later worker. Only stage 1 was performed, and no Lean, compiler, Lake or repository write was used.

## Searches and source route

I read the chapter sec-trace-formula and the sk-i-curve-zero unit records, the three-level policy in SETUP.md, and the current blueprint proof literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md. This item's inherited blueprint ancestry places it under the fibrewise-ampleness input used deeper in that proof. The split retains that placement and uses the line-bundle approximation argument of Stacks 0B8W, rather than replacing any unit-level trace argument. The new node inherits the exact ancestor and adds this item's id to via.

Before creating the tensor node I searched the entire DAG by 01CE, 03L6, the source label and finite-presentation/tensor keywords, and searched the blueprint using blueprint_refs.py for finite presentation, tensor product, 01CE, tensor-product-permanence and tensor product of two finitely. The source-tag search returned no blueprint duplicate. The general finite-presentation descent and dual-evaluation results were reused, not recreated. Project source searches read ProjectionFormula.lean:170 and TensorPullbackFinitePresentation.lean and checked the parent declaration.

The new node's actual msearch.py queries are recorded verbatim in mathlib_searches and searches.jsonl: LeanSearch, Loogle, grep and two LeanFinder phrasings. I read the hits. Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:267 defines the sheaf property but supplies no tensor closure. Mathlib/Algebra/Module/FinitePresentation.lean:338 proves scalar extension by an algebra, not tensor closure for arbitrary sheaves. Module.Relations.tensor in Mathlib/Algebra/Module/Presentation/Tensor.lean is ordinary module presentation data; it requires additional sheaf-local arguments to prove the new statement, so it is not a one-line specialization. Finite-generation tensor results and presheaf tensor definitions likewise do not give this result. The item itself was also searched with all four tools and two semantic phrasings; its models are not in Mathlib. No unavailable service was recorded as a negative result.

The intended future proof of the new node, kept here rather than inside its statement-only JSON, follows the displayed two-presentation calculation in modules.tex, lemma-tensor-product-permanence. On a common neighbourhood take presentations O^m -> O^n -> F -> 0 and O^r -> O^s -> G -> 0. The relations from both factors give (O^m tensor O^s) direct-sum (O^n tensor O^r) -> O^n tensor O^s -> F tensor G -> 0, whose first two terms are finite free. The map is u tensor 1 on the first summand and 1 tensor v on the second; the cokernel universal property is the bilinear universal property with both relation systems imposed. Thus no flatness or local freeness of F,G is needed. This sheaf presentation theorem is the general lemma isolated here, not a new copy of the item's common-stage construction.

## Not duplicates

lem-trf-fp-sheaf-tensor-product vs lem-trf-invertible-fp-tensor-models: the new node is tensor permanence for arbitrary finitely presented modules on any scheme, with no inverse system, invertible limit module, dual, simultaneous models or evaluation composite; it is an independent generic input, not the whole item or a renamed stage-model clause.
lem-trf-fp-sheaf-tensor-product vs lem-trf-invertible-affine-limit-descent: the existing node descends invertible modules along scheme limits; it does not assert tensor permanence for arbitrary finitely presented modules.
lem-trf-fp-sheaf-tensor-product vs lem-sc-meromorphic-sheaf-generic-product: the existing node computes rational-section sheaves as products of generic stalks, not finite presentations of tensor products.
lem-trf-fp-sheaf-tensor-product vs def-weil-pbc-coherent-formal-module: the existing node defines coherent formal modules, not tensor permanence for arbitrary finitely presented sheaves.
lem-trf-fp-sheaf-tensor-product vs lem-weil-pbc-coherent-support-union-exact-sequence: the existing node gives a support decomposition exact sequence for coherent sheaves, not arbitrary finitely presented tensor products.
lem-trf-fp-sheaf-tensor-product vs lem-weil-pbc-invertible-pullback-tensor: the existing node gives pullback, tensor and fibre formulas for invertible factors, not tensor permanence without invertibility.
lem-trf-fp-sheaf-tensor-product vs lem-weil-pbc-coherent-formal-modules-abelian: the existing node concerns the abelian category of coherent formal systems, not this scheme-sheaf finite-presentation property.
lem-trf-fp-sheaf-tensor-product vs lem-weil-pbc-affine-tilde-tensor: the existing node identifies tensor products of associated sheaves on affine schemes with the associated module tensor; it does not assert finite presentation for arbitrary schemes.
lem-trf-fp-sheaf-tensor-product vs lem-weil-pbc-quasi-coherent-tensor-product-affine-sections: the existing node gives quasi-coherence and the affine section comparison, not finite presentation.
lem-trf-fp-sheaf-tensor-product vs lem-weil-pbc-ideal-times-quasi-coherent-affine-sections: the existing node gives ideal-product, quotient and power section calculations; it neither assumes finite presentation of two factors nor concludes tensor finite presentation.
lem-trf-fp-sheaf-tensor-product vs lem-sc-invertible-tensor-qcoherent: the existing node proves quasi-coherence of twists by powers of an invertible module; it does not give finite presentation for arbitrary factors.

## Review by Q100

I checked the statement of the item against limits.tex, lemma-descend-invertible-modules (Tag 0B8W), proof of (2), and the exact module-descent statement immediately before it, lemma-descend-modules-finite-presentation (Tag 01ZR). The source first obtains finite locally free models; the item's construction needs only finitely presented models, which follow directly from 01ZR(1). This is the already selected route of the parent split, and introduces no extra hypothesis. I checked the dual and evaluation against modules.tex, lemma-constructions-invertible (01CT), clause (2), and the tensor finite-presentation property against lemma-tensor-product-permanence (01CE), clause (4). The new statement is exactly that clause restricted to schemes. Every object is introduced; finite presentation is spelled out by a local finite free cokernel presentation, and the three definition dependencies say scheme, module sheaf and sheaf tensor product. The new node contains no proof, proof dependencies, sketch, or unverified Lean attachment.

For step 1 I opened lem-pc-tensor-dual-invertible: its statement explicitly gives invertibility of the dual and the canonical evaluation isomorphism. I applied it with both invertible inputs equal to L, so there is no missing second invertible input. I opened def-sc-invertible-module: it explicitly says locally free of rank one and defines the dual. The finite presentation of a trivial rank-one sheaf is written out, not inferred from a definition of flatness or from a theorem about an unrelated notion.

For step 2 I opened lem-trf-fp-modules-affine-limit-descent: clause (1) is object descent on exactly a small directed qcqs scheme system with affine transitions, not only a theorem about maps. Both L and N satisfy its finite-presentation hypothesis by step 1. Directedness supplies the common upper bound. I opened lem-pc-tensor-pullback-finite-presentation: it handles every scheme morphism with no flatness assumption, exactly what is needed for both transition pullbacks. I opened def-pc-module-pullback: its statement gives the canonical composition isomorphism; together with the cone equations it produces the displayed a,b. These two generic Picard tools are declared in split_report.tool_uses, rather than silently borrowing an off-unit route. No finite-stage invertibility has been assumed.

For step 3 I reread the new statement and 01CE(4). Both A_i and B_i are finitely presented by step 2, so its conclusion gives precisely P_i finitely presented. The structure module's finite presentation is exhibited directly. This is a general tensor theorem requiring its own sheaf presentation argument, not a two-line consequence of the cited descent theorem, and has no inverse-limit or dual hypotheses; it is therefore a proper auxiliary node rather than relabelling the item.

For step 4 I opened lem-weil-pbc-module-pullback-tensor: its statement gives the natural canonical tensor comparison for arbitrary module sheaves, with the formula on pure sections. Its inputs do not have to be invertible, so it applies to A_i,B_i. The tensor of a,b has tensor of their inverses as inverse; then composition with the already obtained e gives exactly epsilon. The proof does not descend that map, assert that the finite-stage factors are locally free, or invoke any of the parent's later isomorphism-descent argument.

I tested the hypotheses and edge cases directly. A singleton system allows A=L and B=N. For the trivial line bundle the evaluation is multiplication O tensor O -> O. Empty schemes cause no difficulty: local presentation conditions are vacuous, and the unique module is its structure module. The new tensor statement also holds when either factor is zero, and for two nonflat finitely presented factors O/(t) on Spec(k[t]); their tensor is O/(t), showing why the new theorem does not need flatness or invertibility. A non-Noetherian scheme causes no additional condition: the source theorem is stated for ringed spaces and uses finite presentations, not coherence. The item's nonempty directed hypothesis is used to choose a common stage. I checked that no cited statement requires the limit itself to satisfy an additional property not supplied in the item. All four steps are below 2000 characters, so no long proof step hides an extra auxiliary assertion. Citations are copied verbatim from node statements, one per uses edge, and the existing statement/dependency metadata was preserved.

I checked B1--B10, C1--C8, D1--D5 and E1--E7 against the actual files and sources: no missing non-elementary tensor assertion remains, no statement is read out of another node's proof, and no SGA source is used. The main correction made during this work was to isolate the sheaf tensor-permanence input and to avoid the tempting but invalid application of ProjectionFormula.isFinitePresentation_tensorObj to models not known invertible.

## Validation

The server review_split check and the initial full deliver.py --no-push preflight passed. Local verification also confirmed the item statement is unchanged and every citations.json quote is part of the indicated statement. Before the final dry run I corrected the source-label spelling in step 4 to modules-lemma-tensor-product-pullback (Tag 01CD), checked in tags/tags and modules.tex.
