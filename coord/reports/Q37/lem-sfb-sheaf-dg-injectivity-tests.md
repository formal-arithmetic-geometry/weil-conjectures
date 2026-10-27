# Worker report: lem-sfb-sheaf-dg-injectivity-tests

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-sheaf-dg-injectivity-tests.json: item, statement unchanged, eight proof steps, split; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-graded-sheaf-module-grothendieck.json: new statement-only prerequisite, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-sheaf-dg-acyclic-hull.json: new statement-only prerequisite, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-sheaf-dg-small-acyclic-subobjects.json: new statement-only prerequisite, unsplit, no Mathlib match.
- citations.json: one literal full-statement quote per cited node per proof step.
- searches.jsonl: actual msearch.py records, retained in the sandbox. write_split.py is the sandbox-only generation script.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, dg injectivity, graded injectivity, homotopical injectivity, dg hull, small acyclics, DGModule and DifferentialGraded. There is no project declaration stating all the item clauses. No Lean file was written and no compiler was run.

## Wanted literature

None. All proof sources used are present in literature/stacks-project. No SGA source was used.

## What needed attention

The original statement faithfully matches Stacks 0FSY on a topological ringed space, after switching to left modules via the graded opposite algebra; its explicit global Hom-complex formulation requires all shifts. I preserved that statement. The original item had no proof. I have not made a new node for either direction or for graded-injectivity tests alone: the graded category and acyclic hull are smaller structural inputs, and the proof itself carries the adjunction argument and the transfinite induction.

The current blueprint was read at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. This auxiliary item serves the inherited direct-image prerequisite via lem-sfb-flat-ringed-dg-pushpull, not a new geometric route. The imported unit record has an older chapter/path than the current blueprint; I did not change it. blueprint_refs.py ancestor prints None for this item's existing ancestry. New nodes preserve that inherited null ancestor and extend its existing via chain rather than inventing a blueprint id. The existing item place is already specific and remains unchanged.

The two generic statements used from other units are declared in split_report.tool_uses: lem-pur-kinjective-characterize-injective (Baer tests for a generator) and lem-pur-kinjective-ML-ordinals (acyclicity of ordinal inverse limits). Neither changes the blueprint unit's route.

## Source error

Stacks 0FSY's limit filtration sentence writes K_beta = colim K_alpha; the intended continuous filtration is K_lambda = colim_{beta<lambda} K_beta. Its displayed successor sequence of homotopy Hom groups runs in the covariant order. Hom into I is contravariant: the actual short exact sequence of complexes is 0 -> Hom(N_s,I) -> Hom(K_{beta+1},I) -> Hom(K_beta,I) -> 0. Step 7 uses this correct order and the already existing long exact cohomology node. These are proof notation errors, not a false target or a change to its hypotheses. The proof also verifies surjectivity onto each whole earlier inverse limit, not merely pairwise surjectivity, before applying 0AAT.

The statement of 0FST does not explicitly require its selected acyclics to be nonzero; its proof's final paragraph explicitly constructs nonzero acyclic submodules. The new small-acyclic node records this necessary conclusion of the source proof, since otherwise a family consisting of zero would satisfy the weaker text and would not give strict growth.

## Not duplicates

No existing node source contains 0FR0, 0FRD, 0FSK, 0FSL or 0FST (searched the whole live DAG). The following conceptual overlaps were also checked:

lem-sfb-graded-sheaf-module-grothendieck vs lem-sfb-sheaf-dg-grothendieck: the new category forgets the differential and keeps a graded algebra action; the old node is the category of dg modules and cannot be used to assert the graded category is Grothendieck.

lem-sfb-sheaf-dg-acyclic-hull vs lem-sfb-dg-good-character-embedding: the hull is left adjoint to forgetting a differential on sheaves and preserves monomorphisms; the existing node embeds ordinary right dg Z-algebra modules into character-module products, with a different construction and conclusion.

lem-sfb-sheaf-dg-small-acyclic-subobjects vs lem-pur-kinjective-acyclic-quotient-complexes-bounded-size: the existing result concerns ordinary complexes in a Grothendieck category and bounded-above degreewise size bounds; the new node supplies nonzero sheaf submodules stable under a dg algebra action. This dg stability does not follow by a one-line specialization.

lem-sfb-sheaf-dg-small-acyclic-subobjects vs lem-pur-kinjective-characterize-K-injective: the latter assumes small-acyclic hypotheses for ordinary complexes and proves a K-injectivity criterion; it does not supply a set of nonzero acyclic sheaf dg submodules.

Whole-blueprint searches were run for injective, graded, graded module, graded injective, acyclic, acyclic differential, acyclic submodule, ordinal, monomorphisms, Baer, dg hull and small acyclics. None states any of the three new results; same_as is empty. The new names were checked against all DAG filenames before creation.

## Review by Q37

I read sdga.tex 0FSY's full proof and the cited 0FSN, 0FSS, 0FST and 0FSQ, as well as the definition of K-injective (0FSU), the first extension property (0FSW), the graded category proof 0FRD with its abelian category statement 0FR0, the hull 0FSK and 0FSL, and the cone identity contraction in dga.tex lemma-id-cone-null. I read homology.tex lemma-ML-over-ordinals (0AAT) and the general Baer argument in injectives.tex lemma-characterize-injective (079G). Each new node is statement-only, introduces its ringed space and dg algebra, and uses no boundedness, K-flatness, noetherianity or degree-zero-algebra hypothesis.

Step 1 uses the new graded-category statement precisely for its generator and Grothendieck hypothesis. I opened lem-pur-kinjective-characterize-injective: its actual statement permits exactly subobjects of that generator as Baer tests. The new hull statement explicitly supplies the natural adjunction bijections, acyclic values and preservation of monomorphisms. These are exactly the three properties used; a bare adjunction would not be enough. The set of subobjects is checked using the concrete sheaf model, rather than assuming that an arbitrary proper class of monomorphisms is a set.

Step 2 uses the new small-acyclic statement to select its family, and the actual signed shift and cone formulas in def-sfb-sheaf-dg-module-localization for the added tests. The contraction s(x,y)=(0,x) is calculated, including its degree-minus-one A-linearity. Both objects in every test are acyclic, and the indexing set remains a set after adding all integer shifts. No separate cone lemma is hidden here: the formula verifies it directly.

Step 3 is the direct two-line extension argument of 0FSW. The only definitional citation supplies signed shifts. A degree-minus-one map extends because the shifted graded target is injective; I wrote out why the shift equivalence preserves the extension property. Applying the Hom differential to the extension gives a closed degree-zero map with the required restriction. No exactness theorem or presumed injectivity of the underlying O-module is being used.

Step 4 uses the contraction already calculated and the definition's signed source shift. I checked the reindexing: a degree-q cocycle N_s -> I is a chain map N_s[-q] -> I, and the null homotopy equation becomes z=d_I h+(-1)^q h d_{N_s}=delta h. Thus it gives all Hom cohomology degrees, not only degree zero.

Step 5 proves the Hom exactness directly. Degree-q surjectivity is extension of maps into I[q]; the kernel consists exactly of homogeneous maps factoring through C. This is an elementary three-line consequence of graded injectivity and the explicit differential, not an unproved assertion that dg graded injectivity implies termwise O-injectivity. I did not cite lem-pur-kinjective-homotopy-exact-injective-target: its hypothesis is termwise injectivity in the underlying abelian category and is not what this proof has.

Step 6 cites the actual lem-sfb-sheaf-dg-grothendieck statement for exact faithful forgetting, graded colimits, and commutation with cohomology. I read every clause. The existing long exact cohomology statement applies to the underlying short exact sequence of O-complexes, so the quotient and successor preimage are acyclic. The new small-acyclic statement explicitly ensures the quotient submodule is nonzero, so the successor is strict until M is reached. For limit stages, exact filtered colimits and the concrete submodule construction keep the result a submodule. The set of all dg submodules bounds the length of strict growth; no proper-class colimit is taken.

Step 7 uses the same long exact cohomology statement, now in complexes of abelian groups. I checked its actual statement allows integer-indexed complexes in any abelian category and gives the needed three consecutive positions. The two outer Hom complexes are acyclic for the reasons already proved, so the middle one is acyclic. This avoids the reversed displayed homotopy sequence in the source.

Step 8 uses the dg Grothendieck node's graded-colimit clause for the compatible-family identification, not an assertion that inverse limits in sheaves are exact. I opened lem-pur-kinjective-ML-ordinals: it assumes surjectivity H_beta^q -> lim_{gamma<beta} H_gamma^q, not just surjective pairwise transitions. The proof checks this separately at zero, successors, and nonzero limits, and checks acyclicity of all earlier stages by induction. Its conclusion is exactly the needed acyclic limit of complexes of abelian groups. This handles uncountable limit ordinals.

I checked small cases: X empty, the zero algebra, M=0, an ordinary ring concentrated in degree zero, and positive/negative/odd shifts. For an empty space or zero algebra the module category is zero and the small-acyclic set can be empty; no nonzero successor is requested. For M=0 the filtration and Hom complex are zero. For A in degree zero the hull reduces to the ordinary disk construction, while an arbitrary dg differential is handled by the adjunction node rather than an unjustified componentwise disk. The explicit cone contraction respects odd left actions. The degree-q boundary calculation checks both parities. The proof is unbounded throughout.

All new-node Mathlib searches were run through msearch.py, with two semantic phrasings before concluding no match, and actual results copied from searches.jsonl. I read the leading hits in Mathlib's KInjective, Acyclic, GradedModule, GrothendieckAxioms/Sheaf, ModuleCat/Sheaf/Abelian, DifferentialObject and Injective/Preserves files. Ordinary sheaves valued in a fixed category do not immediately provide modules over a varying graded algebra sheaf; generic adjunction preservation lemmas do not construct the hull; ordinary acyclic complexes have no dg-action cardinality statement. No unavailable service was recorded as a negative result. The item's inherited searches were retained and supplemented by this session's searches.

I checked delivery-errors B through E: the new nodes are self-contained statements only; source tags were resolved in the local tags table (including correcting an initially mistyped abelian-category tag to 0FR0); there are no clause restatements, no definition-only citation standing for a theorem, no cycle via the parent, and no extra hypotheses. Every citation's exact full statement is in citations.json. Every proof step is below 1000 characters; no long step conceals a standard lemma. The item statement and all maintainer-owned fields are preserved.

## Unfinished work

The three prerequisites are intentionally unsplit stage-1 queue items. Nothing else in the requested one-level split is left unfinished. Delivery validation follows below.
