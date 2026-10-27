## Worker report

Files written:

- dag/nodes/sec-trace-formula/lem-trf-affine-eventual-power-immersion.json: item split into five steps; statement unchanged.
- dag/nodes/sec-trace-formula/lem-trf-segre-hyperplane-pullback.json: one statement-only node, not in Mathlib; exact project theorem found and recorded in lean_candidates for attachment. No new Mathlib leaves.
- citations.json: every dependency in every item step, with the actual statement quoted verbatim.

Attachments:

AlgebraicGeometry.ProjectiveSpace.nonempty_twistRestrict_segre_iso belongs to lem-trf-segre-hyperplane-pullback, lean/WeilConjectures/AlgebraicGeometry/ProjectiveSpace/SegreTwist.lean:115 (proof ends at 181). The archived local/sorry_map_slopmaster2_liveb2378f05.jsonl.gz record has s=false, ts=false. The candidate takes arbitrary coordinate types, so finite projective-space coordinate types specialize it. The proof is not split again.

WANTED: none.

The item was statement-only, with no claim of a completed project proof. The exact blueprint-tag search under lean/WeilConjectures and the searches by eventual power/ample/immersion found no declaration of the whole item. IsAmple.exists_immersion_affine_base, AmpleImmersionAffineBase.lean:199, supplies one positive power only, so cannot be attached to this item. Its existing DAG node is cited. Mathlib search queries, including two semantic phrasings for each search question, were run through msearch.py and are preserved in searches.jsonl; the new node records exactly its own searches. The hits are basic-open Proj comparisons and Over-category tensor formulas, not a hyperplane-sheaf comparison. No service was unavailable.

No statement dispute was found. The proof of Stacks 01VS has harmless indexing slips (it calls a family of k=(m+1)t sections s_0,...,s_k, and one target twist has an inconsistent superscript). The split uses (m+1)q sections and target dimension (m+1)q-1. It does not reproduce the first paragraph's possible negative displayed homogenizing exponent, because that construction is already the closed one-power theorem. No mathematical hypothesis or conclusion is changed.

Nothing remains unfinished in the item's natural-language split. The new comparison statement is awaiting the maintainer's attachment verification, rather than new proof work.

## Blueprint and existing-node searches

Read the chapter and unit records sec-trace-formula and sk-i-curve-zero and the current main-20261015 local-term-locality proof and unit text. This item is a subsidiary ampleness step in the already recorded stable-modification ancestry of lem-trf-local-term-locality; it does not replace the unit's contracting-correspondence route. The blueprint ancestor command returns lem-trf-local-term-locality. The item retains its exact inherited place and via list; the new node adds the item to via and specifies the final Segre step of 01VS it serves.

Searched all DAG nodes by 01VS, 01Q3, 01WD, Segre, global generation, graph/tuple immersion and twisting pullbacks. Ran blueprint_refs.py search for ample, Segre, external tensor, 01WD, Segre pullback, twisting Segre, graph immersion, immersion composition and eventual power. These found lem-chow-segre, def-chow-segre, lem-chow-tuple-immersion and the existing general global-generation/one-power nodes. No existing statement gives the precise isomorphism now stated in lem-trf-segre-hyperplane-pullback: in particular lem-chow-segre asserts closedness and a very-ampleness consequence, not an isomorphism of the two specified modules. The new node has no proof steps or proof dependencies, and its statement contains no proof sketch.

Generic tool use: lem-weil-pbc-sections-morphism-to-proj-polynomial-ring constructs a morphism from generating global sections. It is declared in split_report.tool_uses; no statement of sk-i-curve-zero provides this algebraic-geometric construction. Other off-unit results are closed project nodes. No tool_uses maintainer field was written.

## Not duplicates

lem-trf-segre-hyperplane-pullback vs lem-trf-affine-eventual-power-immersion: the new node identifies a fixed Segre pullback module for any base and dimensions; the item proves eventual embeddings from absolute ampleness and local finite type.
lem-trf-segre-hyperplane-pullback vs lem-chow-segre: the existing node asserts the Segre map is closed and the external product is very ample; it does not state the exact pullback isomorphism used in step 5.
lem-trf-segre-hyperplane-pullback vs lem-sfb-conjugate-projective-generic-closure: the latter constructs equivariant projective generic closures from finite function-field extensions; it does not identify the Segre hyperplane module.
lem-trf-segre-hyperplane-pullback vs lem-sfb-invariant-pencil-graph-model: the latter constructs normalized graph models of invariant rational functions on normal projective varieties; it does not identify the Segre hyperplane module.
lem-trf-segre-hyperplane-pullback vs lem-sfb-semilinear-equivariant-chow-modification: the latter supplies equivariant projective modifications of proper integral varieties; it does not state an isomorphism of twisting modules.
lem-trf-segre-hyperplane-pullback vs lem-sfb-projective-fibre-product-closed-model: the latter constructs closed projective embeddings of fibre products over a field; it does not identify the specified Segre pullback with the external tensor product.
lem-trf-segre-hyperplane-pullback vs lem-per-equivariant-projective-envelope: the latter produces an equivariant homogeneous projective envelope over a Noetherian ring; it does not identify the Segre hyperplane module.

## Review by Q154

I read Morphisms Tag 01VS, label lemma-quasi-projective-finite-type-over-S, both the first paragraph and the complete final paragraph (morphisms.tex:9413-9508), and Properties Tag 01Q3, proposition-characterize-ample, specifically (1) implies (7). I also read Constructions Tag 01WD, lemma-segre-embedding, including its chosen external tensor product and product sections (constructions.tex:2927-2997), and lemma-projective-space (Tag 01NE, at 2785), which supplies the pullback description. The item matches 01VS specialized to an affine base: absolute ample invertible module and locally finite type morphism suffice; neither properness nor Noetherianity is needed. The new node states only the particular module identification used in that construction, over an arbitrary base. Its project declaration and entire proof were read in SegreTwist.lean:115-181; its archived transitive-sorry flag is false. The source label's tag was corrected from an initial mistaken 01NA to the correct projective-space label (01NE); the final new-node source uses the unambiguous label.

Step 1 uses exactly the statement of lem-weil-pbc-ample-very-ample-immersion-affine-base: a positive exponent a, finite projective dimension m, an immersion over Spec A, and its pulled-back O(1). I checked the hypotheses are exactly those of this item. No eventual assertion is taken from that node.

Step 2 uses the finite-type quasi-coherent twist generation statement of lem-weil-pbc-coherent-twist-global-generation with F=O_T. Its statement explicitly provides finitely many global sections for every exponent above a bound. The finite-type/quasi-coherent condition is checked on affine charts: the ring as a module over itself is generated by 1, precisely the definitions in pqf-def-coherent. Tensoring with the structure module is the tensor unit from def-pur-sheaf-tensor-product. Raising the bound to at least 1 ensures e is positive and all tensor powers used are in their stated range.

Step 3 uses the invertibility conclusion of lem-weil-pbc-invertible-pullback-tensor inductively. The generating-section criterion is converted to a cover by nonvanishing loci by the rank-one local-ring calculation written there: a finite family spanning a rank-one stalk cannot have all coefficients in its maximal ideal. The statement of lem-weil-pbc-sections-morphism-to-proj-polynomial-ring explicitly gives the morphism over Spec A, chart preimages and pullback isomorphism, and thus supplies all that is used. Its finite family can be padded by zero without changing generation. The identification with the relative projective-space notation is the affine restriction explicitly included in def-nagata-relative-projective-space; I read that definition rather than assuming an unstated interface comparison.

Step 4 uses the full tuple-immersion statement of lem-chow-tuple-immersion, including its current blueprint_update: the finite binary product certainly exists. The immersion j is one component. lem-chow-segre says closed immersion over every base, including Spec A; it does not by itself assert that the composite of an arbitrary immersion is immersive. I therefore wrote out the closed-open factorization argument, using the closed-immersion definition to choose the target open V, the exact base-change conclusion in lem-weil-pbc-closed-immersion-base-change and the closed-composition conclusion in lem-weil-pbc-closed-immersion-products. This avoids an uncited composition theorem or assuming h is closed. No separatedness of T or properness is invoked here.

Step 5 uses the new node's actual displayed isomorphism, not the proof of lem-chow-segre. Composite and tensor pullback isomorphisms are explicitly clauses (2) of lem-weil-pbc-invertible-pullback-tensor. The maps to the two factors are j and j_e by the fibre-product construction. Substituting their pullback isomorphisms and associatively regrouping a+e tensor factors are elementary, so this assembly step is marked elementary. It has 668 characters; every step is below 2000 and hides no long comparison proof.

I tested m=0 and q=1 (the Segre product has dimension q-1 or m respectively and its O(1) formula remains valid), T empty (all rank-one sheaves and maps on it are unique; a padded one-element zero family still generates), and A=0 (its spectrum is empty, forcing T empty). I checked d=d0 gives e=b, and d>d0 preserves e>=b. No finite-field, characteristic, properness, connectedness, reducedness, or Noetherian hypothesis was smuggled in. The new statement also covers non-affine S; its project theorem allows an arbitrary base and coordinate types.

For delivery-errors B, the only new node is a self-contained statement with its notions cited, no unsplit proof, an exact Stacks tag/label source and actual search records. For C, I opened every cited node and generated citations.json from those exact statements; the chain introduces no dependence on the item and no cycle. For D, the one-power and generation arguments stay in the item, and the new node is a strictly smaller universal Segre comparison with an existing closed proof, rather than a renamed eventual-embedding assertion. For E, the preceding hypothesis and small-case checks cover every application. The draft correction was the precise projective-space source label; no imported mathematical statement needed repair.
