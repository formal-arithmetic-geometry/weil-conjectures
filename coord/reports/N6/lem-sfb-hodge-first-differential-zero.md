# Stage-1 delivery: lem-sfb-hodge-first-differential-zero

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-hodge-first-differential-zero.json: item, split; statement preserved; four assembly steps.
- lem-sfb-smooth-projective-complex-field-model: statement, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.
- lem-sfb-algebraic-dolbeault-derivative-comparison: statement, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.
- lem-sfb-projective-harmonic-representatives: statement, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.
- lem-sfb-derivation-cohomology-scalar-square: statement, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.
- citations.json: verbatim statements for all proof citations.

## Attachments

None. Searched the live project WeilConjectures source both for the blueprint id and for Hodge, Dolbeault, harmonic forms, analytification, Kollár and the first differential. No project theorem states the item or any new supporting input. The upstream sorry declarations do not count as proofs. No Lean files were written and no compiler was run.

## Literature wanted

WANTED: Popa, Kodaira dimension of algebraic varieties, proof of Theorem 1.6.6, printed pp.26--27, for the item, lem-sfb-algebraic-dolbeault-derivative-comparison and lem-sfb-projective-harmonic-representatives. The local literature/popa-kodaira-dimension.pdf is absent. I read the Harvard author's PDF online at https://people.math.harvard.edu/~mpopa/271/Kodaira-posted.pdf, including the differential argument and the characteristic-zero scope of section 1.6. No source was downloaded into the read-only repository. The item has proof_origin.by = agent, since the finite-field-model reduction and the explicit comparisons are agent expansions. Neither the source nor this delivery uses an SGA route.

## Corrections and scope

There was no previous sandbox node, proof, report or searches.jsonl to resume; the live node was unsplit. The statement is correct and unchanged. Its reference to ordinary module cohomology does not make d an O-linear map. In particular pqf-def-cohomology by itself does not assert the comparison with underlying vector sheaves; that comparison and the scalar square are explicitly in the new scalar-square node, and the complex comparison has its own vector-sheaf formulation. It would be invalid to use naturality of coherent base change only for O-linear maps to conclude naturality for d. The square node exists precisely to state this additional assertion.

The comparison sign is explicit: with Dolbeault resolution differential bar-partial, the chain map extending d is (-1)^q partial in resolution degree q, because partial and bar-partial anticommute. The sign has no effect on the zero calculation. This was corrected during self-review before delivery.

Read the chapter record, unit record, SETUP's three levels, and latest blueprint sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. This is a supporting input on the existing Kodaira/Hodge branch below the unit, not a change to a chapter or unit. The blueprint ancestor tool returns None for this inherited chain, consistently with the live item's from.node = null; I retained that value and extended the existing via chain and precise place. Whole-blueprint searches for Hodge, harmonic, Dolbeault, finitely generated subfield, field extension and smooth projective found no equivalent statement. Searches by 01ZM found thm-pd-spreading-out; its statement is recorded below as a nonduplicate, not silently treated as a smooth projective model theorem.

## Review by N6

I checked B--E of delivery-errors against the item, four new statement-only files, sources and all cited node statements. Every new file introduces its own fields, schemes, differential, cohomology or analytic spaces and hypotheses; it contains no proof sketch, proof step or proof dependency. All use the inherited chapter and unit. Every recorded search was actually run through msearch.py and its log read. The first two model searches find Algebra.Smooth.exists_subalgebra_fg and related affine smooth-algebra results, which do not produce a projective scheme with its embedding and complex field model; I read Mathlib/RingTheory/Smooth/NoetherianDescent.lean at line 214. Harmonic-search hits include extDeriv_extDeriv and MDifferentiable.exists_eq_const_of_compactSpace; the latter source Mathlib/Geometry/Manifold/Complex.lean says explicitly it treats holomorphic functions, not harmonic representatives of higher cohomology. The comparison searches give abstract sheaf cohomology and cotangent maps, not GAGA or Dolbeault. Scalar-square hits give ring-level KaehlerDifferential.map_D/map_compDer and cotangent maps, not the cohomological compatibility. No hit is an exact match or one-line specialization.

Step 1 cites only the full statement of lem-sfb-smooth-projective-complex-field-model. It supplies k, X_0, the F-model isomorphism, the embedding sigma, and smooth projectivity of the complex base change. All hypotheses come directly from the item. I read Stacks limits.tex 01ZM (lemma-descend-finite-presentation), 01ZP (lemma-descend-closed-immersion-finite-presentation) and 0C0C (lemma-descend-smooth). To take over the model node: choose a projective embedding, write F as the union of its finitely generated Q-subfields, descend the finite-presentation scheme and its embedding by 01ZM, make the embedding closed by 01ZP and the structure map smooth by 0C0C. All stages are spectra of fields, hence qcqs, and transitions are affine. Equivalently homogeneous equations and finite descent data involve only finitely many coefficients. A finite transcendence basis of k/Q maps to algebraically independent complex numbers; the remaining finite algebraic extension embeds into the algebraically closed field C. No embedding of F is claimed. The global model with its projective and smooth structures, rather than the affine-algebra existence supplied by Mathlib, is the input left for the next split.

Step 2 cites lem-sfb-algebraic-dolbeault-derivative-comparison and lem-sfb-projective-harmonic-representatives, and I read their complete statements. The first gives the isomorphisms AND the formula for H^q(d), not just an unnamed equality of dimensions or ordinary GAGA naturality for module maps. The second supplies an actual smooth representative of the chosen class and its d-closedness, not merely an abstract Hodge decomposition. Smooth projectivity of Y is provided by step 1; it gives compact Kähler components and finite disjoint unions in the statements used. Popa's proof on pp.26--27 explicitly identifies the two cohomology spaces with forms of types (0,j), (1,j), takes harmonic representatives and invokes their d-closedness. The new comparison lemma makes the needed arrow compatibility explicit, while the harmonic lemma is an analytic representation theorem with all p,q, not a relabelled algebraic zero-map assertion. To take over the comparison lemma, combine coherent GAGA with the Dolbeault resolution; the (-1)^q sign gives a genuine chain map. To take over the harmonic lemma, Hodge's elliptic theorem yields representatives and the Kähler identity Delta_d = 2 Delta_bar-partial plus the L2 energy identity yields d alpha = 0. These are genuine separate inputs, not assumed elementary in the assembly. The assembly itself then evaluates the derivative on the chosen representative and uses injectivity of c_{1,q}.

Step 3 cites the full scalar-square statement. It applies to k -> C along sigma, with X_0 smooth projective and q >= 0. It states both comparison isomorphisms and the commutative square needed here, including its coefficient categories. Once u_0 tensor C = 0, the coordinate-functional argument written in the step proves faithfulness directly; no finite-dimensionality of the cohomology is used. Choosing a basis containing one nonzero vector and extending a linear coordinate functional is ordinary linear algebra. This is not a new lemma node.

Step 4 cites the same scalar square for k -> F, the full universal property in def-weil-pbc-kahler-differentials, and pqf-def-cohomology for the derived functor. The square supplies surjectivity of beta_0 and the equality of composites. The O-linear derived-functor definition is used only for functoriality under the model isomorphism; the vector-space-sheaf differential has already been constructed in the scalar node. On affine rings an isomorphism carries da to d(image a), so the model isomorphism respects the universal derivation. The conclusion is exactly the item's original map.

For the scalar-square node I read Stacks coherent.tex 02KH (lemma-flat-base-change-cohomology), including its separated finite affine Cech proof, derham.tex 0FL5 (lemma-base-change-de-rham), and cohomology.tex 01F1 (lemma-modules-abelian). I also opened lem-pc-flat-base-change-cohom, lem-pc-flat-cohomology-separated, lem-pc-flat-cech-cohomology-square and lem-weil-pbc-kahler-differentials-base-change. None states the required non-O-linear cohomological arrow compatibility. A future split has the following concrete route: on a finite affine cover of a separated scheme, affine intersections compute both cohomologies by Cech complexes. On an affine ring A the base-change isomorphism is K tensor_k Omega_(A/k) = Omega_((K tensor A)/K) and sends da tensor lambda to lambda d(1 tensor a). Thus the Cech map d satisfies d(a tensor lambda) = da tensor lambda in each coordinate and commutes with restrictions, so the square of Cech complexes commutes. Flatness of K/k then identifies their cohomology tensor K with base-changed cohomology by 02KH. Comparison after forgetting to abelian sheaves uses 01F1/03FD and can be computed with the same acyclic resolutions in vector sheaves. These facts are in the new node's statement rather than being hidden uses of a definition in the item. This node does not assert the vanishing it is used to descend.

Small cases: the empty scheme gives zero complexes throughout; a disconnected scheme or components of different dimensions are covered componentwise in the two analytic inputs. In degree zero, global functions on a smooth projective complex component are constant, agreeing with the harmonic calculation. For finite etale zero-dimensional schemes, relative differentials vanish, including schemes not geometrically connected over the original field. For q beyond component dimension the relevant forms and cohomology vanish, and the argument still applies. No finite-dimension or connectedness hypothesis was slipped into the tensor-detection argument; arbitrary field cardinality is harmless because only k embeds into C. The scalar node is stated even in positive characteristic because it only asserts base-change compatibility, not degeneration.

All four proof steps have fewer than 700 characters; there is no long step hiding an independent comparison or existence claim. Every non-elementary input is a cited statement; citations.json copies those statements verbatim. No new node repeats a clause of the item: the analytic inputs concern representation and comparison, the model input concerns descent, and the scalar square concerns compatibility, with no zero-map conclusion. The only off-unit proof citation is pqf-def-cohomology, declared as a generic tool in split_report.tool_uses. The new nodes are unsplit, not falsely claimed proved.

## Unfinished work

No part of this stage-1 split is knowingly unfinished. The four new nodes are intentionally statement-only, as required for a one-level split; their proofs are future queue items. The local Popa source remains WANTED. Delivery verification results follow below.

## Not duplicates

lem-sfb-smooth-projective-complex-field-model vs lem-sc-generic-pointed-etale-cofinality: the existing node states initiality of the generic-point etale-neighborhood functor, not a projective field model; the new node states the global smooth projective field model and complex embedding.

lem-sfb-smooth-projective-complex-field-model vs lem-sc-generic-pointed-etale-extension: the existing node states extension of a pointed etale neighborhood, not a smooth projective model over a finitely generated characteristic-zero field; the new node states the global smooth projective field model and complex embedding.

lem-sfb-smooth-projective-complex-field-model vs lem-weil-pbc-etale-finite-data-descent: the existing node states descent for etale objects and finite diagrams over a pre-existing scheme limit, not smooth projective models and complex field embeddings; the new node states the global smooth projective field model and complex embedding.

lem-sfb-smooth-projective-complex-field-model vs lem-weil-pbc-finite-diagram-lift-of-models: the existing node states arrow and relation lifting for models already supplied; it explicitly does not assert object descent; the new node states the global smooth projective field model and complex embedding.

lem-sfb-smooth-projective-complex-field-model vs lem-per-ind-etale-alteration-object-degree-descent: the existing node states eventual alteration conditions over a fixed etale inverse system, not a characteristic-zero complex field model; the new node states the global smooth projective field model and complex embedding.

lem-sfb-smooth-projective-complex-field-model vs lem-zl-smooth-affine-filtration-finite-field-descent: the existing node states descent of a prescribed affine filtration from an algebraic closure of a finite field, incompatible with the characteristic-zero model problem; the new node states the global smooth projective field model and complex embedding.

lem-sfb-smooth-projective-complex-field-model vs lem-zl-smooth-affine-frontier-stratification: the existing node states stratification and descent over finite fields, not a complex model of a smooth projective scheme in characteristic zero; the new node states the global smooth projective field model and complex embedding.

lem-sfb-smooth-projective-complex-field-model vs lem-nagata-one-affine-subring-extension: the existing node states extension of supplied compatible chart subring models by one chart, not a projective scheme with an embeddable field of definition; the new node states the global smooth projective field model and complex embedding.

lem-sfb-smooth-projective-complex-field-model vs thm-pqf-immersion-descent: the existing node states factorization of a quasi-finite scheme inside a finite stage of relative normalization, not smooth projective field descent; the new node states the global smooth projective field model and complex embedding.

lem-sfb-smooth-projective-complex-field-model vs lem-pc-bounded-complex-base-change-enlargement: the existing node states base change of a bounded complex along already given maps, and explicitly no new descent assertion; the new node states the global smooth projective field model and complex embedding.

lem-sfb-smooth-projective-complex-field-model vs lem-pc-proper-flat-single-noetherian-descent: the existing node states a proper module model over a Noetherian base; it neither supplies a projective smooth field model nor embeds the field into C; the new node states the global smooth projective field model and complex embedding.

lem-sfb-smooth-projective-complex-field-model vs lem-pd-finite-separable-datum-refinement: the existing node states refinement of descent data in a separable closure over a fixed field, not a complex embedding and projective smooth model; the new node states the global smooth projective field model and complex embedding.

lem-sfb-smooth-projective-complex-field-model vs thm-pd-spreading-out: the existing node states general finite-presentation object/arrow/equality descent; smoothness, closed projective embedding and an embeddable characteristic-zero field model are not in its statement; the new node states the global smooth projective field model and complex embedding.

lem-sfb-derivation-cohomology-scalar-square vs lem-weil-pbc-top-degree-abelian-neighborhood-zero: vanishing of top-degree abelian cohomology classes near a complement, not compatibility with a field extension.

lem-sfb-derivation-cohomology-scalar-square vs lem-weil-pbc-top-degree-abelian-open-restriction: surjectivity of top-degree restriction to opens, not a scalar-extension derivative square.

lem-sfb-derivation-cohomology-scalar-square vs lem-weil-pbc-top-degree-module-restriction-surjective: surjectivity for an open restriction of module cohomology in top degree, not all-degree field base change.

lem-sfb-derivation-cohomology-scalar-square vs lem-weil-pbc-top-degree-open-restriction-surjective: top-degree open restriction for arbitrary modules, not the derivation square.

lem-sfb-derivation-cohomology-scalar-square vs lem-sfb-spectral-module-top-degree-restriction: top-degree restriction on a spectral space, without field extension or universal derivations.

lem-sfb-derivation-cohomology-scalar-square vs lem-sc-fraction-field-sections-base-change: degree-zero sections after passage from a domain to its fraction field; no derivation or higher cohomology square.

lem-sfb-derivation-cohomology-scalar-square vs lem-per-regular-point-blowup-acyclic: regularity and degree-one acyclicity of a surface blowup, unrelated to the field-extension square.

lem-sfb-derivation-cohomology-scalar-square vs def-pc-affine-alternating-cech-model: defines a specific Cech complex, not a comparison theorem or compatibility of non-O-linear differentials.

lem-sfb-derivation-cohomology-scalar-square vs def-pc-flat-cohomology-comparison: defines beta and gives naturality for commuting module squares; it does not make d an O-linear module morphism and does not assert this derivative square.

lem-sfb-derivation-cohomology-scalar-square vs lem-pc-flat-base-change-cohom: module base-change isomorphisms only, without non-O-linear differential compatibility.

lem-sfb-derivation-cohomology-scalar-square vs lem-weil-pbc-kahler-differentials-base-change: ring-level differential-module base change only; the new input is the higher cohomology square and agreement of coefficient categories.

lem-sfb-derivation-cohomology-scalar-square vs lem-coef-inert-marked-restriction-fibration: the latter asserts restriction fibrations between marked lift quasicategories, without schemes, differential sheaves, or cohomological base change.

lem-sfb-derivation-cohomology-scalar-square vs lem-coef-infinity-isofibration-exponentiation: the latter asserts an exponential corner isofibration for quasicategories and Kan fibrations of mapping spaces, without a sheaf-cohomology square.

lem-sfb-derivation-cohomology-scalar-square vs lem-coef-infinity-relative-cone-initial-corner: the latter identifies relative colimit/limit diagrams with initial/final cone objects in quasicategories; it is not a scalar-extension theorem. I opened all three statements; their source tag collision with 01F1 does not express a mathematical overlap.

## Delivery verification

The first packaging checks listed same-tag collisions; I opened their statements and recorded the mathematical distinctions above. A server preflight then rejected the harmonic node because its grouped definition references were not recognized as individual citations. I expanded all new-node grouped references into separate bracketed ids and regenerated citations.json. This is a citation-format correction only. No statement hypothesis or conclusion changed.
