# Worker report

## Files written

- dag/nodes/sec-trace-formula/lem-trf-projective-bundle-proper.json: existing statement, repaired split, statement unchanged verbatim, three assembly steps totaling 2349 characters (2026-10-23 retry; earlier counts below are historical).
- dag/nodes/sec-trace-formula/lem-trf-symmetric-algebra-open-restriction.json: new statement-only unsplit node; no Mathlib match for the graded sheaf algebra comparison.
- dag/nodes/sec-trace-formula/lem-trf-projective-bundle-affine-presentations.json: new statement-only unsplit node; no Mathlib match for local finite generators together with finite-projective-space embeddings.
- citations.json: a verbatim statement quotation for each citation of every assembly step.

## Attachments

None. The only exact project theorem found is AlgebraicGeometry.projectiveBundle_proper in lean/Sheaf/TraceFormula/ProjectiveBundleProper.lean:55, whose proof is sorry. Searches by the blueprint tag and by projective-bundle/properness notions in lean/WeilConjectures yielded no exact closed project declaration. The globally generated projective-bundle theorem in lean/Sheaf/AlgebraicGeometry/GloballyGeneratedProjectiveBundle.lean:66 also contains sorry; it neither supplies an attachment nor includes the new local-cover conclusion.

## WANTED

None. All sources used are present in literature/stacks-project. No SGA source is used.

## What was wrong and what changed

The following records the earlier re-split, retained as history. The current landing-refusal repair is recorded in the new section immediately below.

The return dated 2026-10-22 requests redistribution of the five-step, 3679-character proof into at least two comparable, independently assignable statement-only nodes, while keeping the item statement and an assembly of at most 3000 characters. There was no DAG file, report or searches.jsonl retained in this sandbox at startup, only dispatcher brief markers. I read the current repository's returned five-step proof as the baseline, saved it as baseline.json in the sandbox, and preserved it verbatim in the appendix below. I changed only split-owned fields of the item. Its statement, Lean metadata, historical blueprint information and maintainer fields are retained.

The two new tasks divide real arguments rather than dividing the properness conclusion into renamed clauses. One is a comparison theorem for graded algebra sheaves, without any properness assertion or finite-type hypothesis; the other constructs a target atlas with finite generators and closed embeddings of local projective bundles, without asserting properness of the original morphism. Both have empty proof and proof_deps, null proof_origin and Mathlib match, status unsplit. Other workers can split them independently. The algebra-comparison task is the substantial first portion of old Step 2 (1103 characters); the atlas task is old Step 1 (972 characters) and the finite-space part of old Step 3. Their intended workloads are comparable. The parent retains the geometric gluing and properness assembly.

Argument accounting, with nothing dropped:

1. Old Step 1: the initial factorization X -> P -> S stays in new Step 1. Every finite-type neighbourhood, affine refinement, restricted epimorphism, standard-basis section, zero-generator padding, covering and restricted quasi-coherence argument is assigned to lem-trf-projective-bundle-affine-presentations.
2. Old Step 2: comparison of affine section algebras, degree preservation by products of degree-one sections, equality of coefficient and generator restriction maps, and their identity/composition compatibility is assigned to lem-trf-symmetric-algebra-open-restriction. Its statement asks for the actual graded sheaf isomorphism and the identity on affine sections, not just bijections of ungraded section rings. Agreement of Proj charts, localized overlap maps and cocycles, followed by the compatible gluing isomorphism, remains explicitly in new Step 2.
3. Old Step 3: applying the existing globally generated projective-bundle result to the constructed finite generators is assigned to the local-presentation task. H-projective properness and the use of the over-U gluing identification remain in new Step 2. Instead of silently transporting properness, the assembly transports the closed embedding and applies H-projective properness to the actual projection P_U -> U.
4. Old Step 4 remains in new Step 3: the inverse image of P_U under i is exactly f^{-1}(U); closed-immersion base change therefore applies to the right square, and the proper-composition clause gives properness of the restriction of f.
5. Old Step 5 remains in new Step 3: the chosen opens cover the entire target, so target locality concludes properness of f, even for an infinite cover.

## Repair of landing refusal — 2026-10-23

The return asks for rebasing the approved side completion onto the current DAG, re-reading changed citations, adjusting the split and pushing again. I ran the prescribed dry run first; it completed with exit 0 and OK (not pushed) at 1cbb1e1b910. I then rebased the sandbox item explicitly from the current shared item, overlaying only proof, proof_deps, proof_origin and split_report. Its statement remains byte-for-byte equal to baseline.json, and current maintainer, Lean and historical metadata are retained. Both new node ids remain absent from the current shared DAG. The released stage-1 repair note still requires these two independent tasks; the old reviewed record is not a reason to discard them. deliver.py fetches current origin/sheaf-dag and constructs the fresh delivery there. Promotion of the side completion belongs to L, exactly as the return says; no repository or launcher file was edited.

I compared every assembly citation against rebase-audit.json, and none of its statement, status or reviewed fields changed. I nevertheless re-read all eleven cited statements and the statement dependencies of both new nodes in the current DAG, including the quasi-coherent symmetric-algebra affine-section clause, symmetric grading, finite-type definition, global generating sections and the existing global-generation H-projective result. rebase-audit-current.json records the complete current statements and comparison. The current quotient-geometry node gives the resulting geometric restriction but not the normalized graded algebra comparison or the finite-generator atlas, so the existing duplicate distinctions remain valid. The repeated blueprint searches for symmetric algebra open restriction and finite projective space returned no matches and confirmed the inherited ancestor.

The concrete adjustment is Step 2: it now invokes rho_U(U) by name and writes the structural equation p_alpha j_alpha theta = pi_U theta = pi|_{P_U}. The relative-Proj definition and existence statement explicitly supply the two affine restriction models and compatibility with structural maps. Thus the transported closed embedding is a factorization of this actual projection over U. This is a mathematical clarification of the retained proof on the current definitions, not an unchanged re-push. The two extracted statements, logged searches and source citations are retained without a changed search question.

For this retry I opened Morphisms 01W8, 01WB, 01WC and the finite-global-generation paragraph of 087S, and Modules 01CG, 01CI and 01CL. The first new task still constructs finite generators on affine neighbourhoods and their finite-space embeddings; the second supplies the graded restriction comparison normalized on generators. Neither asserts the item's properness conclusion. The existing exact project theorem at ProjectiveBundleProper.lean:55 still has sorry; no exact closed declaration was found under WeilConjectures. I re-read Mathlib module-restriction signatures and absolute-Proj properness: these do not assert either extracted statement. The original searches, including the unavailable LeanSearch and invalid first Loogle attempt, remain honestly recorded.

I repeated B-E with the current statements open. Step 1 uses only the projective-bundle presentation and the atlas task. Step 2 uses the algebra task, the actual affine-Proj existence clause, the definition of a closed immersion to check precomposition with theta, and the H-projective properness theorem in the finite-space convention. Step 3 uses the base change of i along P_U -> P with source exactly f^{-1}(U), proper composition clause (b), and unrestricted open-cover locality. Every per-step quote remains verbatim and every non-elementary input is cited. The zero module admits one padded zero generator and empty projectivization; the empty base is harmless; E = O_S gives P^0; a finite-type non-locally-free module needs no frame; an infinite affine cover requires no uniform number of generators. No added finiteness, separatedness or local-freeness hypothesis occurs. All three steps are below 2000 characters and the assembly below 3000. The detailed original handoff and signed Review by Q116 are retained below.

## Repair of landing refusal at 9d3596a72a5

The current return is the 2026-10-22 06:50 UTC entry: the reader approved the split, but landing refused the side-project completion because it had not been promoted to the live queue DAG. This retry preserves that approved mathematical work. I compared the retained returned item and baseline with the current shared DAG without git commands. The current item is byte-equivalent as JSON to baseline.json; the only sandbox differences before this repair were proof, proof_deps, proof_origin and split_report. Neither of the two new node ids exists in the current shared DAG. The released stage-1 repair note still requires two independently assignable nodes and an assembly under 3000 characters, so the old passing reviewed record does not supersede this repair.

I started the prescribed dry run before editing; it exited 0 and printed OK (not pushed) at 39ccde8cec9. I read the delivery command: it fetches current origin/sheaf-dag, uses that commit as the delivery parent, and overlays only the fields stage 1 owns. It keeps current maintainer metadata rather than treating the old side-project completion as the base. I did not change the launcher or repository. This is a freshly based delivery, not a re-push of 9d3596a72a5.

I opened and re-read all current assembly citations, including the current relative-Proj definition and existence theorem, H-projective convention and properness theorem, closed-immersion definition, closed-immersion base-change and composition statements, and target-locality statement. Every retained citations.json quotation is still a verbatim part of the current statement; rebase-audit.json records the reviewed statements and hashes in the sandbox. No retained quoted statement needs replacement. I also re-read both new statements and their defining statement dependencies, the globally generated H-projective statement, and the current quotient-geometry statement used in the duplicate review. The current generic properness-locality node is a Mathlib leaf and allows arbitrary open covers. No dependency requires new hypotheses, a finite cover, a locally free module or an affine-intersection assumption.

The concrete split repair is in assembly Step 2. The previous text invoked compatible gluing on all affine refinements of U. The current text uses the stronger explicit affine restriction data already supplied by def-nagata-relative-proj and lemma-nagata-relative-proj-exists: since each selected U is affine, the two restricted projective bundles have the Proj models of Gamma(U,A) and Gamma(U,B). The new algebra-comparison node applied at W=U identifies those graded rings, their scalars and their degree-one generators with the same symmetric algebra. Hence their Proj charts and localized overlap maps agree over U. Transporting the local finite-space closed embedding then gives H-projectivity of the actual projection P_U -> U. This spells out the precise current cited clauses and keeps every argument of the approved split. It does not create another geometric-comparison node or bypass either extracted task.

The source review was repeated from the present local Stacks files: Morphisms Tags 01W8, 01WB, 01WC and the finite-global-generation paragraph of 087S; Modules Tags 01CG, 01CI and 01CL. The existing logged searches were read and retained because neither new statement nor its Mathlib search question changed. I reread the restriction signatures in Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:348-395 and the absolute Proj properness instance in ProjectiveSpectrum/Proper.lean:372; neither states the new graded algebra comparison or affine-cover embedding result. No unrun search has been added.

I checked B-E again against the rewritten assembly. Steps 1 and 3 keep the presentation, cover, correct pullback source, closed-immersion composition and arbitrary-cover locality argument. Step 2 uses actual affine-restriction theorems, not only a definition for an existence claim. The algebra comparison is supplied by the first new task, and local embeddings by the second; their proofs remain empty. The zero module, empty scheme, non-locally-free finite-type module and non-quasi-compact base cases remain valid. All citations and dependencies still agree, and every assembly step is under 2000 characters. The final dry run and direct delivery below supersede the earlier validation receipt. A fresh blueprint search confirmed the same ancestor and no match for either new statement; four additional same-tag candidates in the current DAG were opened and distinguished in Not duplicates.

## Repair of current return at 3b511d729a5

This retry addresses the actual current return, dated 2026-10-22 11:06 UTC, at branch head 3b511d729a5. The earlier 9d3596a72a5 repair above is preserved as history. Before editing, the required full dry run exited 0 and printed OK (not pushed) at e0a6c54971d. I compared the retained split and baseline with the current shared DAG: the current item still equals baseline.json, and only the four split-owned fields proof, proof_deps, proof_origin and split_report differed from the retained delivery. Both new node ids are still absent from the current shared DAG. All eleven saved assembly-citation statements and their available current status/review records agree with rebase-audit.json; no changed citation needs replacement. I nevertheless opened every current cited statement again. The delivery tool will form a new commit on current origin/sheaf-dag, retaining the current maintainer fields; promotion of the side completion belongs to L, as the return itself says.

The concrete adjustment is in Step 2: name the common graded algebra C and the affine restriction isomorphisms a and b supplied by the relative-Proj existence statement. Their composite theta=b^{-1}a is the comparison over U, with the equation pi_U theta=pi|_{P_U}. Composing j_alpha with theta now explicitly gives the H-projective factorization of the actual restricted projection. The topological homeomorphism and surjective sheaf-map checks explain why that composite is a closed immersion. This keeps the two extracted arguments and their entire handoff, while making the comparison and its structural-map direction reviewable. I also corrected the first algebra Loogle attempt's verdict: its unknown identifier is an invalid query, not evidence of absence. Its original query/results and searches.jsonl are unchanged, and the valid second Loogle attempt remains recorded.

For this retry I re-read the item against Stacks 01W8(1), the full proofs of 01WB and 01WC, and the finite-global-generation paragraph of 087S; I re-read Modules 01CG, 01CI and 01CL for the algebra task. The omitted proof of 01CI is still assigned to the extracted task with the original affine-generator argument preserved below. The current module restriction and absolute-Proj properness Mathlib signatures were re-read; neither is the new comparison or atlas theorem. The statements and search questions of both new tasks are unchanged, so their genuine recorded searches are reused rather than invented or repeated.

I rechecked B-E in the new assembly. Step 1 takes the presentation from def-trf-projective-bundle-morphism and the affine cover/embeddings from lem-trf-projective-bundle-affine-presentations. Step 2 takes the graded affine identities from lem-trf-symmetric-algebra-open-restriction, the actual affine restriction isomorphisms and structural-map compatibility from def-nagata-relative-proj and lemma-nagata-relative-proj-exists, and the finite-space properness conclusion in precisely the convention of def-kun-projective and lem-kun-projective-implies-proper. Step 3 uses arbitrary base change of a closed immersion, proper composition clause (b), and arbitrary open-cover locality, with X_U=f^{-1}(U) because f=pi i. Each cited node's statement supplies that exact assertion. citations.json is revalidated without modifying its verbatim quotes. For the empty scheme, E=0 (padded by one zero generator), E=O_S, a non-locally-free finite-type E and an infinite affine cover, the same hypotheses and structural equations apply. No affine intersection or finite cover is assumed, no target or unit route changes, and neither new task restates properness. These checks supplement my signed Review by Q116 above.

## Searches and reuse

Before creating the nodes I searched the whole DAG by projective-bundle, projective bundle, locally H-projective, restriction, symmetric algebra, 01WB, 01OB, 01B5, 01CG, 01CL and 01CI, and read candidate statements. I ran tools/blueprint_refs.py ancestor lem-trf-projective-bundle-proper and searches for projective bundle, symmetric algebra, restriction, 01WB, 01OB, symmetric restriction, locally projective, symmetric algebra open restriction and finite projective space. The nearest blueprint ancestor is lem-trf-local-term-locality; the new nodes have the inherited via list with this item prefixed. No blueprint node states either new algebra-comparison or local-presentation statement. The existing quotient-geometry node already states the resulting bundle restriction isomorphism, so I did not create a duplicate geometric restriction node.

All new-node Mathlib searches were run with the required msearch.py command and are in searches.jsonl, with their exact tool/query and actual results in the nodes. Both nodes have LeanFinder, Loogle, source grep and LeanSearch attempts and a second phrasing. The affine-presentation LeanSearch attempt returned rate-limit unavailability, recorded as unavailable. The first algebra Loogle query reported unknown identifier Sheaf; the second valid quoted-word query returned only symmetric monoidal category instances, which are not symmetric-algebra comparisons. LeanFinder returned module restriction maps, tilde restriction, and absolute Proj construction/properness/finite-type results. I read the module restriction signatures (Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:348, 390, 395) and Proj properness instance (Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean:372). They do not state either new lemma, nor give one-line specializations. Whole-Mathlib grep found no IsHProjective, IsProjectiveBundle, locallyProjective or locally_projective. The item's previous searches are retained because its statement and search question did not change; their recorded affine-Proj properness candidate was reread.

## Review by Q116

I read the item statement against Morphisms Tag 01W8 (definition-projective), clause (1): E is a finite-type quasi-coherent module, not necessarily locally free, and the closed embedding is into its projective bundle over an arbitrary scheme S. I read the full proofs of Tag 01WB (lemma-characterize-locally-projective) and Tag 01WC (lemma-locally-projective-proper), and the finite-global-generation paragraph of Tag 087S (lemma-projective-over-quasi-projective-is-H-projective). The item keeps exactly that projective-bundle convention; no ample line bundle, Noetherianity, finite presentation, separatedness of S, uniform rank or quasi-compactness is introduced.

For the algebra-comparison node I read Modules Tag 01CI (lemma-pullback-tensor-algebra), which gives symmetric-algebra compatibility with pullback, and Tag 01CG (lemma-local-tensor-algebra), which describes each symmetric power by sheafification, as well as Tag 01CL (lemma-whole-tensor-algebra-permanence). I also read the existing quasi-coherent symmetric-algebra and symmetric-grading nodes. The comparison is normalized on scalars and degree-one sections, so every product has the same degree and every affine restriction has the same values on its algebra generators. This is why the requested comparison preserves the grading and commutes with further restrictions. Tag 01CI has an omitted proof; the explicit generator/affine-overlap argument from old Step 2 is preserved in the appendix as the work handed to the future worker. I did not pretend the source states the normalization formulas verbatim or that the definition of relative Proj proves an arbitrary comparison.

For the affine-presentation node I checked the hypotheses of the globally generated result in its full DAG statement: finite type, quasi-coherence and a finite generating family. These hold after restricting a finite-free local epimorphism and refining its domain to an affine open (affine-basis node read). Images of the standard basis supply sections that generate in precisely the sheaf-surjectivity sense of def-weil-pbc-generating-sections; no surjectivity of sections over arbitrary opens is assumed. The existing global-generation theorem supplies the finite-space closed embedding on that open, using the same H-projective convention. Its statement does not supply the cover or generators that the new node must construct. The old detailed argument is preserved below for this independent task.

For new assembly Step 1 I opened both cited statements: def-trf-projective-bundle-morphism supplies exactly the presentation and finite-type quasi-coherent module, and lem-trf-projective-bundle-affine-presentations supplies the covering, finite sections and local finite-space embeddings. Absorbing the over-S isomorphism into a closed embedding is immediate from the definition. The step claims no properness prematurely.

For the original Step 2 I opened the new algebra-comparison statement and all five existing cited statements. The current affine-specialized Step 2 is checked in the landing-refusal repair section above. The new node gives the graded affine identifications and their restriction compatibility. def-nagata-relative-proj specifies the actual charts and localized overlap maps, while lemma-nagata-relative-proj-exists, separately cited, supplies existence and unique comparison respecting the affine charts and structural maps. Their combination applies to the same gluing datum, without requiring intersections of affine opens to be affine. I checked def-weil-closed-immersion: precomposition with an isomorphism preserves its homeomorphism and surjective sheaf-map conditions. def-kun-projective then gives the H-projective factorization of the actual P_U projection, and lem-kun-projective-implies-proper states precisely the properness consequence in that convention. This repairs the potential C4 error of citing only a construction's definition for its existence/uniqueness theorem.

For Step 3 I opened lem-weil-pbc-closed-immersion-base-change, lem-weil-pbc-closed-immersion-proper and lemma-nagata-projective-target-local. The first allows arbitrary scheme base change, including P_U -> P. The source is X_U because f equals pi composed with i, not because of an unproved image-factorization claim. Clause (b) of the second states exactly that a closed immersion followed by a proper map is proper. The last accepts any open target cover and the properness of each inverse-image restriction, so there is no hidden finite-cover hypothesis. citations.json quotes a verbatim part of each cited statement (the whole statement where useful) for every step; proof_deps is exactly the union of uses.

Small cases: on the empty base the empty affine cover is allowed and the locality conclusion remains valid. The empty open has zero section algebra, and the algebra comparison is still the canonical isomorphism. When E is zero, use a single zero generator so n_alpha=0; its projective bundle is empty and the empty closed embedding into projective zero-space is valid. For E=O_S one gets the identity bundle locally; for E=O_S/(a) it is essential that finite type does not mean locally free, and the comparison and embeddings still make sense. No step needs affine intersections or a finite target cover; no bound on n_alpha is claimed.

I checked delivery-errors B through E against the actual statements and sources. New nodes introduce every object, cite the notions they use, contain no proof sketches or proof dependencies, use single TeX escapes, and have genuine search logs and filled blueprint provenance. Neither new node concludes properness of f, neither depends on this item, and the two tasks do not depend on one another. Existing node candidates and shared source tags are distinguished below. All parent proof steps are below 2000 characters; the assembly is below 3000. The return's one numbered demand is thus addressed with two new parallel tasks, not with a mere text shortening. The required full dry run passed server preflight; direct push follows.

## Not duplicates

lem-trf-symmetric-algebra-open-restriction vs lem-sc-invertible-symmetric-algebra-coproduct: This proves a coproduct assertion for tensor powers of an invertible module in a specified algebra sheaf; the new node compares symmetric algebra sheaves of the same arbitrary quasi-coherent module on two different open bases, preserving grading and generators.

lem-trf-symmetric-algebra-open-restriction vs lem-weil-pbc-quasi-coherent-symmetric-algebra-affine: This asserts quasi-coherence and bijectivity of the affine sheafification unit; it does not compare the two separately constructed graded sheaves on S and its open subscheme U or their further-restriction normalizations.

lem-trf-symmetric-algebra-open-restriction vs lem-weil-pbc-quasi-coherent-symmetric-algebra-core: This gives the ungraded universal property on one fixed scheme; the new node compares constructions on two bases with the full grading and iterated-open-restriction compatibility.

lem-trf-symmetric-algebra-open-restriction vs lem-weil-pbc-quasi-coherent-symmetric-algebra: This gives the ungraded universal property and affine sections on one scheme, not the generator-normalized graded comparison of two independently based constructions with iterated-restriction coherence.

lem-trf-symmetric-algebra-open-restriction vs lem-weil-pbc-symmetric-algebra-sheaf-construction: This defines the sectionwise presheaf and its sheafification; it does not assert the graded comparison under open restriction.

lem-trf-symmetric-algebra-open-restriction vs def-trf-canonical-symmetric-graded-algebra: This specifies the affine-basis algebra and its degree-preserving restriction within one fixed scheme; the new node compares the algebra sheaves constructed on S and on the independently restricted scheme U, including every symmetric degree and iterated restriction.

lem-trf-projective-bundle-affine-presentations vs lem-sc-global-generation-nonvanishing-cover: This concerns the nonvanishing cover of an already globally generated invertible module; the new node constructs affine base neighbourhoods and finite-space closed embeddings for arbitrary finite-type quasi-coherent modules.

lem-trf-projective-bundle-affine-presentations vs lem-per-excellent-quasiprojective-normalized-blowup: This constructs normalized blowups over an excellent Noetherian affine base; the new node is a local projective-bundle atlas over an arbitrary scheme, with no blowup or normalization.

lem-trf-projective-bundle-affine-presentations vs lem-per-surface-point-blowup-geometry: This is regular surface point-blowup geometry; the new node has no regularity, dimension or blowup hypotheses and constructs a projective-bundle atlas.

lem-trf-projective-bundle-affine-presentations vs def-weil-pbc-generating-sections: This defines what it means for specified sections to generate; it asserts neither a finite generating affine cover nor the resulting projective-space embeddings.

lem-trf-projective-bundle-affine-presentations vs def-weil-pbc-module-finite-type-presentation: This defines local finite generation and finite presentation; it does not construct affine neighbourhoods together with H-projective bundle embeddings.

lem-trf-projective-bundle-affine-presentations vs def-weil-pbc-morphism-to-projective-space-by-sections: This defines a morphism from generating sections of an invertible module, not a closed immersion of the projective bundle of an arbitrary finite-type module or a generating cover on its base.

lem-trf-projective-bundle-affine-presentations vs lem-weil-pbc-coherent-kernel-condition-descent-local-generators: This supplies local generating data for kernels under coherent-kernel hypotheses; the new node concerns the original finite-type module and embeds its projective bundles.

lem-trf-projective-bundle-affine-presentations vs lem-weil-pbc-coherent-kernel-condition-descent: This descends finite type of kernels of finite-free maps; the new node assumes only finite type of E and gives projective-space embeddings.

lem-trf-projective-bundle-affine-presentations vs lem-weil-pbc-coherent-kernel-condition-restriction: This restricts a coherent-kernel condition, not a finite-type module atlas with projective embeddings.

lem-trf-projective-bundle-affine-presentations vs lem-weil-pbc-coherent-kernel-intersection-finite-type: This treats finite type of a kernel on an intersection; the new node treats E itself and constructs finite-space embeddings.

lem-trf-projective-bundle-affine-presentations vs lem-weil-pbc-coherent-local-finite-presentation: This supplies finite presentations for coherent modules; finite presentation/coherence is not assumed by the new finite-type projective-bundle atlas.

lem-trf-projective-bundle-affine-presentations vs lem-weil-pbc-coherent-module-finite-type-local-core: This derives finite type from coherence locally or globally, not local projective-space embeddings from finite type alone.

lem-trf-projective-bundle-affine-presentations vs lem-weil-pbc-coherent-module-finite-type-local-cover: This derives finite type from locally coherent restrictions, without projective-space embeddings.

lem-trf-projective-bundle-affine-presentations vs lem-weil-pbc-coherent-module-finite-type-local-restrict: This assumes coherence and proves restricted finite type, without an affine presentation of a projective bundle.

lem-trf-projective-bundle-affine-presentations vs lem-weil-pbc-coherent-module-local-on-open-cover: This proves locality of coherence; no coherence is assumed and no coherence conclusion is asserted in the new node.

lem-trf-projective-bundle-affine-presentations vs lem-weil-pbc-finite-separable-base-refinement: This changes the field base of a given smooth projective morphism; the new node constructs local embeddings over any scheme.

lem-trf-projective-bundle-affine-presentations vs lem-weil-pbc-finite-type-kernel-local-generators: This derives finite generation of a kernel using local generating data; the new node constructs embeddings of projective bundles of E itself.

lem-trf-projective-bundle-affine-presentations vs lem-weil-pbc-finite-type-local-coefficients: This gives local finite sections and coefficient expressions; it does not make the neighbourhoods affine or produce the closed projective-space embeddings required by the new node.

lem-trf-projective-bundle-affine-presentations vs lem-weil-pbc-finite-type-module-stalk-finite: This concerns finite generation of a single stalk; it gives neither a generating cover nor a projective-space embedding.

lem-trf-projective-bundle-affine-presentations vs lem-weil-pbc-generating-sections-stalk-span: This characterizes given generating sections by their stalk spans, not the local atlas and projective embedding conclusion.

lem-trf-projective-bundle-affine-presentations vs lem-weil-pbc-invertible-generating-sections-fibre: This tests generating sections of an invertible module at fibres; arbitrary finite-type modules in the new node need not be invertible.

lem-trf-projective-bundle-affine-presentations vs lem-weil-pbc-module-finite-free-local-lift: This lifts epimorphisms locally along an arbitrary source; it gives no projective bundle or finite-space embedding.

lem-trf-projective-bundle-affine-presentations vs lem-weil-pbc-module-finite-type-image-extension: This treats finite type under quotients and extensions; it does not construct a projective bundle atlas.

lem-trf-projective-bundle-affine-presentations vs lem-weil-pbc-quasi-coherent-finite-type-affine: This compares finite-type modules with finitely generated affine sections; the new node additionally constructs closed embeddings of the associated projective bundles.

lem-trf-projective-bundle-affine-presentations vs lem-sfb-finite-graded-proj-projective: This concerns finitely generated graded algebras over a field with finite-dimensional degree zero; the new node is over arbitrary affine neighbourhoods in any scheme and retains sheaf generators.

lem-trf-projective-bundle-affine-presentations vs lem-sfb-projective-affine-base-blowup: This concerns blowups of an already H-projective scheme over a Noetherian affine base, not local embeddings for projective bundles of arbitrary finite-type modules.

lem-trf-projective-bundle-affine-presentations vs lem-trf-alteration-relative-curve-preparation: This is an alteration and curve factorization theorem over a field or excellent trait, unrelated to the general module atlas conclusion.

lem-trf-projective-bundle-affine-presentations vs lem-trf-projective-bundle-global-generated-h-projective: This assumes a finite generating family globally on the entire base; the new node constructs an affine cover and the finite families from the strictly weaker finite-type assumption, then obtains the local embeddings.

lem-trf-projective-bundle-affine-presentations vs lem-trf-projective-bundle-proper: The item concludes properness of any closed subscheme of a finite-type projective bundle; the new node instead constructs a finite-generator atlas and finite-space embeddings of the ambient bundles, with no properness conclusion.

lem-trf-projective-bundle-affine-presentations vs lem-trf-projective-bundle-to-h-projective: This requires an ample invertible sheaf on the whole base and gives a global embedding of an arbitrary projective-bundle morphism; the new node needs no ample sheaf, constructs the generating cover, and gives embeddings of the local ambient bundles.

lem-trf-projective-bundle-affine-presentations vs lem-trf-relative-marked-nodal-reduction: This is a marked-curve semistable alteration statement with excellent Noetherian hypotheses, not the arbitrary-scheme projective-bundle atlas.

lem-trf-symmetric-algebra-open-restriction vs lem-trf-projective-bundle-quotient-geometry: the existing node already gives the resulting open-restriction isomorphism of projective bundles, including twists and quotients; it does not state a normalized isomorphism of the underlying graded algebra sheaves on every degree and affine section. The new node isolates that finer algebra comparison from old Step 2, not a second geometric restriction theorem.

lem-trf-projective-bundle-affine-presentations vs lem-trf-projective-bundle-quotient-geometry: the existing quotient classification has no finite-type hypothesis and gives no finite global generators or finite-space embeddings on an affine cover. The new node supplies those specific local presentation data.

lem-trf-projective-bundle-affine-presentations vs lem-trf-free-projective-bundle-base-change-space: This compares the bundle of an already free module with base-change projective space; it provides neither a finite-generating affine cover for arbitrary finite-type modules nor their closed embeddings.

lem-trf-projective-bundle-affine-presentations vs lem-sfb-finite-constant-projective-graph: This embeds a given projective scheme over a finite field extension by its graph into projective space over a separated target; the new node starts with an arbitrary finite-type quasi-coherent module on any scheme, without field or target-separation hypotheses.

lem-trf-projective-bundle-affine-presentations vs lem-sfb-equivariant-normal-projective-model: This normalizes a birational equivariant model over a field and proves its projectivity; the new node concerns a module atlas, with no group, birational morphism or normalization.

lem-trf-projective-bundle-affine-presentations vs lem-sfb-projective-pointed-universal-curve-tower: This constructs a tower of stable pointed moduli families over a field; the new node constructs local finite-space embeddings of arbitrary finite-type projective bundles and assumes no curve or moduli data.

## Preserved returned proof and task handoff

This appendix is the old proof, not proof steps in either new node. It records the entire argument so the two future workers have all of the handed-off reasoning, rather than a shortened description that loses work.

### Returned step 1

Unpack [def-trf-projective-bundle-morphism]: write $P=\mathbf P_S(\mathcal E)$ with projection $\pi:P\to S$, and choose a closed immersion $i:X\hookrightarrow P$ over $S$ with $f=\pi i$ (absorbing the given $S$-isomorphism into $i$). By the finite-type clause of [pqf-def-coherent], every point of $S$ has a neighbourhood $V$ carrying a surjection $\mathcal O_V^{\oplus n}\twoheadrightarrow\mathcal E|_V$. Choose an affine neighbourhood $U\subseteq V$ of that point using [lem-weil-pbc-affine-opens-basis]. Restriction is still surjective: the local expressions for a section restrict to their intersections with $U$. The images of the standard basis are thus finitely many global sections of $\mathcal E|_U$ generating it in exactly the sense of [def-weil-pbc-generating-sections]. If $n=0$, use the single zero section instead. These $U$ cover $S$. Quasi-coherence and finite type of $\mathcal E|_U$ follow immediately from their local definitions in [pqf-def-coherent].

Citations: def-trf-projective-bundle-morphism, pqf-def-coherent, lem-weil-pbc-affine-opens-basis, def-weil-pbc-generating-sections.

### Returned step 2

For each chosen $U$, identify $P_U=\pi^{-1}(U)$ over $U$ with $\mathbf P_U(\mathcal E|_U)$. Here this is restriction of the defining gluing datum, not an assumption that the module is locally free. Indeed, for every affine open $W\subseteq U$, clause (b) of [lem-weil-pbc-quasi-coherent-symmetric-algebra] identifies the section algebra in either construction with $\operatorname{Sym}_{\mathcal O_S(W)}(\mathcal E(W))$, sending the same section $e$ to its degree-one generator. These identifications preserve degrees: the degree-$m$ part is spanned by products of $m$ such generators [lem-weil-pbc-symmetric-algebra-graded]. Their restriction maps agree on coefficients and on degree-one generators, hence on all products and sums. Thus the local Proj schemes, their structure maps, their localized overlap maps, and their cocycles are the same in the two constructions of [def-nagata-relative-proj]. Restricting that gluing to the affine cover of $U$ gives the claimed identification, carrying $\pi|_{P_U}$ to the projective-bundle projection $\pi_U$. No intersection of affine opens is assumed affine.

Citations: lem-weil-pbc-quasi-coherent-symmetric-algebra, lem-weil-pbc-symmetric-algebra-graded, def-nagata-relative-proj.

### Returned step 3

The module $\mathcal E|_U$ is finite type and quasi-coherent and is generated by the finite family in Step 1. Therefore [lem-trf-projective-bundle-global-generated-h-projective] applies over $U$ and makes $\pi_U:\mathbf P_U(\mathcal E|_U)\to U$ H-projective. Apply [lem-kun-projective-implies-proper], whose projectivity convention is precisely the finite-projective-space convention, to conclude that $\pi_U$ is proper. Under the over-$U$ identification in Step 2 this is properness of $\pi|_{P_U}$: the separated, finite-type and universally-closed conditions defining properness are unchanged by an isomorphism over the base [def-weil-proper-morphism].

Citations: lem-trf-projective-bundle-global-generated-h-projective, lem-kun-projective-implies-proper, def-weil-proper-morphism.

### Returned step 4

Put $X_U=f^{-1}(U)$. The restriction $i_U:X_U\to P_U$ is the base change of $i$ along the open immersion $P_U\hookrightarrow P$, and is a closed immersion by [lem-weil-pbc-closed-immersion-base-change]. To check the source, $i(x)$ lies in $P_U$ exactly when $\pi i(x)=f(x)$ lies in $U$; equivalently the pullback of the open subscheme $P_U$ along $i$ is the open subscheme $f^{-1}(U)$. The restriction of $f$ is $\pi|_{P_U}\circ i_U$, because $f=\pi i$. Step 3 gives that $P_U$ is proper over $U$. Clause (b) of [lem-weil-pbc-closed-immersion-proper] now says that this composite is proper. Thus every $X_U\to U$ is proper.

Citations: lem-weil-pbc-closed-immersion-base-change, lem-weil-pbc-closed-immersion-proper.

### Returned step 5

The opens $U$ in Step 1 cover $S$, and Step 4 proves properness of every restriction $f^{-1}(U)\to U$. Apply [lemma-nagata-projective-target-local] to this cover. Its conclusion is that $f$ is proper, as required. The cover may be infinite, and properness is only asserted globally after applying this target-locality theorem.

Citations: lemma-nagata-projective-target-local.

## Unfinished work

The new nodes are deliberately statement-only tasks for other workers, as the released re-split order requires. No Lean file or compiler was touched. No source/statement dispute was found. The parent split passed the required dry run and is ready for direct push.

## Prior validation (retained history)

The required deliver.py Q116 lem-trf-projective-bundle-proper --no-push completed with exit 0 and printed OK (not pushed) at 2a8f90f98cc: preflight passed. This ran the server preflight, including check_dag.py and review_split.py. The item statement was also compared byte-for-byte with the returned baseline; the assembly is 1967 characters with step lengths 511, 915 and 541, and both new nodes have no proof steps. The report line reference was corrected to ProjectiveBundleProper.lean:55 before direct delivery; no mathematical content changed after the passing dry run.

## Current validation

After the landing-refusal repair the assembly has 2178 characters, with step lengths 511, 1126, 541. The item statement remains identical to the returned baseline. Both retained new nodes are statement-only; their exact searches and all citations remain intact. A final full dry run on current origin/sheaf-dag and direct delivery follow this report update.

## Validation of retry for 3b511d729a5

Initial server dry run passed at e0a6c54971d. The adjusted assembly has 2234 characters, with step lengths 511, 1182, 541. The item statement remains byte-for-byte identical to the baseline; both new nodes still have empty proof and proof_deps. All per-step citation quotations are checked against current statements. Final server dry run and direct push follow this update.
