# Stage-1 report: lem-sfb-space-qcoh-extension-closed

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-qcoh-extension-closed.json`: statement, split; retained its exact statement, statement dependencies, provenance and earlier searches, and added a seven-step proof and the searches actually logged for Q155.
- `citations.json`: one verbatim statement quotation for each node used by each step.
- No new DAG nodes; zero new Mathlib leaves. `write_split.py` is a sandbox-only preparation script; `searches.jsonl` is the search tool's own log.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag and for extensions/quasi-coherence found scheme Zariski extension theorems, not this theorem for algebraic spaces on their small etale site. In particular `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_shortExact` has a scheme Zariski module signature. I did not claim it as the algebraic-space result.

## WANTED

None. The sources needed for this argument are present.

## Corrections and scope

The unsplit input had no proof. Its statement is correct as written: it is the extension case of spaces-properties.tex Tag 03M1 (lemma-properties-quasi-coherent), clause (4). I kept the statement and its six statement dependencies unchanged. The proof reduces to a scheme chart, as that source requires, and expands the scheme argument using descent.tex Tag 0GNB (lemma-properties-quasi-coherent), clause (4), and Tag 06VE (lemma-equivalence-quasi-coherent-limits), proof of (10). I did not create a node that simply renames the scheme extension case or the original conclusion.

One important potential gap is avoided: an equivalence between the quasi-coherent subcategories does not imply ambient extension closure. The middle term is not assumed quasi-coherent while restricting to the Zariski site or forming the module adjunction counit. Its Zariski restriction is proved quasi-coherent first, using affine section lifting. Only then is the exact association theorem applicable to its short exact sequence. No arbitrary exactness of restriction from the etale topology to the Zariski topology is asserted.

The inherited blueprint ancestry is preserved. `tools/blueprint_refs.py ancestor` reports `None` for this already-created item, and its existing `from.node` is null with a detailed `from.place` and `via` chain. The current blueprint under `literature/blueprint/latest/` and the chapter/unit records were read. The inherited place ends in the 03M1 extension input supporting the perfect-generator reduction in 0D3F, which is all this split realizes. I did not edit the unit record: this is not its key statement node. Whole-DAG concept/tag searches and whole-blueprint searches found no existing blueprint node stating this algebraic-space extension case in another form.

## Not duplicates

No new nodes were created. Existing nodes are reused for scheme association, exact association, Zariski extension closure, affine vanishing, section lifting and exact localized restriction. The existing `lem-sfb-space-qcoh-kernels-colimits` does not supply extension closure and is not used to assert it. The stronger affine-chart calculus node only computes operations after quasi-coherence is known and is likewise not used to infer the middle term's quasi-coherence.

## Review by Q155

I read spaces-properties.tex Tag 03M1 and its localization preliminaries and proof of clause (4); descent.tex Tag 0GNB clause (4) and Tag 06VE parts (5),(10) and their proofs; schemes.tex Tag 01IE (lemma-extension-quasi-coherent); sites-modules.tex the localization section and lemma-abelian; and the affine vanishing portion of etale-cohomology.tex Tag 03P2. I also read the current blueprint proof of `lem-sc-etale-affine-qcoherent`, the Lean statement and proof of `Etale.surjective_app_of_subsingleton_H_one` in `Sites/TorsionAcyclic.lean`, and the statement of every cited node. No new node requires a separate source audit.

Step 1 uses the algebraic-space definition for its site/ring and the representable-etale scheme-test node for both composition and the fact that a morphism between etale charts is etale. Thus the inverse descriptions really identify the localized site with the scheme's small etale site, with identical coverings and rings. The localized restriction lemma explicitly says its restriction functor is exact. Restricting a local presentation is an instance of the local-presentation definition: the slice is further localized and its covering families and free module presentations are unchanged. No algebraic-space chart is silently identified with a Zariski chart.

Step 2 uses the scheme equivalence only on the two known quasi-coherent end terms, producing their quasi-coherent Zariski restrictions. Its inverse and tensor-pullback description are explicitly in its statement. The separate extension/presentation/Hom node states the canonical module adjunction L adjoint R. This gives the counit on the arbitrary middle module, which the restricted QCoh equivalence by itself would not give. The scalar-times-restricted-section formula describes this actual adjunction counit and its naturality; it is not an arbitrary chosen isomorphism.

Step 3 uses the scheme comparison's etale restriction/pullback comparison to identify the kernel on an affine open with the associated sheaf of its quasi-coherent Zariski restriction. The affine vanishing node applies with q=1 to this module. Its cohomology is the underlying abelian sheaf cohomology, matching exactly the section-lifting node. The forgetful-functor node explicitly asserts exactness, so the module extension gives the abelian short exact sequence required there. The test object is the affine open W in the small etale site of the scheme T; it meets the hypotheses of the lifting node. This proves section surjectivity without assuming either N_T or its Zariski restriction quasi-coherent.

Step 4 uses sectionwise kernels, explicitly included in the forgetful-functor node. For the right-hand map, sections lift on affine opens by Step 3; on an arbitrary open, an affine cover therefore provides local lifts. This proves Zariski epimorphy rather than claiming sectionwise surjectivity on all opens. The Zariski extension-closure node applies on the arbitrary scheme T to quasi-coherent end terms and this now-proved short exact sequence. Consequently E is quasi-coherent.

Step 5 applies the exact-finiteness comparison solely to a short exact sequence whose three Zariski terms are now quasi-coherent, solely on the small etale site. Its statement explicitly supplies this ambient exactness. The module adjunction and the scheme equivalence give a counit diagram with invertible end maps. No big-site exactness or pure-extension assertion is imported from 06VE.

Step 6 spells out the short-five-lemma chase in local sections. Injectivity follows from the zero image in the right term and injectivity on the left; surjectivity is local, lifting the image in the right term first and then the difference in the left. This is an elementary diagram chase, not a hidden comparison lemma. The scheme equivalence then supplies quasi-coherence of LE and hence N_T. Step 7 just unpacks the local-presentation definition on the final object of each chart: its covers and presentations are the covers and presentations over that object of X_et. This gives the predicate on every object, without using a nonexistent global final scheme object for X.

I checked zero kernel, zero quotient, the split extension, and empty charts. A zero end term reduces the argument to an isomorphism; no nonzero hypothesis is used. Split extensions give the usual direct sum on each chart. Empty charts satisfy the local predicate vacuously. Affineness is used only on the open test schemes W, never for T or X; no intersections of arbitrary affine opens are assumed affine, and no finite cover or Noetherian/separation condition is introduced. Every step is shorter than 2000 characters. The named dependencies were checked for paths back to the item and none were found.

All off-unit statements are generic tools, declared with reasons in `split_report.tool_uses`: scheme-test localization, exact localized restriction, scheme QCoh comparison, the canonical module adjunction, affine vanishing, exact coefficient forgetting, H^1 section lifting, and Zariski extension closure. They implement the scheme-local argument of the item's source, rather than replacing a step of the unit route.

For Mathlib I ran the required logged commands with Q155 and this item's id: two different LeanFinder phrasings, Loogle, grep and LeanSearch. The results identify the generic local-presentation definition, its data, finite-presentation implications, locally free modules and the category of scheme modules. I read the indicated Mathlib quasi-coherence definitions at lines 248-284; none of those hits asserts this algebraic-space extension theorem. The original searches are retained, and the new records reproduce the tool/query text in the actual sandbox log. No compilation, Lake command, repository mutation, or other agent was used.

## Unfinished work

None in the stage-1 split. The cited unsplit section-lifting node remains its own existing downstream item; its proof is not claimed completed here.

## Delivery validation

The first dry run requested a longer verbatim quotation for the exact slice-restriction lemma. I expanded that quotation to the full exactness-and-adjunction clause; no mathematical change was needed.
