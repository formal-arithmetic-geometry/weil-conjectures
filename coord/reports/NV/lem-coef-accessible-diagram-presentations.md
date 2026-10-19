# Stage-1 report: lem-coef-accessible-diagram-presentations

Group NV; worker stage1; 2026-10-17. Statement unchanged. Five new statement-only nodes, zero Mathlib leaves. This is a first-reader preparation; no delivery is authorized here.

## Files written

All node files below are in `dag/nodes/sec-six-functors/` inside this sandbox.

- `lem-coef-accessible-diagram-presentations.json`: item, statement, split into seven proof steps; no Mathlib match.
- `lem-coef-accessible-compact-slice-density.json`: statement, unsplit; compact-source slices at a prescribed accessibility cardinal, their filteredness and canonical density; no Mathlib match.
- `lem-coef-infinity-relative-slice-sections.json`: statement, unsplit; relative arrow slices, all coherent sections and source-created slice colimits; no Mathlib match.
- `lem-coef-filtered-cocartesian-section-cofinality.json`: statement, unsplit; HTT's filtered-section theorem for general cocartesian fibrations; no Mathlib match.
- `lem-coef-infinity-filtered-poset-reindexing.json`: statement, unsplit; coherent cofinality and small cardinal-filtered poset replacement; no Mathlib match.
- `lem-coef-functor-spine-tower-mapping-descent.json`: statement, unsplit; spine restriction, mapping-space descent for a countable increasing union and local smallness; no Mathlib match.

`citations.json` contains one verbatim statement quote for each node used by each numbered proof step. `searches.jsonl` is the search command's actual log. `write_split.py` is sandbox-local authoring support, not a project tool modification.

## Attachments

None. Searched the slopmaster2 project declarations under WeilConjectures by the item's blueprint tag and by accessible/compact/filtered/coherent diagram terminology; no declaration supplies all clauses. Also searched upstream master as reference material. No completed Lean proof was substituted for a DAG split. No Lean source or compiler was run or changed.

## Literature wanted

WANTED: Jacob Lurie, Higher Topos Theory, Proposition 5.4.4.3 and its proof, for lem-coef-accessible-diagram-presentations.

WANTED: Higher Topos Theory, Proposition 5.4.2.2(2)-(3), Lemma 5.4.2.4, Proposition 5.3.5.4 and Lemma 5.1.5.3, for lem-coef-accessible-compact-slice-density.

WANTED: Higher Topos Theory, Corollaries 2.4.7.11-12, Proposition 4.2.2.4, Proposition 1.2.13.8 and the relative-slice paragraph of the proof of Proposition 5.4.4.3, for lem-coef-infinity-relative-slice-sections.

WANTED: Higher Topos Theory, Lemma 5.4.4.2, printed pages 432-434, for lem-coef-filtered-cocartesian-section-cofinality.

WANTED: Higher Topos Theory, Theorem 4.1.3.1, Proposition 4.1.1.8 and Proposition 5.3.1.18, for lem-coef-infinity-filtered-poset-reindexing.

WANTED: Higher Topos Theory, the mapping-space argument in Lemma 5.3.4.12 and proof (2)-(3), (6) of Proposition 5.3.4.13, for lem-coef-functor-spine-tower-mapping-descent and the compactness argument in the item.

These places were read online at https://people.math.harvard.edu/~lurie/papers/HTT.pdf; they are not archived in the supplied literature directory. Following the standing brief, the item's expanded proof is marked `proof_origin.by = agent`. Stacks does not state these quasicategory theorems; no invented Stacks tags or SGA route are used.

## Findings and corrections

The imported node was an unsplit statement, not an existing proof. Its two accessibility assumptions and its sharp cardinal inequality agree with the proof route in HTT 5.4.4.3. I found no statement dispute and did not change its statement or its target ancestry.

The main danger is assuming that filtered fibers alone make the whole section category filtered with cofinal evaluations. They do not supply HTT's hypotheses: the slices must also admit the kappa-small lambda-filtered colimits, and postcomposition must preserve them. Step 4 proves those facts using lambda-accessibility, closure of kappa-compacts under existing kappa-small colimits, and the slice-colimit theorem. It does not replace the original simplicial indexing shape by its homotopy category.

During self-review I removed an attempted citation of the existing one-simplex attachment lemma: its hypotheses did not justify arbitrary simultaneous cell attachment. The final Step 3 gives the degreewise pushout argument from unique nondegenerate decomposition. I also explicitly cite the existing functor/cone calculus to justify that the functor objects are quasicategories. The general poset replacement has no cardinality bound on the poset itself: small and kappa-filtered is what the item asks, not a poset of size less than kappa.

The compactness clause is proved in Steps 2-3, rather than moved into a new pointwise-compact-diagram theorem. The simplex, cell and tower arguments retain the natural mapping-space comparisons, so the compactness comparison is an equivalence of spaces rather than just a bijection on components. No new node simply restates a clause of the item. The section theorem concerns arbitrary cocartesian fibrations, the density theorem concerns single objects, and the remaining new nodes are general coherent indexing and mapping calculus.

## Not duplicates

lem-coef-accessible-compact-slice-density vs lem-coef-infinity-compact-approximation: the existing theorem existentially chooses cardinals simultaneously for a finite family and accessible functors; the new theorem works at every prescribed cardinal for which the single category is accessible. Existentially chosen cardinals cannot identify the fixed lambda and kappa in this item.

lem-coef-accessible-compact-slice-density vs lem-coef-accessible-ind-colimit-extension: extension from an Ind presentation concerns existence and uniqueness of extended functors, not filteredness and canonical density of the entire compact-source slice at a fixed cardinal.

lem-coef-accessible-compact-slice-density vs lem-coef-presentable-cardinal-enlargement: enlargement supplies sufficiently large accessibility cardinals; it does not state canonical compact-source slice density for a given cardinal.

lem-coef-infinity-relative-slice-sections vs lem-coef-infinity-pointwise-cocartesian-transport: the existing theorem transports diagrams along a given cocartesian fibration and computes its mapping fibers; the new theorem constructs the relative slice of p, identifies all its sections with compact-source natural transformations, and states source-created slice colimits.

lem-coef-infinity-relative-slice-sections vs lem-coef-infinity-join-cone-calculus: the existing comparison treats cones with a constant source and a varying diagram. The new section construction allows an arbitrary diagram-valued source d and includes fiberwise postcomposition and slice colimits.

lem-coef-filtered-cocartesian-section-cofinality vs lem-coef-accessible-infinity-pullback: the existing theorem proves accessibility of pullbacks of accessible functors; it does not prove filteredness of all sections over an arbitrary small simplicial base or cofinal evaluation under the smaller filtered-colimit hypotheses.

lem-coef-filtered-cocartesian-section-cofinality vs lem-coef-infinity-filtered-cofinal-pullback: the existing theorem concerns a binary homotopy pullback of already strongly cofinal functors between filtered categories. It does not state HTT 5.4.4.2 for sections over arbitrary simplicial sets.

lem-coef-infinity-filtered-poset-reindexing vs lem-weil-pbc-filtered-category-directed-cofinal: the existing result is ordinary filtered-category reindexing by a directed set. The new result concerns arbitrary quasicategories, an arbitrary regular cardinal, and coherent cofinality.

lem-coef-infinity-filtered-poset-reindexing vs lem-coef-infinity-filtered-cofinal-pullback: the existing result implies colimit invariance for its stronger kappa-cofinal functors but supplies no cofinal poset replacement and no general comma-contractibility cofinality criterion. This proof only obtains cofinal evaluations from the section theorem, not the stronger hypothesis of that existing result.

lem-coef-infinity-filtered-poset-reindexing vs lem-coef-infinity-final-index-colimit: the existing result computes a colimit at a final indexing object, not along a general cofinal functor or poset replacement.

lem-coef-functor-spine-tower-mapping-descent vs lem-cbc-spine-inner-anodyne: inner anodyne spine inclusions are asserted by the existing node, but neither functor-category equivalences nor coherent mapping-space descent for inverse towers are its statement.

lem-coef-functor-spine-tower-mapping-descent vs lem-cbc-simplicial-composition-spine: the existing theorem describes composition spaces with fixed vertex data; the new theorem supplies the global restriction equivalence, the countable tower formula and local smallness for arbitrary small shapes.

lem-coef-functor-spine-tower-mapping-descent vs lem-coef-infinity-mapping-excision: the existing theorem treats one pushout with a monomorphism, whereas the new node treats a countable increasing union and simplex-spine restriction. Step 3 reuses the existing theorem for each finite-dimensional cell pushout.

lem-coef-functor-spine-tower-mapping-descent vs lem-cbc-enhanced-functor-cone-calculus: the existing theorem states that functor objects are quasicategories and characterizes their equivalences, but does not compute their mapping spaces on a countable union or prove local smallness.

The DAG and whole blueprint were searched by accessibility, compact diagrams, compact slices, sections, coCartesian fibrations, cofinality, filtered posets, skeletal and spine terminology and by the HTT places. None of the five statements occurs as a blueprint node; `same_as` is empty. Their ancestry is the item's nearest blueprint ancestor, prop-coef-integral-exceptional-adjoint, proof paragraph 2, through the existing small-saturated-arrow and derived coefficient-adjunction chain. This implements the mapping-complex infrastructure used there, not a different geometric route.

## Review by NV

I read HTT 5.4.4.3 and its cited section lemma 5.4.4.2, then checked the compactness proof in 5.3.4.13 and filtered-poset replacement in 5.3.1.18. For the new compact-slice node I read the compact-core/Ind presentation statements in 5.4.2.2, 5.4.2.4 and 5.3.5.4. For the relative-slice node I checked the arrow-fibration construction and the overcategory colimit statement in 1.2.13.8, against the actual relative slice used by 5.4.4.3. For the mapping-descent node I read the spine and inverse-tower portions of 5.3.4.13 and the preceding mapping-space argument. The cofinality node uses the contractible comma criterion and invariance of colimiting cocones, not ordinary categorical finality.

For Step 1 I opened the existing enhanced-functor calculus and objectwise-colimit theorem. The first says that Fun(K,C) is a quasicategory; the second explicitly permits an arbitrary small simplicial K and any class of colimits that exists in C. Thus kappa-accessibility is sufficient, without assuming presentability. Local smallness is an explicit clause of the new mapping-descent theorem.

For Step 2 I checked the entire existing arrow-square statement: its three mapping spaces have the needed compact source, and the equivalence is natural in the target arrow. The existing spaces-commutation statement permits finite shapes. The spine equivalence and repeated mapping-excision square therefore give the actual filtered-colimit comparison. For Step 3 the same commutation statement permits all fewer-than-kappa products and the countable inverse tower. The existing excision theorem requires only one injective attaching map, satisfied by the coproduct of boundary inclusions. The nondegenerate-decomposition statement gives the unique degeneracy needed for the explicit cellular pushout. The induction is on dimension, with the discrete zero-skeleton as base and lower-dimensional boundaries in the induction step. I corrected the inappropriate one-cell citation described above.

For Step 4 I checked that the compact-small-colimits theorem does not assert existence: lambda-accessibility supplies that existence first, and its kappa-small shape hypothesis is separately imposed. Its local-smallness and kappa-filtered-colimit hypotheses follow from kappa-accessibility. The new relative-slice theorem then gives exactly the created colimits and preservation by postcomposition, not preservation of arbitrary colimits that were never shown to exist. Compact-source density supplies essential smallness and filteredness, not the smaller filtered-colimit hypothesis by itself.

For Step 5 the base K is the original possibly noncategorical simplicial set and has fewer than kappa nondegenerate simplices. The new fibration and section nodes explicitly allow that base; their notion of sections includes noncocartesian edges. The uncountability and mu-to-the-nu bound, the two regular cardinals, fiberwise filteredness, existence of the smaller colimits, and their preservation were all checked before applying the section theorem. No assumption that the large total space is small is inserted.

For Step 6 the relative-slice node provides the full comma category and its essential smallness, so passing to a small representative is legitimate. Each evaluation is cofinal by Step 5; the new reindexing theorem preserves the canonical colimit cocone supplied by the density theorem. The existing objectwise-colimit theorem then identifies its vertex with p in the full functor category. For Step 7 the same new reindexing theorem gives a genuinely small kappa-filtered poset. The relative-slice node states essential smallness of Fun(K,D), the definition gives its fullness, and Steps 2-3 prove its compactness. Step 1 and Step 6 verify all remaining accessibility clauses. Every citation quote was copied from the dependency's statement rather than its proof or its source references.

I tested the empty K case: its functor category is terminal; the all-section category is terminal, the pointwise colimit test is vacuous, and the empty product is covered by the spaces-commutation statement. A nonempty K with empty C has no p, so the presentation assertion is vacuous; accessibility of the empty functor category causes no exception. For relative slices, D empty and K empty gives the unique empty section, while nonempty bases may give no sections without the filtered-fiber hypotheses. The section theorem excludes empty fibers by its filteredness definition. For a point base it reduces to filteredness and identity cofinality of the fiber. For the spine/tower node n=0 and a constant tower give the identity equivalences. Finite skeleta have fewer than kappa cells because they are subsets of K's nondegenerate cells. The countable tower really needs uncountable kappa, which the item assumes. Poset replacement asserts smallness in the smaller universe but never an unwarranted size less than kappa.

All five new nodes introduce their objects and coherent notions explicitly, have empty proof and proof-dependency fields, and contain assertions only. The thirty newly run search records are copied from the command log with the original tools and query text. All services returned results. Ordinary CategoryTheory presentability, Over-colimit and final-functor hits were read as ordinary-category analogues; they do not specialize to arbitrary quasicategories in one line. The StrictSegal hit supplies a different horn property, not mapping descent. Accordingly no node is mislabeled a Mathlib leaf. The proof carries the compactness and generation constructions itself, so it is neither an elementary-node proliferation nor a relabelled conclusion. Off-unit coherent and simplicial tools are declared in split_report.tool_uses because they are generic infrastructure and do not replace this unit's route. No top-level tool_uses field is written.

## Unfinished work

No mathematical clause is left unfinished at this split level. The five general tools are intentionally statement-only, for later splitting. A fresh second reader must review and deliver this preparation; this worker runs only the required no-push dry run.

## Second reading by NV

I independently read the April 9, 2017 HTT PDF at the recorded Harvard URL (saved as sandbox-only `HTT.pdf` and `HTT.txt`). None of these sources is a Stacks theorem, so there are no Stacks tags to invent or verify. The item agrees with the fixed-cardinal argument of Proposition 5.4.4.3, Lemma 5.4.4.2, Proposition 5.3.4.13 and filtered-poset replacement 5.3.1.18; its statement is unchanged. I checked both regular cardinals, the sharp inequality, uncountability, arbitrary simplicial K, local smallness and both accessibility hypotheses. No statement dispute was found.

- Step 1: checked the actual statements of `lem-cbc-enhanced-functor-cone-calculus`, `lem-coef-infinity-yoneda-presheaf-limits`, the accessibility definition and the new mapping-descent node against HTT 5.1.2.2 and 5.3.4.13; PASS, objectwise colimits require only the colimits in question, not presentability.
- Step 2: checked the natural arrow-square, mapping-excision, spaces-commutation and spine statements against HTT 5.3.4.9 and proof (1)–(3) of 5.3.4.13; PASS, all three arrow-square source objects are compact and the finite spine induction includes n=0 and n=1.
- Step 3: checked the nondegenerate-decomposition statement, mapping-excision injectivity hypothesis, fewer-than-kappa products, tower mapping formula and the spaces-commutation statement against HTT 5.3.4.13(4)–(6) and 5.3.4.12; PASS, the degreewise cell argument is explicit and uncountability bounds the countable tower nerve.
- Step 4: checked compact-source density, existing `lem-coef-compact-small-colimits` and the relative-slice colimit clause against HTT 5.4.2.2, Corollary 5.3.4.15 and 1.2.13.8; PASS, lambda-accessibility supplies existence before compact-small-colimits is applied, and postcomposition preserves the source-computed colimits.
- Step 5: checked both new slice/section statements against HTT 2.4.7.11–12, 4.2.2.4 and every hypothesis (i)–(iv) and conclusion (1)–(2) of Lemma 5.4.4.2; PASS, these are all sections over the original simplicial base and no smallness of the total fibration is assumed.
- Step 6: checked the new general cofinality criterion/restriction theorem, canonical density cocone and existing objectwise-colimit statement against HTT 4.1.3.1, 4.1.1.8, 5.1.5.3 and the final paragraph of 5.4.4.3; PASS after replacing the bundled reindexing citation by the narrower missing cofinality tool.
- Step 7: checked the existing `lem-coef-infinity-cofinal-kappa-poset` statement, relative-slice smallness, fullness definition and all accessibility clauses against HTT 5.3.1.18 and 5.4.4.3; REPAIRED, the existing poset replacement is reused and the general cofinality theorem bridges its cocomplete-target formulation to the existing colimit in the possibly noncocomplete functor category.
- New `lem-coef-accessible-compact-slice-density`: checked HTT 5.4.2.2(2)–(3), 5.4.2.4, Corollary 5.3.5.4 and 5.1.5.3; PASS after correcting “Proposition 5.3.5.4” to “Corollary”. It fixes the accessibility cardinal, unlike the existing existential common-cardinal approximation node. Statement-only, self-contained and all notions defined or cited.
- New `lem-coef-infinity-relative-slice-sections`: checked HTT 2.4.7.11, dual 2.4.7.12, 4.2.2.4, 1.2.13.8 and the relative slice in 5.4.4.3; PASS, all-section/arrow pullback construction, essential smallness and source-created colimits are explicit. Existing pointwise transport and constant-source cone nodes do not state this construction. Statement-only and definition dependencies present.
- New `lem-coef-filtered-cocartesian-section-cofinality`: checked the entire statement of HTT Lemma 5.4.4.2 and its comma-category proof; PASS, filteredness alone is not substituted for hypotheses (iii)–(iv), and all sections are allowed. This general arbitrary-base section theorem is not a clause of the item or the existing binary pullback theorem. Statement-only and definition dependencies present.
- New `lem-coef-infinity-cofinal-colimit-restriction`: checked HTT Theorem 4.1.3.1 and Proposition 4.1.1.8; REPAIRED, the duplicate filtered-poset clause was removed and the node renamed to its remaining content. Cocone equivalence, comma contractibility and colimit invariance concern arbitrary quasicategories. Testing cofinality on cocomplete targets suffices: use the presheaf Yoneda diagram; its restricted colimit evaluated at j is the groupoid completion of the coherent comma j/u. This is the missing general criterion, not the stronger smaller-cardinal cofinality hypothesis of the existing pullback node. Statement-only, with explicit definitions and no proof dependencies.
- New `lem-coef-functor-spine-tower-mapping-descent`: checked the spine and tower arguments in HTT 5.3.4.13(2)–(3),(6) and 5.3.4.12; PASS, the inverse limit is of spaces with coherent restriction and is natural in both diagrams, not a limit of components. Existing one-pushout mapping-excision does not give the infinite tower formula. Statement-only and definition dependencies present.

Small cases: K empty gives a terminal functor/section category and vacuous objectwise colimit test; K a point reduces generation to compact-source density. C empty with K nonempty has no p, while K empty still gives the terminal category. For C the nerve of vector spaces over any field, the zero object and its identity fit the slice/density and postcomposition assertions, with no nonzero-object assumption. A point base reduces the section theorem to its fiber, and empty fibers are excluded precisely by filteredness. Empty D and empty K give the unique empty section. Spine dimensions 0 and 1 and constant towers give identity comparisons. Cofinality for empty targets has only the empty domain; a nonempty target with empty domain fails the comma condition. Posets have no claimed size bound below kappa; only smallness and kappa-directedness are asserted.

I searched the shared DAG by the HTT numbers and compact-slice, section, spine, tower, cofinal and poset vocabulary, read the actual candidate statements, and searched the current and archived imported blueprints. This found the coherent poset-replacement duplicate missed by the first reading. I also checked the named Lean project source and upstream reference for an exact completed attachment; none was found. I ran six fresh semantic searches using different phrasing, with actual command outputs appended by msearch.py to searches.jsonl. I read the ordinary candidate signatures in Mathlib Presentable/Dense.lean:28–76, Presentable/Directed.lean:528–532, Limits/Final.lean:90–100, and the StrictSegal and Quasicategory definitions. Hom-set accessibility/finality and strict simplex/path bijections do not specialize to arbitrary quasicategories. No Mathlib leaf was created.

Changes: (1) removed the duplicated poset-replacement clause and renamed its remaining general cofinality node; (2) cited the existing coherent poset theorem in step 7 and explicitly bridged its target hypothesis; (3) corrected the compact-density source label; (4) corrected the delivered item's created.item/group to this item and NV; (5) appended genuine independent search records; (6) regenerated every citation from the repaired dependency statement. Historical first-worker sections, including `## Review by NV`, remain in place. The five remaining new nodes are strictly smaller general tools; no conclusion was moved to a restated item. The off-unit enhanced-functor theorem remains a reported generic tool for maintainer review, and the nondegenerate-decomposition theorem is already a Mathlib leaf. No maintainer-owned route exemption, live file, Lean file or build was written or run.

The server dry run completed successfully: `OK (not pushed) deliver/NV/lem-coef-accessible-diagram-presentations at 04f4ffd8d7: preflight passed`. The tool ran the required server preflight (including the DAG and split review checks); no such project validation tool ran on this machine. A further no-push run was launched after the completed second-reading report, to verify that exact final preparation before delivery.

The further no-push run found three stale full-statement quotations of `def-coef-presentable-infinity-category`: the shared definition had been updated during the server wait to specify the ambient space universe and coherent corepresented functors. I opened the updated definition, checked that its local-smallness, filtered-colimit and accessibility requirements used in steps 1, 4 and 7 are unchanged, and replaced these quotations with the exact, relevant accessibility sentence. No statement or proof step was weakened. The required no-push check is rerun after this citation repair.

The citation-repaired no-push run passed: `OK (not pushed) deliver/NV/lem-coef-accessible-diagram-presentations at b4390bdcb1: preflight passed`. This verifies the final mathematical split and its current quotations; delivery follows with the same nodes and citations.
