# Q67: lem-trf-space-chart-limit-enlarged-sections

## Files written

- dag/nodes/sec-trace-formula/lem-trf-space-chart-limit-enlarged-sections.json: statement split into nine proof steps; no Mathlib match for the complete item.
- citations.json: 33 statement quotations, one for each direct proof citation.
- report.md: this report. searches.jsonl retains the previous attempt's searches and the additional queries actually run here. write_split.py is a sandbox-only preparation script.

New nodes: 0. Mathlib leaves: 0. All dependencies already exist. The item statement and statement dependencies are unchanged.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag, enlarged etale language, AlgebraicSpace, and chart-limit language. There is no declaration giving this item's algebraic-space limit, scalar normalization and localization clauses. Generic scheme and category-theoretic results do not attach this item. No Lean was written or compiled.

## WANTED

None. All sources used were available in literature/stacks-project and literature/blueprint/latest.

## What needed repair

The item was statement-only, with no proof. The sandbox contained only search logs, which I read and reused rather than repeating their queries. I supplied the universal property for an arbitrary cone explicitly: use its atlas component to factor through the equalizer, then test the factorization at an arbitrary chart after pulling the atlas back to that chart. This avoids assuming a product over all charts lies in the smaller module universe. I also supplied the equations for naturality, the exact module action of the transported direct image, and the coordinate maps identifying the enlarged localized functors.

No statement dispute is needed. The complete imported statement is retained. There is a source-proof typo, described below; correcting the base of that fibre product leaves the theorem and route unchanged. The chapter and unit records were read; their latest blueprint versions were also read. This is infrastructure below the recorded specialization and polarized-descent chain, not a replacement for the chapter's Lefschetz–Verdier or the unit's contracting-correspondence route.

## Source error

In literature/stacks-project/spaces-morphisms.tex, Tag 03M8, lemma-compute-pushforward, the proof prints

$(V\times_Y U)\times_X(V\times_Y U)=V\times_Y R$.

Its overlap must instead be taken over $V\times_Y X$. To see the printed formula fail, take $X=Y=U=\operatorname{Spec}k$ and take $V$ to be the disjoint union of two copies of $\operatorname{Spec}k$. The printed left side has four points, while $R=\operatorname{Spec}k$ and the right side has two. The corrected overlap has two points. My proof consistently uses $T_0\times_WT_0$ and $T\times_WT_0$, where $W=X\times_YV$, as already required by Tag 03H7 and the item's statement. This reports an error in the source's proof, not a false theorem or a change to the item.

## Searches and reuse

I read the four existing 2026-10-23 log entries: grep AlgebraicSpace/enlarged etale/chart limit (no hits); LeanSearch for direct image as fibre-product evaluation and all-chart limits (eight generic evaluation/preservation results); Loogle for SheafOfModules and limit (twelve generic colimit results); LeanFinder for module-sheaf sections on algebraic spaces as chart limits (eight scheme/global-section results). These were retained along with the item's inherited 2026-10-22 searches.

I ran a second semantic phrasing about a small limit from an atlas equalizer. LeanFinder returned generic gluing pullback cones, PresheafOfModules.isSheaf_of_isLimit and CategoryTheory.Sheaf.isLimitConeΓ. The source of the latter, Mathlib/CategoryTheory/Sites/GlobalSections.lean, lines 90–160, was read: it constructs an abstract global-sections cone under HasGlobalSectionsFunctor. It does not identify our chart category with the enlarged slice, identify its global sections with the atlas equalizer, or prove the ringed localization normalization. Thus it is not an exact or one-line specialization for the complete item. The logged grep for isLimitConeΓ, sectionsFunctor and evaluationPreservesLimit identified this file and generic functor-category results. No new generic lemma was created: the explicit equalizer argument is the substance of this split.

DAG searches covered the source tags 03G1, 03H7, 03G8, 03M8, 03LX and 041F, and equalizer/atlas/chart keywords across all chapters. Blueprint reference searches for chart limit, compatible sections, enlarged, 03M8 and 03H7 found no equivalent imported node for this item. I read the existing atlas-extension, enlarged-ringed-morphism, permanence, tuple-sheaf, atlas direct-image diagram, atlas equalizer and cover-kernel statements. The last two direct-image comparison statements are not used to establish this item: that would either assume its content or create a cycle. The lower enlarged-site model, chart-ringed morphism and permanence statements suffice.

## Not duplicates

No new nodes were created. The pre-existing enlarged-site model gives atlas descent but does not state the arbitrary-cone universal property over the full scheme-chart category or its preservation under the specified cartesian localization; those are proved here.

## Review by Q67

I read the sources for the item in spaces-properties.tex: Tag 03G1 (lemma-compare-etale-sites), Tag 03H7 (remark-explain-equivalence), Tag 03G8 (lemma-morphism-ringed-topoi), the enlarged-site localization square in lemma-pushforward-etale-base-change, and Tag 03LX (lemma-pushforward-etale-base-change-modules). I also read spaces-morphisms.tex Tag 03M8 and spaces-topologies.tex Tag 041F, including all three covering assertions. For permanence I read the adjacent composition, base-change and permanence statements (03FT, 03FU, 03FV). I checked the current blueprint ancestor proof, unit and chapter in literature/blueprint/latest. There are no new-node sources to audit.

For Step 1 I opened the statements of fibre-products-etale-covers, chartwise-etale-permanence, algebraic-space and etale-module-functors. The first gives the universal product and scheme overlaps, permanence explicitly gives base change, composition and the etaleness of an arrow between objects etale over a common base, the definition provides an atlas, and the chart definition gives exactly the triangles and arrows. This verifies both directions of the category identification; no representability of f is inferred or required.

For Step 2 I checked the enlarged-model statement, enlarged-chart-ringed-morphism statement, module-sheaf definition and chart-functor definition. The chart-ringed statement explicitly supplies both precomposition and the ring map whose restriction is pullback of regular functions on every scheme chart. The module definition supplies restriction semilinearity. Therefore the cone maps are linear for the same R-action, not for an unspecified isomorphic coefficient ring.

For Step 3 the enlarged-model statement gives the precise equalizer with naturality and extends module structures. The module and size definitions justify taking its inherited operations and its small carrier. For Step 4 the same equalizer gives the unique factorization of the atlas component; addition and scalar preservation are checked after its injective atlas projection. This is an elementary use of a cited equalizer, not an uncited general large-limit existence theorem.

For Step 5 I checked the fibre-product and permanence statements supply the scheme P and the surjective etale covering P to T. The enlarged-model equalizer applies at the scheme object T with that cover; thus F(T) to F(P) is injective. The two displayed restrictions agree by the cone equations. These facts prove the factorization through every chart and uniqueness, which is the part not supplied merely by naming the atlas equalizer. Each arbitrary chart is handled individually; there is no large product or quantification over a small skeleton substituted without explanation.

For Step 6 the model's stated naturality in F and the module definition give compatibility with module morphisms. The two maps for V1 to V2 have identical composites into each chart by presheaf functoriality. I wrote that equation and its scalar homomorphism explicitly. The structural-map normalization verifies the semilinearity in V; this does not require the map of test schemes to be surjective.

For Step 7 I checked the chart-ringed-morphism statement says its underlying direct image is precomposition by X times_Y V. The ringed-topos-morphism definition expressly gives module direct image with underlying sheaf f_* and action through the structural map. The enlarged-model equivalence transports it back to the small sites. The two inverse comparison maps then follow from the universal properties already proved, with their projections equal; the chart-functor definition specifies exactly these projections and their naturality. I did not cite a fully faithful functor as though it gave an evaluation/Yoneda formula.

For Step 8 I checked permanence applies to g without surjectivity, and the enlarged-model statement explicitly identifies both localized sites, including rings. The definition of localization specifies the slice objects. The two coordinate maps are inverse on every enlarged-site object, not just scheme objects, by the fibre-product universal property. For Step 9 I checked the same maps leave the underlying chart scheme, arrow and map a to V unchanged. Hence the coefficient map is literally the same a-sharp, and contravariant restriction gives the same cone projection. The chart-ringed statement normalizes ring maps on those charts, so this also checks the coefficient comparison, not merely the underlying sets.

I tested the limit argument with f an identity and with W a scheme: the identity chart is then terminal in the non-opposite chart category and the limit reduces to F(W). For W empty the sheaf equalizer yields the zero module, with no nonempty atlas assumption. For a disconnected W and a disconnected atlas, the P-to-T test retains all overlap conditions; it never assumes connectedness. I also tested g an open immersion that misses part of Y and g the empty etale map: the formulas remain valid since no surjectivity of g is used. No quasi-compactness, separation, finiteness, or quasi-coherence hypothesis was added. The small-vertex claim uses an equalizer of two small section modules rather than completeness for a large indexing category.

Against delivery-errors B–E: no statement-only new nodes, duplicate clauses or new Mathlib leaves were introduced; the item's TeX is unchanged; all 33 quotes in citations.json were checked as literal substrings of the currently cited statements. All non-elementary geometric and sheaf-descent inputs are named existing nodes. No use is made of the proof text of a cited node in place of its statement. The elementary steps are only explicit equalizer factorization or functoriality arguments from those inputs. All nine steps are below 2000 characters (maximum 949), so no long step hides an omitted lemma. The source typo and its counterexample are reported rather than copied. The item has no dependency back through its parent pushforward-restriction node.

## Unfinished work

None in the requested split. Independent review and any eventual Lean implementation remain the maintainer's stages. Delivery checks are recorded below after running the required server tools.

## Delivery checks

The required deliver.py --no-push completed successfully on 2026-10-23: `OK (not pushed)` at dry-run commit 6cbc71dacc9, with server preflight passed. No compiler, Lake command or local DAG/preflight check was run. The final push invocation reruns the required delivery checks for this report and item.
