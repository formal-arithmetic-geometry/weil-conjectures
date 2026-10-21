# Q144: lem-per-continuous-coefficient-slice-normalization

## 1. Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-continuous-coefficient-slice-normalization.json`: statement, now split in seven steps; statement and statement dependencies retained verbatim. No exact Mathlib match. No new nodes and no new Mathlib leaves.
- `citations.json`: twenty verbatim statement quotations, one for each step/node pair.

The item was initially absent from the sandbox. I copied the current repository node and retained its inherited source, blueprint ancestry and searches. The additional actual searches are recorded from `searches.jsonl`. No Lean, library, repository or launcher file was written and no compiler/build tool was run.

## 2. Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag and for continuous coefficient, slice restriction and normalized inverse-image terminology found no declaration proving every clause. Continuous-coefficient declarations and the Mathlib `Scheme.ellAdicSheaf` construction do not state this theorem.

## 3. WANTED

None. All sources used are available locally.

## 4. Problems found and changes

The imported item had no proof. I retained its statement and made the indexing-category computation explicit: the displayed object is initial in the category defined in `def-weil-proetale-inverse-image`, hence terminal in its opposite, which is the actual colimit index. The resulting map is restriction along the second component of the graph. Its restrictions and its sheafification unit are checked, rather than inferred from an unspecified equivalence.

I kept the distinction between arbitrary site objects and noetherian schemes throughout. In particular no noetherian hypothesis on a site object is needed for continuous functions or slice restriction, and no general preservation of inverse limits by arbitrary inverse image is asserted. Closed immersions are handled by their existing coefficient isomorphisms, not as site objects. The derived clause uses a K-flat resolution and the existing tensor-restriction theorem rather than claiming that ordinary sectionwise tensors already compute arbitrary derived pullbacks.

Two reference issues in read-only dependency nodes were noticed. The source of `def-weil-proetale-inverse-image` calls Stacks 06UM the indexing-category construction, but 06UM is `sites-section-pullback` (pullback maps on global sections); the indexing construction is Tag 00VC, `sites-section-functoriality-PSh`, especially `equation-colim-category`. Step 2 cites the latter, which I read. Also the last sentence of `def-weil-pbc-lisse-lattice-coefficients` writes the comparison for an arrow f:Y→X with reversed domains (`E_Y→f_*E_X`). The proof uses only its correctly stated sections and precomposition restrictions, and explicitly constructs the correctly typed adjunct `T_X→u_*T_U` and `u^{-1}T_X→T_U`. Neither issue requires a change to this item's statement. The dependency nodes were not edited.

The chapter and unit route stay unchanged: the split supplies the normalized continuous realization input under the first paragraph of `lem-per-smooth-pullback-t-exact` (cohomology of pullback). The item is not a unit key node, so no unit record is delivered. Generic ringed-site tools outside this unit are declared, with their reasons, in `split_report.tool_uses`.

## 5. Unfinished work

None in the stage-1 split. Existing cited nodes retain their own independent proof obligations. This delivery does not claim a Lean proof.

## Not duplicates

No new nodes. Whole-DAG title/statement searches and `blueprint_refs.py` searches for continuous coefficient, continuous coefficient slice, localized ringed site, continuous ring, inverse image and restriction found generic tools rather than another blueprint statement of all this item's clauses. I reused the localized-site tensor and K-flat nodes instead of creating special cases. The returned over-site Mathlib constructions were read as possible tools, not treated as a proof of continuous coefficient comparison.

## Review by Q144

I read Bhatt–Scholze Definition 6.8.1 and Lemma 6.8.2 on printed pp. 58–59, the paragraph before Definition 6.8.6 on p. 60, and Remark 6.8.15 on p. 62. These give the continuous coefficient definitions, completion/localization identification, immersion comparison and the ambient module-pullback interpretation. The normalization calculation added here is my explicit argument, so `proof_origin.by` is `agent`. I also read Stacks `sites.tex` at Tag 00VC (`section-functoriality-PSh`, the indexing-category formula and colimit restrictions), Tags 00XZ/00Y0 (localization); `sites-modules.tex` at Tag 04IX (`definition-localize-ringed-site`), Tags 03CZ and 03EL (scalar adjunction and tensor pullback); and `sites-cohomology.tex` at Tags 06YS, 0G7E and 06YY (K-flat resolutions, preservation and derived-pullback computation). There are no new-node sources to check.

For Step 1, I opened `lem-weil-proetale-weakly-etale-localization` and `def-pur-localized-ringed-site`. The former states the actual equivalence of sites including coverings; the latter states the value and module-action formula on the slice. Neither assumes a noetherian source. I did not use merely a definition to supply the equivalence.

For Step 2, I opened `def-weil-proetale-inverse-image` and `def-weil-pbc-sheafification`. The former really indexes by the opposite of its category of graph maps. For any object (W,phi), the unique arrow from i_0 is pr_W phi, so the opposite diagram has the required terminal object. I wrote both directions of the colimit comparison and the restriction equality F(ab)=F(b)F(a). The latter node states the universal property needed to extend this comparison across the unit. This is an elementary calculation, not a new lemma or a quotation of an unstated cofinality theorem.

For Step 3, I checked that `lem-weil-pbc-continuous-ring-functions-sheaf` applies to every scheme and topological commutative ring. I used `def-weil-pbc-lisse-lattice-coefficients` only for its section and restriction definitions. Clause (2) of `lem-weil-proetale-weakly-etale-localization` states the constant-section-normalized finite constant-sheaf comparison. The explicit formula z composed with a checks the structural adjoint, coefficient inclusion, quotient projections and transitions. It does not claim that every section lifts through a finite quotient. Thus no projectivity or surjectivity assumption has slipped in.

For Step 4, I opened `lem-weil-pbc-continuous-coefficients-immersion-restriction`: it states the completed integral and rational coefficient identifications for noetherian X, which is exactly the hypothesis in force. Its application here is on X, not on arbitrary U. The slice is sectionwise, so its limit cone and projections restrict identically. I opened `lem-weil-pbc-localization-inverse-image-coherence` and checked that its comparison sends fraction representatives to the stated fractions and commutes with specified ring identifications. This supplies the rational identification rather than an assumed commutation of a general inverse image with completion.

For Step 5, that same coherence node explicitly states exact module inverse image over the inverse-image ring and termwise unbounded derived functors. I checked that the coefficient isomorphism from Step 3 fits its ring-identification clause. I wrote out the balanced tensor map and its inverse along a ring isomorphism; this is the elementary reason the additional scalar extension disappears.

For Step 6, the five cited morphism definitions state flatness and unramifiedness for etale maps, the open diagonal for unramified maps, the local-ring identification for open immersions, and the flat-diagonal criterion for weak etaleness. Their short implication is written out. `lem-weil-pbc-continuous-coefficients-immersion-restriction` explicitly states both immersion coefficient isomorphisms, induced by continuous-function pullback and compatible with inclusion and composition. The etale case uses both noetherian hypotheses only to identify the completed coefficients on the two bases; the immersion case uses the actual immersion comparison. Constants and quotient maps commute by the postcomposition equation from Step 3.

For Step 7, I opened all four cited statements. `lem-pc-kflat-resolution` gives flat terms as well as K-flatness and a quasi-isomorphism. `lem-weil-pbc-ringed-topos-kflat-pullback` works for arbitrary small ringed topoi and arbitrary structural coefficient maps; I use it with the identity map on the pulled-back ring, first for f inverse image and then for the slice. `lem-weil-pbc-ringed-topoi-derived-pullback` computes on those representatives and makes comparisons independent of resolution. `lem-sfb-localized-site-tensor-restriction` states the natural isomorphism with the identical pure tensor under the two sheafification units and imposes no flatness or finiteness hypothesis. Applying it to E_Y and each term of HP gives the displayed restriction formula with the correct ring R restricted to U. Exactness preserves the quasi-isomorphism, and the comparison commutes with differentials by naturality. This checks the derived claim without silently substituting a constant rational sheaf for the continuous coefficient ring.

I checked delivery-errors B–E against the node and these sources: no new unsplit statements or disguised clauses are introduced; every proof citation has a corresponding verbatim quotation; statement dependencies and inherited blueprint metadata are preserved; proof dependencies are exactly the union of uses; all generic off-unit tools are declared; no SGA source is cited. All seven steps are below 2000 characters, the longest 1528. The initial-object and balancing arguments are explicit, and the only substantive generic homological inputs are cited existing statements.

For edge cases I tested empty U and empty V (the graph object and its unique arrows still exist; ring-valued functions on the empty space have their usual terminal-ring value), the identity U=X, disconnected objects (constants stay constant componentwise), arbitrary nonnoetherian weakly etale U, every n≥1 and successive quotient transition, an arbitrary uniformizer constant, and unbounded complexes (the cited K-flat and exactness results have no bound). None changes the statement. The derived coefficient tensor is trivial only after a structural ring isomorphism has actually been established; it is not asserted for general f.

Mathlib checks used the required msearch command with leanfinder, leansearch, loogle and grep, with different natural-language phrasings. I read the returned `CategoryTheory.Sheaf.over` and over-map constructions in `Mathlib/CategoryTheory/Sites/Over.lean` and `AlgebraicGeometry.Scheme.ellAdicSheaf` at `Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean:59–68`. They construct relevant individual notions, but do not assert the completed integral/rational coefficient, finite-quotient and derived module normalization clauses. Successful search responses were recorded as no match; no unavailable service was represented as a negative search.
