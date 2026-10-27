# Stage-1 report: lem-sfb-normal-base-fibrewise-line-locality

1. Files written:
   - `dag/nodes/sec-six-functors-basics/lem-sfb-normal-base-fibrewise-line-locality.json`: item, split; statement unchanged; no Mathlib match.
   - `dag/nodes/sec-six-functors-basics/lem-sfb-normal-domain-smooth-family-models.json`: statement, unsplit; no Mathlib match. Normal arithmetic models of the family, without a section or a line module.
   - `dag/nodes/sec-six-functors-basics/lem-sfb-normal-noetherian-generic-line-pullback.json`: statement, unsplit; no Mathlib match. Precisely Stacks 0BD7, not an arbitrary-normal-base extrapolation.
   - `report.md`, `citations.json`; search queries, actual answers and the append-only search log remain in the sandbox. No Lean was written; no compiler, Lake, build, local DAG checker or git command was run.

2. Attachments: none. I searched `lean/WeilConjectures/` for the exact blueprint tag, the notion, generic triviality, normal family models and related Picard terms. The affine algebra normal-model declarations do not state this assertion about arbitrary scheme families and line modules. The pre-existing item searches are retained, and new searches and actual answers are added.

3. WANTED: none. Every source used here is present locally. No SGA source is used.

4. What needed correction: the unsplit item correctly warns that Stacks 0BD7 alone does not imply its non-Noetherian statement. I preserved that warning and the statement. The repair is an explicit local-ring/normal-model reduction; it does not silently impose a Noetherian base, choose a section, use properness, or assert simultaneous finite-stage descent of all fibre trivializations. An arbitrary normal scheme need not have integral affine open neighbourhoods, so a reduction by a covering of integral affines would be invalid. I instead use Spec of each local ring, then spread its trivialization. The latest blueprint direct-image proof has no line-bundle lemma of this form; this remains the inherited below-unit prerequisite of the alteration/Picard route, not a replacement of any unit step.

5. Unfinished work: the two new prerequisites are deliberately statement-only and unsplit, for the next DAG layer. No argument is hidden as a proof sketch in their statements. The item's proof is complete conditional on these explicit nodes and the existing cited statements.

## Sources and searches

I read `literature/stacks-project/divisors.tex`, Tag 0BD7 (`lemma-in-image-pullback`), statement and entire proof, including the local factorization, the meromorphic coefficient module and the saturated bad locus. Its hypotheses are local Noetherianity of both schemes, a normal integral base, flat nonempty integral fibres, quasi-compactness or local finite type, and generic triviality. The new generic-line node reproduces these hypotheses, without adding smoothness or regularity. Its proof is not supplied, as required for a new node.

For the normal-model node I read `pione.tex`, Tag 0EZJ (`lemma-extend-covering-general`), normal approximation and smooth-family descent paragraphs; `algebra.tex`, Tag 033C (`lemma-normal-goes-up`), the normal finite-type subring construction; `limits.tex`, Tags 01ZM (`lemma-descend-finite-presentation`), 01ZQ (`lemma-descend-separated-finite-presentation`), 0C0C (`lemma-descend-smooth`), and 05F4 (`lemma-limit-contained-in-constructible`); and `more-morphisms.tex`, Tag 055I (`lemma-nr-geom-connected-components-constructible`). The node is explicitly agent-formulated: 0EZJ has a section and trims to its component, which cannot be used for an unpointed family. Instead, after descending the family and its smoothness/separation to a normal finite-type subring, take the constructible locus where the number of geometric connected components is exactly one. All points of Spec R land in it. Tag 05F4 makes the image of a later normal subring stage lie in this locus. The number-one condition excludes empty fibres. Pullback to the directed tail preserves the condition. The normal subrings cover R because every finitely generated subring is contained in its normalization inside its fraction field, which lies in R and is finite over a finite-type integer ring. Finite presentation and smoothness provide the finite-stage family; finite type over Noetherian stages gives Noetherian sources. This supplies family models only, not a line-pullback theorem or its desired conclusion.

I read the module limit statements in `limits.tex`, Tags 0B8W (`lemma-descend-invertible-modules` (2)) and 01ZR (`lemma-descend-modules-finite-presentation` (2),(3)). The full already-existing nodes for these facts are reused. I read the entire statements of every citation appearing in `citations.json`; that file records verbatim statement text, not proof text or a definition used in place of a theorem.

Searches were made only through the required `msearch.py` command. Each item/new node has LeanFinder, Loogle, grep and LeanSearch queries, and a second semantic phrasing. The first Loogle queries involving `AlgebraicGeometry.IsSmooth` returned an unknown-identifier diagnostic, so I did not use them as evidence of absence; a further `AlgebraicGeometry.Scheme, "invertible"` query completed with zero hits. Both semantic services ran successfully. I read all returned types and the relevant Mathlib source: `RingTheory/PicardGroup.lean` (relative Picard kernel/exact sequence and lines 883 onward), `RingTheory/Smooth/NoetherianDescent.lean` (the smooth algebra subring model at 255 and 268), and `AlgebraicGeometry/Geometrically/Connected.lean` and `Integral.lean`. The ring Picard exact sequence is not descent of an arbitrary line on a scheme family. Smooth affine algebra descent does not provide a normal scheme-family system with geometric connectedness. These are not one-line specializations of the new nodes. A supplementary grep of `AlgebraicGeometry` confirmed the existing geometric-fibre classes, without an approximation theorem. Search outputs and exact queries are retained separately; no unavailable service is recorded as no match.

Before naming either node I searched the whole DAG by tags 0BD7, 0EZJ, normal approximation, smooth models and generic invertible sheaves; I also used `tools/blueprint_refs.py search` for 0BD7, 0B8W, 0C0C, 055I, normal approximation, integral fibres and generic invertible wording, and read the latest unit/direct-image blueprint. No blueprint statement duplicates either new lemma. The normal pointed-family nodes require a section, which the item does not have. The regular finite-type-over-a-field generic-line node has stronger base hypotheses; it cannot be applied to the normal arithmetic models here. Blueprint `from.node` is null along the existing inherited created-item chain; the prescribed ancestor command also returned None. The exact inherited place/via route is preserved and extended, with `same_as: []` for both new nodes.

## Review by Q01

I checked delivery-errors B to E against the files and sources, with special attention to the scope of each citation and to facts that need their own node. I did not treat the isolated appearance of a Stacks tag as a proof. The two new nodes have self-contained statements, definitions or inline meanings, empty proofs and proof dependencies, actual searches, and a precise blueprint place. They are different from each other: one constructs a family system without mentioning any invertible module; the other is a Noetherian generic-line pullback theorem for flat families, without smoothness or an approximation system. Neither restates a clause of the original arbitrary-normal-base locality assertion.

Step 1 uses the smooth-base-change clause of `lem-pc-proper-base-change`, the separated-base-change theorem, and all needed parts of `lem-weil-pbc-qcqs-morphism-permanence`. None is cited for more than its statement. The fibre and line identifications use the universal property and functorial tensor pullback, with local rank-one generators written out. The map on residue fields is in `def-weil-residue-field`. All field-valued fibres are nonempty and geometrically connected because the corresponding original residue-field fibre remains so after every extension.

Step 2 uses the new normal-domain models, then exactly the invertible-object descent clause of `lem-trf-invertible-affine-limit-descent`. Its small directed index, affine transitions and qcqs stages are supplied by the model node, not assumed without justification. Invertibility on later stages follows immediately in pulled-back local frames. In review I made the Noetherianity of the total model stages explicit in the model node; the later application of 0BD7 then needs no uncited local-finite-type comparison.

Step 3 checks every hypothesis of `lem-sbc-cartesian-family-generic-limit`: integral qcqs bases, dominant projections, affine transitions, cartesian family squares and qcqs family maps. The family models supply these data without a section. The generic-line isomorphism descent node applies on the resulting qcqs generic fibres, with fixed finitely presented module models. I checked that it descends the given isomorphism AND its inverse/equations, not merely a morphism. The elementary residue-field factorization is written out using the prime kernel on an affine chart. It applies even when the image of the generic point of Spec R is not a global generic point of S. Only the one needed generic trivialization is descended; the proof does not need infinitely many fibre conditions at a finite stage.

Step 4 uses `lem-pc-smooth-flat` for flatness, `lem-trf-smooth-connected-fibre-normal-integrality` for the actual integral nonempty fibres, and the new exact 0BD7 statement for the pullback conclusion. I checked both local Noetherian hypotheses, normality AND integrality of the base, quasi-compactness of the map, invertibility of L_j and generic triviality. No regularity assumption replaces normality and no group scheme property is used.

Step 5 is genuinely elementary: tensor pullback preserves the displayed rank-one bases, and an open neighbourhood of the closed point in Spec of a local ring contains a basic open D(a) with a a unit, hence is the whole spectrum. Therefore the pulled-back base line is free. This is an argument from the definition of an invertible line, not an uncited projective-module theorem.

Step 6 uses the full statement of `lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods` for the limit, directedness and affine transitions. `lem-weil-pbc-scheme-over-limit` supplies the limit for the base-changed family and its affine transitions. The qcqs permanence theorem applies to the finitely presented family over affine opens. The existing module isomorphism-descent theorem therefore spreads the actual trivialization and inverse from the local ring to one neighbourhood. This avoids the incorrect integral-affine-cover reduction. Step 7 uses the explicit tensor unit formula and the cover by the chosen neighbourhoods; it imposes no gluing or uniqueness condition.

Small cases: S empty gives the empty cover. For S a field, the hypothesis is already the desired triviality. For p the identity, an arbitrary base line is locally trivial, consistent with the result. R can be non-Noetherian and of positive characteristic; no excellence or characteristic-zero hypothesis is used. At a non-generic point s, its local-ring generic point need only map to a point of S, and residue-field factorization handles this. Nonproper fibres cause no problem because isomorphism descent uses qcqs finite-presentation data, not proper cohomology-and-base-change. A disconnected arbitrary normal base is treated one stalk at a time. The model lemma excludes empty fibres by connected-component count equal to one; 0BD7 also explicitly excludes them. Testing reducible flat fibres shows why the integral-fibre hypothesis of 0BD7 cannot be dropped. No Noetherian statement is applied directly to the original base.

All non-elementary proof steps are shorter than 2000 characters; none hides a separate long argument. Proof dependencies are precisely the union of step citations. Generic off-unit tools are declared in `split_report.tool_uses`; no maintainer-owned `tool_uses` or review fields were written. I also checked for cycles through the required server checks. No statement dispute was found, and the item's statement was not changed.

## Not duplicates

- lem-sfb-normal-domain-smooth-family-models vs lem-weil-pbc-affine-etale-covering-eventually: descends an etale covering family on supplied systems, not normal arithmetic models of a smooth family.

- lem-sfb-normal-domain-smooth-family-models vs lem-weil-pbc-descend-finite-locally-free: descends finite local freeness for a supplied morphism, not smooth unpointed connected-family models.

- lem-sfb-normal-domain-smooth-family-models vs lem-weil-pbc-descend-surjective: descends surjectivity of a supplied finite-presentation morphism, not a normal-base family approximation.

- lem-sfb-normal-domain-smooth-family-models vs lem-weil-pbc-limit-contained-in-constructible: a constructible-image containment tool on a supplied system, not construction of a smooth family model system.

- lem-sfb-normal-domain-smooth-family-models vs lem-sbc-cartesian-family-generic-limit: starts with an existing cartesian system and constructs generic-fibre limits; it does not construct smooth connected normal Noetherian family models.

- lem-sfb-normal-domain-smooth-family-models vs lem-sbc-dominant-finite-refinement-limit: proves that an already supplied finite-refinement cone is limiting; does not construct a smooth family model.

- lem-sfb-normal-domain-smooth-family-models vs lem-sbc-dominant-function-field-limit: constructs only the function-field limit from a supplied base system, not a descended family system.

- lem-sfb-normal-domain-smooth-family-models vs lem-sbc-galois-cover-base-change: base-changes a finite etale torsor; it does not approximate the smooth family and its normal base.

- lem-sfb-normal-domain-smooth-family-models vs lem-sbc-galois-cover-stage-descent: descends a finite etale torsor on a supplied system; no family model system is constructed.

- lem-sfb-normal-domain-smooth-family-models vs lem-sbc-noetherian-spreading-data: requires a section and pointed generic torsor and produces their model; the new result has neither a section nor a torsor.

- lem-sfb-normal-domain-smooth-family-models vs lem-sbc-normal-family-generic-limit: requires a chosen section and a pointed generic-fibre system; the new lemma concerns unpointed families and supplies arithmetic family models, not pointed generic data.

- lem-sfb-normal-domain-smooth-family-models vs lem-sbc-normal-finite-stage-diagram: constructs normalized base stages without a limit or family; the new statement includes the unpointed connected-family system.

- lem-sfb-normal-domain-smooth-family-models vs lem-sbc-normal-finite-stage-universal: constructs one normalized base stage with a universal property; no smooth unpointed family or directed family models are asserted.

- lem-sfb-normal-domain-smooth-family-models vs lem-sbc-normal-noetherian-refinement: constructs a normal base system only; it does not descend an unpointed family with geometric connectedness.

- lem-sfb-normal-domain-smooth-family-models vs lem-sbc-normal-pointed-family-approximation: requires a section and invertible n; those hypotheses are absent here, so its family approximation is not available for an unpointed family.

- lem-sfb-normal-domain-smooth-family-models vs lem-sbc-pointed-galois-cover-limit-descent: descends a pointed torsor on supplied diagrams; the new node constructs family models without any torsor or point.

- lem-sfb-normal-domain-smooth-family-models vs lem-sbc-pointed-section-stage-descent: descends a given section/map on a supplied system, not an unpointed connected-family approximation.

- lem-sfb-normal-domain-smooth-family-models vs lem-sbc-pointed-smooth-family-stage: has a section as a hypothesis and descends it; the new model lemma must work with no section.

- lem-sfb-normal-domain-smooth-family-models vs lem-sbc-underlying-finite-etale-extension: extends the underlying cover of a pointed generic torsor; no unpointed family-model construction is stated.

- lem-sfb-normal-domain-smooth-family-models vs sbc-thm-spreading-finite-etale-galois: extends a generic Galois cover using a section and rational point; the new result is an unpointed family-model construction.

- lem-sfb-normal-domain-smooth-family-models vs sk-prop-input-spreading: extends a generic finite etale torsor on a pointed family, whereas the new lemma constructs an unpointed arithmetic family system.

- lem-sfb-normal-domain-smooth-family-models vs lem-trf-geometrically-reduced-fibres-limit-descent: descends reducedness for a supplied family system, allowing empty fibres; the new node constructs normal arithmetic models with nonempty connected fibres.

- lem-sfb-normal-noetherian-generic-line-pullback vs def-sfb-integral-cartier-divisor: defines Cartier divisors and their partial pullbacks; it is not the line-module pullback theorem.

- lem-sfb-normal-noetherian-generic-line-pullback vs lem-sfb-local-generic-unit-factorization: a local algebra factorization of a unit after generic localization; it neither constructs nor descends an invertible sheaf on a scheme family.

- lem-sfb-normal-noetherian-generic-line-pullback vs lem-sfb-normal-base-fibrewise-line-locality: the new 0BD7 lemma assumes both schemes locally Noetherian but needs only generic triviality and flat integral fibres, with no smoothness; the item has arbitrary normal base and local conclusion, reached through approximation and neighbourhood descent.

- lem-sfb-normal-noetherian-generic-line-pullback vs lem-sfb-smooth-generic-trivial-line-descent: the existing lemma requires regular integral separated finite-type schemes over a field; 0BD7 covers merely normal locally Noetherian bases, flat integral-fibre maps and arbitrary locally Noetherian sources. The regular-over-a-field specialization cannot handle the normal arithmetic models.

- lem-sfb-normal-noetherian-generic-line-pullback vs lem-sfb-normal-group-vertical-cartier-descent: the existing assertion is equality of Cartier divisors on a smooth commutative group scheme with a section; 0BD7 concerns arbitrary flat integral-fibre scheme morphisms and line modules, without a section or group law.

- lem-sfb-normal-domain-smooth-family-models vs lem-weil-pbc-smooth-normal-domain-approximation: the existing assertion models one smooth algebra as a ring colimit; it supplies neither a non-affine scheme-family model nor nonempty geometrically connected fibres.
