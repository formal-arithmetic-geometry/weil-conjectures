# Worker report: lem-sfb-smooth-trait-local-rational-spreading

1. Files written: dag/nodes/sec-six-functors-basics/lem-sfb-smooth-trait-local-rational-spreading.json (statement, split); citations.json (verbatim statement quotes for every proof citation); report.md. No new nodes and no new Mathlib leaves. The 15 steps reuse existing nodes throughout. The statement, source record, historical searches and blueprint ancestry are retained.
2. Attachments: none. Searched the current lean/WeilConjectures tree by the exact id, the blueprint tag, rational/birational maps, trait localization and spreading. No project declaration gives this entire statement. Mathlib's RationalMap and spread_out_of_isGermInjective' supply ordinary rational-map or pointwise spreading interfaces, not the relative trait statement with all its clauses.
3. WANTED: Bosch–Lütkebohmert–Raynaud, Néron Models (1990), §§2.5, 4.3 Proposition 5, 4.4 Corollary 4, printed pp.55–59,108,111, for this item. The literature PDF named in the node is absent in the read clone. I read the primary scan at https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf through its PDF text (PDF pp.61–65,114,117). The written proof is marked agent-origin and its operative inputs are the local Stacks sources; no source was downloaded or added to the repository.
4. Errors corrected: there was no existing proof, only a statement. The imported reference to BLR 2.5 Proposition 5 alone does not give the desired proof: that proposition already assumes a relative rational map, whereas producing such a map is the main issue here. I use the direct argument explicitly suggested in BLR 4.3 Proposition 5. In particular I descend the local map, then separately descend its equality with the prescribed generic morphism. For the isomorphism assertion I descend both maps and their inverse equations, and choose base neighborhoods with no special-fibre overlap; I do not assume the source V separated. No statement error or change of hypotheses was found.
5. Unfinished: none at stage 1. Existing unsplit dependencies retain their own work; no proofs of those nodes were edited. No Lean was written and no compiler, Lake or build tool was run.

## Sources and searches

Read the role and stage-1 contract, all of delivery-errors B–E (including its repeated copy), SETUP's three blueprint levels, GOAL.md, the stored chapter/unit records and the latest blueprint unit. This auxiliary has no imported blueprint ancestor: blueprint_refs.py ancestor prints None. Its ancestry remains the existing chain to the Néron criterion, within the recorded ctf stability route; the six-functor statement is not replaced. blueprint_refs searches for rational map, morphism.*limit and dense.*field found no equivalent blueprint statement (the proper-target elimination result has different hypotheses and conclusion). DAG searches by tags, titles and statements found the existing tools used below. No node is created, so there are no new-versus-existing tag pairs to distinguish.

The item-level semantic searches, Loogle query and Mathlib grep were actually run through msearch.py, with queries recorded in searches.jsonl and appended to the item's preserved search records. Both semantic services and Loogle answered. A second semantic phrasing asked specifically about the isomorphism and fibrewise-dense-open conclusion. I read Mathlib/AlgebraicGeometry/SpreadingOut.lean, lines 315–395: spread_out_of_isGermInjective' extends a morphism from Spec of one source stalk, with a locally finite type target. It does not state the item's fibrewise-dense trait extension, birational extension or base-change clauses; the item is not a Mathlib leaf. Ordinary RationalMap uses topological dense opens, rather than fibrewise dense opens.

The Stacks sources read include limits.tex lemma-descend-opens (01Z4), lemma-descend-finite-presentation (01ZM), proposition-characterize-locally-finite-presentation (01ZC), and the neighborhood-limit argument in lemma-morphism-glueing-near-closed-point (0GWT); algebra.tex lemma-characterize-dvr (00PD), lemma-minimal-prime-reduced-ring (00EU) and Noetherian localization permanence (00FN); morphisms.tex smooth composition/flatness/reduced-fibre inputs, finite-type Noetherianity and lemma-scheme-over-field-universally-open (0383); divisors.tex effective-Cartier-complement density (07ZU); and the source statements of every cited DAG node. The source tags and labels used by the proof are attached to the individual steps. No prohibited SGA source is used.

## Not duplicates

No new nodes. In particular the affine-neighborhood limit, qc-open descent, arrow descent, eventual equality, principal-prime DVR criterion, flat torsion-freeness, scheme-map gluing, and field-universal-openness results are existing nodes, reused with their stated hypotheses.

## Review by NJ

I checked the BLR passages against the actual statement rather than treating its reference as a black box. BLR 4.3 Proposition 5, printed p.108, explicitly passes from local extensions at generic points of the special fibre to the rational/birational map; BLR 4.4 Corollary 4 makes the same local-ring test for a smooth test scheme. The proof here supplies the finite-presentation descent and compatibility that those passages compress. There are no new nodes whose sources remain to check. The following is my check of each step and its cited statements.

Step 1: Uses the DVR element-factorization statement and precisely the principal-localization/open-base-change statements. The displayed denominator identity proves E=R[1/pi]; the nonzero uniformizer is part of the DVR hypothesis.

Cited statements read: lem-weil-pbc-dvr-unit-times-uniformizer-power, lem-weil-pbc-principal-localization-open-immersion, lem-weil-pbc-open-immersion-base-change.

Step 2: Finite-type composition/base change and preservation of Noetherianity apply to Z, V and W. The open-Noetherian statement ensures domains are quasi-compact; the locally-Noetherian quasi-separatedness and qcqs-morphism statements ensure the required relative quasi-separatedness. Smooth restriction supplies local finite presentation on the chosen opens. Stalk localization and Noetherian localization apply to A_xi. No intersection of affine opens is claimed affine.

Cited statements read: def-sc-discrete-valuation-ring, lem-sfb-finite-type-composition-base-change, lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-noetherian-open-subscheme-noetherian, lem-weil-pbc-locally-noetherian-quasi-separated, def-sbc-smooth-morphisms, lem-weil-pbc-qcqs-morphism-permanence, lem-weil-pbc-affine-open-stalk-localization, lem-weil-pbc-localization-noetherian, lem-weil-pbc-noetherian-finitely-many-components, lem-weil-pbc-smooth-restrict-open-subschemes.

Step 3: The smooth criterion supplies flatness at xi. The flat definition is stalkwise, so the torsion-free-domain lemma applies directly to the R-module A_xi. The reduced-fibre statement and minimal-prime localization-field statement identify the reduced fibre stalk as a field, and the fibre-stalk-quotient node identifies it with A_xi/pi. The principal-prime criterion is applied with H=B=A_xi, not to a nonprincipal minimal prime of an arbitrary affine coordinate ring. Its injectivity, Noetherianity and prime-ideal hypotheses have all been checked.

Cited statements read: sbc-lem-smooth-criterion, def-weil-flat-morphism, lem-trf-flat-module-torsionfree-domain, sbc-lem-smooth-geometrically-reduced, lem-weil-pbc-minimal-prime-reduced-localization-field, lem-sbc-scheme-fibre-stalk-quotient, lem-sbc-regular-principal-prime-localization-dvr.

Step 4: Smooth composition and the smooth criterion give flatness of V/T. The cited torsion-free result, not just the definition of flatness, proves injectivity of pi at the stalks. The affine nonzerodivisor-complement theorem gives schematic density. The separated-target agreement node explicitly states equality for Z-morphisms agreeing on a schematically dense open. It needs only separatedness of W/Z, which is assumed.

Cited statements read: lem-trf-smooth-composition, sbc-lem-smooth-criterion, def-weil-flat-morphism, lem-trf-flat-module-torsionfree-domain, lem-pc-affine-nonzerodivisor-complement-dense, lemma-nagata-ext-scheme-theoretically-dominant-separated.

Step 5: The base-change statement supplies smoothness of V_k/Z_k and W_k/Z_k. The smooth reduced/dominant-pullback statement actually says that generic component points map to generic component points, and its base Z_k is reduced and locally Noetherian as required. Finite-component topology explains why the local dense open contains these points. This uses the statement of that node, not its proof.

Cited statements read: lem-pc-proper-base-change, lem-trf-smooth-reduced-dense-pullback.

Step 6: The local-scheme limit statement gives the directed affine-neighborhood system and the compatible canonical map. The fibre-product limit statement identifies its V pullback. The qc-open descent node states both descent of the domain and its resulting restricted inverse-limit system. Every stage is qcqs by Step 2 and transitions are affine; D_xi is qc by Noetherianity.

Cited statements read: lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods, lem-weil-pbc-limit-fibre-products, pqf-lem-limit-qc-open-descends.

Step 7: The arrow-descent node requires finitely presented qcqs source and target models, verified in Step 2 for the descended open and W_N. Its conclusion gives the exact local pullback of the morphism over the base. This is not an application to arbitrary non-small diagrams: the neighborhoods form a set in the fixed scheme universe.

Cited statements read: lem-weil-pbc-finite-presentation-arrows-descent.

Step 8: The equality-descent node states eventual equality of maps into a locally finite type target. Its source is the qc affine-transition system of generic opens; its limit is the L_xi fibre by Step 3 and the fibre-product limit node. I compare maps to W_E over Z_E, so the required local finite type hypothesis comes from W/Z. A mere equality of rational classes is not substituted for equality on the prescribed generic domain.

Cited statements read: lem-weil-pbc-limit-fibre-products, lem-weil-pbc-locally-finite-type-limit-map-equality.

Step 9: The scheme-morphism gluing node explicitly gives existence and uniqueness of a map from an open cover. Agreement is supplied by Steps 4 and 8. The map is over Z because that equality can be tested on the cover. Step 5 proves that the resulting open meets every component of the Noetherian special fibre. The generic open is added explicitly, rather than assumed to descend automatically.

Cited statements read: lem-weil-pbc-scheme-morphism-gluing.

Step 10: The open-descent and arrow-descent statements apply separately to both local opens and both arrows, all qcqs/finitely presented. The image includes the entire local generic target because h_E is an isomorphism and the domain includes the entire local generic source.

Cited statements read: pqf-lem-limit-qc-open-descends, lem-weil-pbc-finite-presentation-arrows-descent.

Step 11: The eventual-equality statement is applied to the two inverse identities and then to the prescribed generic maps, with their fixed lft targets. It imposes no separatedness on V. A common later neighborhood preserves all finitely many equalities. Thus these are genuine isomorphisms of opens, not just equality on geometric points.

Cited statements read: lem-weil-pbc-locally-finite-type-limit-map-equality.

Step 12: This is an elementary finite-component set argument: each xi_i lies on none of the other components, so removing those closed subsets keeps it. A point on the special fibre of an intersection would have to belong exclusively to two different components, impossible. Restricting the base preserves the local-scheme pullback. No regularity or disjointness of entire special-fibre components is assumed.

Cited statements read: none; elementary.

Step 13: The gluing statement gives both maps; its uniqueness part identifies the composites with the identities on the two open covers. Overlaps for distinct base neighborhoods lie in the generic fibre by Step 12, so they agree using Step 11 even though V need not be separated. Density is checked on V_k and W_k using the generic-point statement already established in Step 5.

Cited statements read: lem-weil-pbc-scheme-morphism-gluing.

Step 14: The field-universal-openness node explicitly permits arbitrary schemes and arbitrary base schemes over a field. For each of the two fibres its projection is therefore open. The written nonempty-open argument proves preservation of density; it does not need finite type, a surjective projection lemma, or schematic density for arbitrary X. The two point-image hypotheses on R to R-prime ensure the correct generic and closed field extensions.

Cited statements read: lem-sc-scheme-over-field-universally-open, def-pc-base-change.

Step 15: Base change preserves the inverse identities by the fibre-product universal property and preserves open immersions by the cited node. Step 14 supplies relative density on both sides and on a common agreement open, so the conclusion is well-defined on birational representatives.

Cited statements read: def-pc-base-change, lem-weil-pbc-open-immersion-base-change.

I tested the empty schemes and empty special fibres (choose the whole generic open, or the empty domain when appropriate), disconnected special fibres, positive-dimensional smooth fibres, noncomplete DVRs and imperfect residue fields. For the affine sanity check Z=T and V=W=A^1_T, h_E(x)=pi^{-1}x fails the local-extension hypothesis at the special generic point, exactly as it should. For nonseparated V the proof only glues its inverse on generic overlaps, never applies separated-target uniqueness to V. For the last assertion arbitrary X may be nonreduced and non-Noetherian: the argument uses openness over fields, not a generic-point characterization of density that could fail with infinitely many components. Ramified and transcendental DVR extensions are allowed; only their induced residue-field maps enter that argument.

Checked delivery-errors B1–B10: no new unsplit statement hides a proof, no hollow definition or undeclared new notion was added, and all exact search queries were run. Checked C1–C8: all substantial descent, uniqueness, generic-point and openness facts are cited by statements that say exactly what is used; every citation has a verbatim quote in citations.json. Cross-unit uses are declared as generic tools in split_report.tool_uses. Checked D1–D5: the item itself carries the spreading and birational assembly, rather than moving its clauses into newly named nodes. Checked E1–E7: all finiteness, flatness, density and separatedness hypotheses are matched above, the generic compatibility and inverse equations are explicit, and no false inference from image containment to subscheme factorization is used. Every proof step is below 2000 characters, and no standard intermediate comparison is left without its existing cited node. Statement unchanged; no STATEMENT-DISPUTED issue found.
