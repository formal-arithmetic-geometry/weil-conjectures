# Stage-1 report: lem-sfb-smooth-model-volume-order-comparison

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-model-volume-order-comparison.json: item, statement; split into seven proof steps, preserving the imported statement and blueprint metadata.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-trait-volume-infrastructure.json: new statement-only node, unsplit; no Mathlib match. General local geometry of smooth finite-type trait schemes, special-fibre generic DVRs, density, and differential rank.
- dag/nodes/sec-six-functors-basics/lem-sfb-trait-line-section-order-normalization.json: new statement-only node, unsplit; no Mathlib match. Uniform vertical orders normalize an everywhere-generating generic line section, including evaluation of generic units on DVR-valued sections.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-cotangent-etale-criterion.json: new statement-only node, unsplit; no Mathlib match. The relative cotangent criterion for a map between two smooth schemes, with the elementary determinant reformulation.
- citations.json: one entry per cited node per proof step, quoting its statement verbatim.

There are three new nodes and zero Mathlib leaves. The new nodes are deliberately not split. All searches were made with the prescribed msearch.py command; searches.jsonl retains the actual results. LeanFinder and LeanSearch supplied two phrasings for each new statement, followed by Loogle and source grep. I read the returned candidates, including OrderOfVanishing.ordHom_of_isUnit and ord_of_isUnit, and the algebraic formally-etale differential equivalence: none supplies these geometric extension or converse statements. The item also received fresh concept searches. No Lean was written or compiled.

## Attachments

None. The blueprint-tag and concept searches under lean/WeilConjectures found no project declaration proving every clause of the item. A Mathlib result is not claimed as an attachment.

## Literature wanted

WANTED: Bosch–Lütkebohmert–Raynaud, Néron Models, 4.3 order construction and Lemma 1, printed pp.104–105 (PDF pp.110–111), for lem-sfb-smooth-model-volume-order-comparison and lem-sfb-trait-line-section-order-normalization.

WANTED: Bosch–Lütkebohmert–Raynaud, Néron Models, 4.3 p.104 and 2.2 Proposition 5, for lem-sfb-smooth-trait-volume-infrastructure.

WANTED: Bosch–Lütkebohmert–Raynaud, Néron Models, 2.2 Proposition 8 and Corollary 10, printed pp.40–41 (PDF pp.46–47), for lem-sfb-smooth-cotangent-etale-criterion.

The BLR PDF is absent from the local literature tree. I downloaded nothing into the repository or sandbox. I read the primary scan through the web reader at https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf, including the paragraphs preceding Lemma 1, its proof, and the differential criterion. The proof is marked agent-origin as required for a missing local source. I also read the local Stacks statements on regular smooth ascent (07NF), regular schemes being normal (0569), height-one intersection for normal domains (031T), schematic density under flat base change (081H), and smooth differential rank (02G1). No SGA route is used.

## Corrections and scope

The imported statement is retained: no statement dispute was found. The old narrative needed explicit support for normalization, the cotangent criterion, and the geometric facts underlying the order. These are general supporting statements, not substitute comparison or open-immersion conclusions. The comparison itself remains an argument in the item, including the determinant identity, valuation inequality, both directions of the equivalence, and the finite-component conclusion on the whole domain.

I corrected two potential unsupported inferences while writing the split. A DVR strict-henselization node alone does not assert that the original uniformizer remains a uniformizer; the triples construction supplies the equality of maximal ideals and strict henselianity. Likewise the cover's preservation after base change is now cited explicitly rather than assumed. The determinant coefficient is used only where the rational map is defined. No extension of that coefficient across an indeterminacy locus is claimed.

The unit and current latest blueprint unit were read. This node continues the existing BLR bounded-group/translation-model branch under sk-thm-sf-ctf-stability. Blueprint ancestor lookup returns no imported ancestor; the inherited null ancestor and full via chain are retained. Searches over the whole DAG and blueprint for the source places, trait geometry, line-section orders and the differential criterion found no existing node stating these three new results. Off-unit tools are declared individually in split_report.tool_uses.

## Unfinished work

No part of the item's stage-1 split is intentionally left unfinished. The three supporting nodes have complete statements but no proofs, as required for one-level splitting; they remain unsplit for later work. The missing local BLR copy is recorded above.

## Not duplicates

lem-sfb-smooth-trait-volume-infrastructure vs lem-sfb-smooth-trait-curve-local-properties: the existing node concerns relative curves; the new statement allows arbitrary pure generic dimension and identifies every vertical generic DVR and its uniformizer.

lem-sfb-smooth-trait-volume-infrastructure vs lem-sc-smooth-omega-finite-locally-free: local freeness alone does not identify the constant rank from generic purity, nor give density, regularity, the special-fibre components or their DVR stalks.

lem-sfb-smooth-trait-volume-infrastructure vs lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension: the existing fibre-dimension formula does not state the smooth trait geometry and its vertical generic local rings.

lem-sfb-trait-line-section-order-normalization vs lem-sfb-local-generic-unit-factorization: the existing result is local-ring factorization under integral-fibre hypotheses; the new result concerns an invertible sheaf on the entire model with possibly several special components and a specified common order, together with the section valuation formula.

lem-sfb-trait-line-section-order-normalization vs lem-sfb-trait-primitive-section-specialization: primitive specialization of a merely nonzero generic section on the existing more restricted model does not assert an everywhere-generating extension or the evaluation formula for an arbitrary generic unit.

lem-sfb-trait-line-section-order-normalization vs lem-sfb-normal-open-line-weil-dictionary: a divisor/line-bundle dictionary does not assert extension and invertibility of this fixed generic frame, nor the valuation measured by an arbitrary DVR-valued section.

lem-sfb-smooth-cotangent-etale-criterion vs lem-sfb-smooth-trait-local-rational-spreading: spreading is an extension/uniqueness assertion for rational maps; it does not characterize etaleness by the relative differential map.

The new geometry node isolates reusable local smooth-trait structure. Although the item mentions its DVR consequence, this node does not restate the volume-order comparison or replace a conclusion by an opaque new lemma. The normalization node proves a general line-section extension statement, not the inequality or its open-immersion characterization. The differential criterion is BLR's independent general smooth-to-smooth theorem, with no volume or trait hypothesis.

## Review by NB

I read delivery-errors B–E in full and reviewed the statements and source paragraphs against each step, rather than treating a passing schema check as mathematical review. I checked the source for the item in BLR 4.3, for normalization in its preceding order paragraphs, for the geometric infrastructure in the same paragraphs together with the local Stacks regularity and density results, and for the cotangent criterion in BLR 2.2 Corollary 10 and Proposition 8. The new nodes introduce their rings, schemes, fibres, sheaves and maps explicitly and have only statement dependencies, not hidden proof claims.

Step 1 uses the new smooth-trait infrastructure for regularity, differential rank, disjoint special components and the vertical generic DVR with uniformizer pi. The remaining existence and uniqueness of an order is the elementary DVR factorization of a nonzero coefficient in a rank-one module; I checked the cited DVR definition. Smooth finite-type group fibres have the stated pure dimension. This also explains exactly why the component-plus-generic-fibre subsets used later are open.

Step 2 uses that infrastructure for density and nonemptiness of the generic fibre; together with the assumed nonempty special fibre this makes the map onto the two-point trait surjective. I opened lem-sfb-smooth-space-cover-etale-sections: it assumes a smooth surjective morphism, exactly what is available. I opened lem-trf-space-fibre-products-etale-covers: its jointly surjective etale-family clause applies after strict-henselian base change and ensures a member meeting the closed point. I opened lem-weil-pbc-strict-henselization-triples: it says both that the resulting local ring is strictly henselian and that its maximal ideal is the extended original prime. The section theorem applies to that etale member and its closed-fibre point. Finally lem-sc-strict-henselization-dvr supplies the DVR property, while the triples node, not the DVR node, supplies pi as uniformizer. These are generic lifting tools; they do not change the unit's route.

Step 3 uses the normalization node twice for the two determinant lines and once for the trivial line with generic frame a. Its generic frame hypothesis is satisfied because omega is nowhere vanishing and a is a generic unit. Irreducibility and nonemptiness are the item's hypotheses. The selected section need not lie in the domain of u: only a and its extension on M are evaluated. The valuation formula gives m=0 exactly, hence a global unit.

Step 4 uses only the final uniqueness clause of lem-sfb-smooth-trait-local-rational-spreading, which I read explicitly, with Z equal to the trait and the separated target N. It permits gluing the representative to the prescribed map on the entire generic fibre. The differential and exterior-power definitions give the determinant map on the domain U; the normalized global frames then give the displayed scalar identity. Base-density puts the special generic point in U. DVR factorization gives the inequality without assuming regularity of b outside U.

Step 5 uses schematic density from the geometry node to extend the equality b=a on U. Both differential sheaves have the same rank, so the determinant clause of the new smooth-cotangent criterion applies. I checked that the existing flat-isomorphism-dense-open statement requires separatedness, flatness, local finite type, and a quasi-compact schematically dense target open, with no quasi-compactness assumption on U. Etaleness supplies flatness and local finite presentation by its cited definition; the diagonal gives separatedness, and N_E is the required quasi-compact schematically dense open. The scheme case of the existing algebraic-space criterion therefore proves an open immersion everywhere on U, not only near the special generic point.

Step 6 is elementary from the open-immersion and differential definitions: restricting a sheaf and its universal derivation along an open immersion identifies the differential sheaves. The determinant is a unit at the special generic DVR, so the coefficient identity from step 4 gives equality of orders. No uncited converse differential theorem is used here.

Step 7 first normalizes the two top forms using the common order on all components. For each source component, the component-plus-generic-fibre open has irreducible nonempty special fibre, so the section hypothesis invokes the normalization node with exactly its hypotheses. Those opens cover the entire domain. The determinant is therefore a unit on that entire domain, and the same global criterion of step 5 applies once to the whole map; no unsupported gluing of component images is used. Empty special fibres are allowed in this last clause: the normalization statement allows arbitrary n when empty, and if the source special fibre is empty then its domain is its generic fibre.

I tested rank zero (the determinant is the identity of O), negative orders of omega, generic-only connected components, several special components, an empty special fibre in the finite-component clause, an imperfect residue field and an arbitrary nonexcellent DVR. The facts used require none of perfectness, excellence or properness. Strict henselization is invoked with a separable closure, not an algebraic closure. The normalization node requires a generating generic section, not merely a nonzero section; it extends by normal height-one detection, and has no uniqueness-of-order assertion when the special fibre is empty. Its unit valuation assertion is restricted to DVR extensions in which pi is a uniformizer. I checked that every citation quote is copied from the actual cited statement and that proof_deps is precisely the union of step uses. Every proof step is below 2000 characters. I found no hidden independent comparison lemma inside a long step, no duplicate created node, and no Mathlib leaf being treated as absent without searches.
