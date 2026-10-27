# NG: lem-per-tame-trait-quotient-log-etale

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-tame-trait-quotient-log-etale.json: existing statement split into nine explicit steps; full statement, source, statement dependencies, creation record, inherited searches and blueprint provenance preserved.
- citations.json: one verbatim statement quotation for every dependency of every proof step.
- report.md: this report.

No new nodes and no new Mathlib leaves. The sandbox also contains the actual msearch.py search log, an extracted text of the supplied ILO PDF for reading, and a preparation script; these are research material, not additional DAG deliverables.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint id and the notions tame trait, tame quotient, logEtale, LogEtale and Kummer. The two StalkNormalizationTraitSection local-algebra files concern normalization stalks and do not state all clauses of this item. The historical deleted Sheaf module in lean_removed is not a current attachment.

## WANTED

None for this delivery. I read the supplied ILO PDF locally. The existing generic logarithmic composition node mentions Kato 1988 as WANTED in its own provenance; I use that existing node's statement, and do not claim to have read Kato or repair its proof here.

## What was wrong and what changed

The released stage-1 repair note and coord/changes/20261024-Q108-log-alteration-inputs.md explicitly reopen this interface and invalidate the retired proof closure. The live item had no proof. I reconstructed the algebraic calculation and the Kummer comparison independently rather than restoring historical dependencies. The mathematical statement is true as written, including nonfaithful actions and possibly imperfect separably closed residue fields; no STATEMENT-DISPUTED correction was needed.

The current blueprint/latest chapter, unit and ancestor proof were inspected. The item is not the unit key node. Its inherited blueprint ancestry records a historical route through Artin--Gabber, but Q108 explicitly preserves that provenance while reopening just the geometric XVI 3.7 interface. This delivery uses no Artin--Gabber result, no arbitrary-field adic duality, and no SGA source. The current source statement is XVI 3.7, not the old ancestor proof. Searches of the whole imported blueprint for Kummer, tame trait, uniformizer and fixed field, and searches of dag/nodes for the corresponding statements and Mathlib declarations, found the existing tools used below. No new alias was needed.

In particular, I noticed that lem-per-log-smooth-composition-strict-base-change is still excluded. I instead cite the already existing lem-sfb-log-smooth-composition-strict-base-change. I inspected that node's statement and recursively checked the complete statement/proof closure of all dependencies selected for this delivery against coord/route-pivot-dropped.txt: the intersection is empty. No excluded prerequisite or new duplicate replacement is introduced.

## Not duplicates

No new node was created. The following matches were reused rather than duplicated: lem-wf-finite-field-action-fixed-degree (Artin's theorem for a finite faithful action), lem-sfb-finite-invariant-fraction-field-lifting (fraction fields of invariants), lem-weil-pbc-noetherian-submodule-finite, lem-weil-pbc-finite-over-complete-local-product, lem-exc-dvr-galois-degree-data, lem-sfb-totally-ramified-uniformizer-presentation, and lem-sfb-log-smooth-composition-strict-base-change. Elementary averaging, valuation restriction and rank-one chart algebra are explicit steps, not new nodes.

## Mathlib searches

All new searches were run with the prescribed msearch.py command and their actual results were read. They are appended verbatim as logged summaries to mathlib_searches; every inherited search is preserved. For the generic-action question, LeanFinder and Loogle returned FixedPoints.finrank_eq_card; the logged FieldTheory grep located it at Mathlib/FieldTheory/Fixed.lean:346 and IsGalois.of_fixed_field at Mathlib/FieldTheory/Galois/Basic.lean:95. I read those declarations. They match the already existing Mathlib leaf lem-wf-finite-field-action-fixed-degree, not the whole item.

For the item itself I ran LeanFinder on the finite mixed-characteristic strictly henselian trait quotient and logarithmic etaleness, Loogle on "LogEtale", a whole-Mathlib grep for logarithmic-etale spellings, and LeanSearch with a second phrasing about tamely ramified traits and composition. All services answered. The first semantic query returned perfection, valued residue finiteness and ordinary standard-etale algebra; the second returned ordinary formally smooth/etale composition. The direct logarithmic searches had no hits. These do not identify the item's logarithmic assertion with ordinary etaleness. The existing leaf is cited instead of adding a new field-action node.

## Review by NG

I read ILO, Expose XVI 3.7, printed p.254, from the definition of T=S'/H through the inference of log smoothness over T. The text explicitly asserts the tame extension and its logarithmic etaleness but omits the algebra. I also read Expose VI 2.1--2.2, printed pp.71--72, including the standard Kummer base-change model. My proof_origin is honestly agent: the detailed invariant-ring and uniformizer argument is an independent expansion assembled from the existing cited statements. I read the Stacks source passages behind the main tools: algebra.tex 0325 (lemma-quotient-complete-local), more-algebra.tex 0ALJ (lemma-complete-henselian), algebra.tex 04GG (lemma-characterize-henselian), more-algebra.tex 09EB (lemma-galois-conclusion), and the initial uniformizer/minimal-polynomial paragraph of 09ER (lemma-weakly-unramified-goes-up-along-totally-ramified). There are no new nodes requiring a separate source audit.

For step 1 I checked the statements of lem-weil-pbc-noetherian-submodule-finite, lem-weil-pbc-finite-algebra-is-integral and lem-weil-pbc-integral-maximal-contracts-maximal. They give exactly finite invariants as an R-submodule, integrality of the finite map, and locality at the maximal ideal. I wrote out why the same R-generators generate B over A, and why dominance gives injectivity. This avoids assuming locality just from a nonzero map of traits.

For step 2 I read the full invariant-fraction-field leaf: it permits an arbitrary finite action and an injective inclusion whose image is the invariant ring; no integrality or faithful action is assumed there. The displayed product of the translates of a denominator also verifies that identification directly. The fixed-degree leaf requires faithfulness, so I first replace H by its image G in field automorphisms. It states finite Galois and degree = |G|, exactly what this step takes. The divisibility by |H| then follows by counting kernel cosets. This is necessary: with trivial action the degree is one, not |H|.

For step 3 the DVR definition explicitly supplies the normalized valuation convention; the two valuation leaves supply the nonnegative-membership criterion and valuation arithmetic. The argument is short valuation restriction, with its hypotheses and ideal calculation given explicitly: F contains a positive-valuation element from R, the least positive value generates its value subgroup, and a least-valuation ideal element divides every other. No normality/descent theorem is hidden here. I checked the integral-closure assertion using the monic equation: a negative valuation would give exactly one smallest-valuation term. Thus later ramification and uniformizer-presentation lemmas are applied to the actual integral closure B, not just an arbitrary DVR with fraction field L.

For step 4 I read the full finite-complete-local-product statement. Its domain clause applies because A is a subring of B; this supplies completeness for A's own maximal ideal, not merely completeness for an unspecified ideal from R. The complete-pair statement gives henselianity, and the local-root-lifting equivalence converts its convention to the monic simple-root convention in the item. All cited statements give these precise conclusions; no property of an unknown completion is assumed.

For step 5 the finite-extension-over-a-separably-closed-field leaf states purely inseparable, not trivial. This distinction matters when k is imperfect. I checked the residue field extension is finite using the finite R-generating set and the locality established in step 1. Pure inseparability forces H to fix k' elementwise; Reynolds averaging is legitimate since |H| is a unit. The average reduces to the original residue, proving k_A=k_B. This transfers the given separable closedness of k_B to k_A. The fraction characteristics remain zero and the residue characteristic is p.

For step 6 I read the complete degree-data node: it assumes a finite normal separable extension and uses its integral closure; both were verified in steps 2 and 3. B has one maximal ideal and the residue degree is one by step 5. Its exact g e f formula gives e=n. An inequality e <= [L:F] would not suffice, and I did not substitute one.

For step 7 I tested all hypotheses of the totally-ramified-uniformizer-presentation node: complete base DVR, finite separable degree n, actual integral closure, local map, equal residue fields, and maximal-ideal ramification exponent n. It states the polynomial presentation for every uniformizer of B, so it applies after replacing t by the unit multiple tau. I wrote the root lifting calculation and explained why the monic degree-n annihilator X^n-pi is the minimal polynomial. Thus the comparison is an actual A-algebra isomorphism, not merely a field isomorphism or equality of degrees.

For step 8 I checked the sets-valued strictly-henselian sections-to-stalk statement, the full fs logification definition, the affine-spectrum fibre-product statement, the ordinary-etale definition and the chart-log-etale definition. The first is used on the actual canonical log sheaf at the closed point. Nonzero elements of a DVR are uniquely a uniformizer power times a unit; at the generic point the chart element is invertible. This proves the chart realizes the specified canonical log structure. I computed the tensor-ring comparison, and the group map is multiplication by n with zero kernel and cokernel Z/n. The isomorphism from step 7 is the actual chart comparison. For ordinary etaleness an isomorphism is flat, of finite presentation and unramified (its diagonal is the identity), so the cited definition is sufficient. This proves log etaleness without the excluded general SNC chart lemma or an excluded Kummer comparison node.

For step 9 I read the permitted sfb composition statement: it says both that log etale implies log smooth and that log-smooth maps compose. These two clauses give the composite in the order V -> S' -> T, regardless of the mixed-composition wording in that node. Its locally Noetherian fs assumptions are exactly present. The recursive route check mentioned above checked its dependencies too. Its cross-unit use is declared explicitly as a generic tool, as are the other non-Mathlib cross-unit tools; none changes the unit route.

I checked B--E of delivery-errors.md against these files: no statement-only new nodes containing hidden proofs, no new undefined notions or duplicate aliases, no unrun searches, no cited node used for something absent from its statement, no missing source-backed non-elementary assertion, no circular dependency, and no clause moved to a new node. The full inherited statement and dependencies are preserved as ordered by Q108. Each dependency of every step has a verbatim complete-statement quote in citations.json. All nine steps are below 2000 characters; the longest is the explicit chart calculation. The computation is elementary after the cited lemmas and does not hide an additional comparison lemma.

Small cases checked: H trivial, a completely trivial nonfaithful action, and any nontrivial action with a kernel all give the image-group degree; n=1 makes the root presentation and log comparison identity maps; imperfect separably closed residues are handled by purely inseparable extensions and averaging; a wildly ramified preliminary S'/S is allowed since the proof only constrains S' over the invariant trait; empty or disconnected V causes no additional condition in composition. No residue-perfectness, faithful H-action, or condition on V beyond the statement was inserted.

## Unfinished work

None in this one-level stage-1 split. Existing unsplit/open dependencies remain their own items. No Lean was written, no compiler or Lake command was run, and no repository or launcher file was edited.
