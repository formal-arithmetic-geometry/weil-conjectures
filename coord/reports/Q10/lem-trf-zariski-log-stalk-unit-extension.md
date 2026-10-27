# Stage-1 report: lem-trf-zariski-log-stalk-unit-extension

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-zariski-log-stalk-unit-extension.json`: statement, split; no Mathlib match. The statement and statement dependencies are unchanged. Six proof steps assemble existing results, with the elementary orbit and cancellation computations written out.
- `citations.json`: eight entries, one per step/node citation, copied verbatim from the corresponding current node statements.
- `report.md`: this report.

No new nodes, no Mathlib leaves, no Lean files, no compiler or Lake calls. `ilo.txt` and `write_split.py` are sandbox research files only.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag/id, Zariski log structures, LogStructure, CharacteristicMonoid, FineSaturated and change-of-units terminology. No project declaration states this item. Ordinary stalk maps, Gm stalks, germ injectivity and localization lemmas are not attachments of a logarithmic statement. Existing sorry declarations would not constitute attachments.

## WANTED

None needed to finish this split. ILO VI 1.1 refers to Kato (1988), section 1, for the general logarithmic language; the existing associated-log and change-of-site nodes explicitly state the needed construction and stalk formulas. This delivery uses their statements rather than pretending ILO prints the full change-of-units theorem.

## Findings and route

The live item was unsplit and had no repair note; the sandbox had no earlier item or report. Read the worker brief, role, stage-1 document, GOAL, SETUP's three levels, STATE, tools README, and delivery-errors B--E in full (both repeated copies). The newer direct-delivery instructions control the read-only workspace, recorded searches, no compiler, and self-delivery.

Read the chapter and unit records, and the current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/_section.md` and `lem-trf-local-term-locality.proof.md`. The latest blueprint uses contracting correspondences, whereas the already-created item's `blueprint.from` accurately calls its logarithmic alteration ancestry historical. This split proves that existing supporting item; it does not replace any unit or chapter step, change their statements, or resurrect the old nearby-duality route. The blueprint provenance is retained and explained in split_report.blueprint.

No statement dispute or mathematical correction was necessary. In particular, no claim that the log structural map is injective, that X is integral, or that A is a domain is used. Those stronger claims need log regularity or additional hypotheses that are absent here.

DAG/blueprint duplicate searches covered “log stalk”, “logarithmic”, “monoid”, “characteristic monoid”, pushouts/integrality, strict-henselization stalks and faithful flatness. Read the statements of `lem-trf-associated-log-universal-stalks`, `lem-trf-prelog-pushout-log-axiom`, `lem-trf-filtered-ring-log-pushout`, the prelog comparison, chart face localization, fs face sharpening, strict-henselization triples/functoriality and the six proof inputs. Reused existing statements rather than adding generic monoid or strict-local ring nodes. A dependency-graph traversal of every proof input found no path back to this item.

## Mathlib search results

The original item's earlier five recorded searches are retained. Ran new searches with the prescribed msearch command, recorded in searches.jsonl and copied with exactly the same tool/query strings into mathlib_searches:

- LeanFinder: the complete Zariski/etale log-stalk integrality and injection statement. Returned ordinary scheme germ-injectivity and stalk-map lemmas, not log structures.
- Loogle: `"LogStructure"`, no hits.
- Grep: `LogStructure|log.structure|characteristic.monoid|FineSaturated`, no hits.
- LeanSearch: pushout adjoining units for changing logarithmic sites. Returned ordinary structure-sheaf stalk/localization, local-ring-map and Zariski/etale topology inclusion facts.
- Second LeanFinder phrasing: cancellativity under extending a subgroup of units. Returned monoid localization cancellation and `Function.Injective.cancelCommMonoid`. These do not supply a log change-of-site comparison or the pushout calculation. They confirm the familiar cancellation algebra, which is written directly as elementary proof steps.
- Grep of the returned names, then a corrected directory-scoped grep: read Mathlib/Algebra/Group/InjSurj.lean lines 86--102 and 180--196. The first file-scoped search reports malformed path fields because rg omits filenames for a single input file; the second, over Algebra/Group, gives the correct paths/lines (94 and 187). Both real searches are retained. Neither is a match to the item. No service was unavailable.

## Not duplicates

No new nodes were created, so there are no new/existing-node pairs to distinguish. The general prelog comparison and chart-localization nodes are used directly; their conclusions are not repackaged as children.

## Review by Q10

I read ILO VI 1.1, printed p.69, for the log/chart/characteristic conventions; VIII section 3 opening, p.97, for the Zariski convention; VIII 3.3.2--3.3.4(ii), pp.106--107, for associated Zariski and etale log structures and existence of charts; and VIII 3.1.1--3.1.5, pp.98--99, for integral monoids, localization, and sharpening. The item is an agent extraction rather than a numbered ILO assertion, so proof_origin is agent. No new node needs a separate source review. I also read Stacks 04KF (spaces-properties.tex, lemma-describe-etale-local-ring), its scheme case 04HX (etale-cohomology.tex, same label), 07QM (more-algebra.tex, lemma-dumb-properties-henselization), and 05CK (algebra.tex, lemma-faithfully-flat-universally-injective).

Step 1 uses the actual log-structure definition in def-trf-fs-log-blowup for the unit-locus isomorphism and the actual stalk and logification comparison clauses in lem-trf-zariski-prelog-logification-comparison. The parameter sheaf is the given N_Z, not a constant chart, so the general prelog-sheaf node is needed. I checked its hypotheses: X is locally Noetherian, N_Z is a sheaf of commutative monoids with a structural homomorphism, and xbar is geometric over x. Unit germs are units after shrinking because an inverse and its equation are finite germ data. Zariski logification of an already logarithmic sheaf is identified explicitly by [l,a] -> l+a. The cited statements supply the canonical stalk formulas, and their compatible prelog maps supply the structural formula used here.

Step 2 cites no non-elementary input. I checked the orbit relation explicitly: G consists of actual invertible elements of L, so translation by a unit pair gives an equivalence relation; the product of two orbit relations is again one, using the product of the two group elements. Thus it is exactly the generated monoid congruence, even before L is known integral. The two displayed maps on characteristics are mutually inverse by calculation on representatives. This avoids assuming cancellation prematurely or hiding the characteristic comparison in a new node equal to the item.

Step 3 uses lem-trf-chart-face-localization-logification for precisely its face, localized pushout, and characteristic isomorphisms; no section/splitting of the quotient is assumed or taken from its proof. Its ring named A is our B, its log stalk named L is our M, and its face F is our E. Every hypothesis holds on the given pointed etale chart. Lem-trf-fs-face-sharpening supplies integrality of Q-E and its exact unit subgroup E^gp; its fs and face hypotheses were supplied by the chart and the preceding application. Def-trf-fs-log-blowup guarantees existence of one such chart when none is fixed in the first clause. The characteristic map is canonical because both cited maps send the chart class to its germ class.

Step 4 is the elementary cancellation argument in this concrete pushout, not an appeal to an unstated theorem that pushouts preserve integrality. Equality after adding [t,k] produces one u in the unit subgroup. Cancellation in R, a submonoid of Q^gp by the fs face result already applied, and in H proves equality before adding [t,k]. I wrote the group-completion criterion as well. There is no requirement that the structural map E^gp -> B^times be injective, which would be false for a general chart.

Step 5 uses the first, canonical-stalk clause of lem-sfb-space-strict-local-flatness with the identity chart of the scheme X over itself. Its statement explicitly provides O_(X,xbar) = O_(X,x)^sh; the identity map is etale and the geometric lift is xbar. This tool is more general than the scheme case needed here, and I checked its canonical function-germ identification against Stacks 04KF/04HX. Lem-sc-strict-henselization-faithfully-flat then applies to the local ring A and the separable closure selected by the geometric point. Lem-weil-pbc-faithfully-flat-ideal-contraction explicitly concludes injectivity for I=0. Thus the cited statements really give the ring injection and hence the injection on unit groups. These three nodes are declared as generic off-unit tool uses in split_report, with reasons; no source's route is replaced.

Step 6 uses only steps already proved. An equality [l,1]=[l',1] gives a unit a with iota(a)=1; the unit injection forces a=1, giving l=l'. Cancellation in the target then reflects to L. This order is essential: I did not assume L integral to prove its own injection. The final structural, germ, chart and units compatibility equations are written on representatives and do not assert compatibility just by the word “transport”.

I checked edge cases: the trivial log structure gives L=A^times and M=B^times, including Q=0 and E=Q; a chart with all elements mapping to units gives characteristic zero and the same cancellation proof; rank-zero characteristic causes no choice of generators or nonzero element. In the standard chart N -> k, 1 -> 0, the structural map is not injective, but the proof still applies because all cancellation is in the log monoid, not in the ring. Torsion in unit groups is allowed. X may be empty (then no x is available and the statement is vacuous), reducible, nonreduced, or nonnormal. No finite cover, affine intersection, log regularity, or domain assumption enters.

Checked delivery-errors B--E point by point: no new-node schema/definition/citation problem arises; every cited result was read and contributes its statement, not its proof; all non-elementary inputs have node citations; the elementary calculations are explicitly given; there is no relabelled child or cycle; all hypotheses and canonical maps are tracked. Every step has fewer than 1000 characters, so no >2000-character step hides a subsidiary lemma. The original statement, metadata, blueprint provenance and searches are retained. The sandbox is the only location written.

## Unfinished work

None in the authorized stage-1 split. The existing cited nodes may themselves remain open; their further splits are outside this one-level delivery. Required server checks and delivery follow.
