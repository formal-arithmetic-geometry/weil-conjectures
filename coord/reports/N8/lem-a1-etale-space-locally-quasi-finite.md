# Stage-1 report: lem-a1-etale-space-locally-quasi-finite

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-a1-etale-space-locally-quasi-finite.json`: item statement, unchanged; now split into three steps. Mathlib verdict: no exact match for the algebraic-space statement.
- `citations.json`: verbatim statement excerpts for both proof citations, indexed by step.
- `report.md`: this report. The required search wrapper also wrote `searches.jsonl` in this sandbox.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter file changed.

## Attachments

None. I searched `WeilConjectures/` in the read-only slopmaster2 source for the exact blueprint tag, algebraic-space terminology, and locally-quasi-finite terminology. There is no declaration for this algebraic-space item. The project declarations mentioning local quasi-finiteness concern scheme morphisms, not this statement. I did not treat upstream master sorry declarations or a Mathlib declaration as attachments.

## WANTED

None: the Stacks sources used are present locally.

## Audit and changes

The imported item was unsplit, rather than false. Its hypotheses already define the chartwise meaning of etale, and its conclusion defines the chartwise meaning of locally quasi-finite. Those two explicit quantifiers remove any need to prove a new atlas-independence or descent theorem here. I kept the entire statement and its four statement dependencies unchanged.

I read Stacks `spaces-morphisms.tex`, Tag 03XU (`lemma-etale-locally-quasi-finite`, lines 7760 onward). Its proof reduces to an etale scheme map, applies Morphisms 03WS, and concludes by definition. I read `morphisms.tex`, Tag 03WS (`lemma-etale-locally-quasi-finite`, lines 8161 onward), which uses etale implies unramified (02GK, `lemma-etale-smooth-unramified`) and unramified implies locally quasi-finite (02V5, `lemma-unramified-quasi-finite`, lines 7778 onward). The latter is already the exact statement of `lem-weil-pbc-unramified-quasi-finite-at-points`. Creating a scheme-etale-to-quasi-finite lemma would add an unnecessary two-line specialization, so I used the existing more general node directly.

The whole-DAG searches included the Stacks tags 03WS, 03XU and 02V5 and the etale/quasi-finite and unramified/quasi-finite concepts. The whole-blueprint searches used `tools/blueprint_refs.py search` for 03WS and locally quasi-finite, and the item ancestor was confirmed as `lem-a1-affine-hc0`. No imported blueprint node states this algebraic-space theorem in another form. The existing unramified theorem is a generic tool of `sk-thm-p1`; `split_report.tool_uses` explains exactly why it is used. This follows the existing 03XU/03WS scheme-reduction route and does not replace a unit step. I read the item's chapter and unit records, the current main-20261015 ancestor text, and the existing parent split. The ancestor text supplies the compact-support vanishing context, not a separate proof of 03XU; the precise auxiliary proof location is already recorded in the item's historical blueprint ancestry.

I retained the inherited Mathlib searches and added only actual wrapper queries recorded in this sandbox's `searches.jsonl`. The two LeanFinder phrasings and the two LeanSearch phrasings returned scheme-level Etale/IsEtale, FormallyUnramified, LocallyQuasiFinite, constructors, and other scheme facts. These do not state a theorem for algebraic spaces. Loogle returned no hits. The whole-Mathlib grep for `AlgebraicSpace|algebraic.space` returned no hits. A preliminary single-file grep returned five documentation headers with filename-less parsing; its record says so, and it is not evidence of a theorem. I read the local scheme classes and candidate source, including `Morphisms/QuasiFinite.lean:71` and `Morphisms/Etale.lean:140`; I did not mistake search-server name/version differences for an exact local declaration. No Mathlib leaf is asserted.

## Not duplicates

No new node was created. In particular, the existing `lem-weil-pbc-unramified-quasi-finite-at-points` is reused rather than duplicated, and no new node restates either the whole item or its chartwise clause.

## Review by N8

I checked the split against delivery-errors B through E with the item, cited statements, and Stacks text open. There are no new-node self-containment, source-tag, or unsplit-proof obligations: this delivery introduces no nodes. The original statement already introduces the base scheme, target scheme, algebraic space, morphism, and both chartwise conditions. Its definition nodes say what it needs: `def-pc-scheme` gives schemes and morphisms; `def-trf-algebraic-space` gives algebraic spaces and representable etale maps tested by schemes; `def-weil-etale-morphism` gives scheme etaleness with unramifiedness as an explicit conjunct; `pqf-def-quasifinite` defines scheme local quasi-finiteness as quasi-finiteness at every point. No proof of a definition is used as an unstated theorem.

Step 1 uses the item's own universal hypothesis for an arbitrary representable etale map from a scheme. The scheme target is precisely T, so the composite is a scheme morphism. I opened `def-weil-etale-morphism` and checked that its statement explicitly includes unramifiedness. Extracting that conjunct is elementary, rather than an unrecorded theorem about smoothness or infinitesimal lifting. Its exact first sentence is in `citations.json`.

Step 2 cites `lem-weil-pbc-unramified-quasi-finite-at-points`. I read its entire statement: it applies to any scheme morphism with the sole additional condition of unramifiedness, and expressly concludes local quasi-finiteness in the same `pqf-def-quasifinite` sense used by the item. Taking its source to be V and its target to be T checks every hypothesis. I am using the statement, not its affine proof or a claim in its docstring. The recorded quotation is its verbatim concluding sentence. This is the only non-elementary step, and it has the node citation that supplies its full conclusion.

Step 3 is universal introduction over the same class of charts fixed in step 1. It adds no comparison between two definitions of algebraic-space local quasi-finiteness, no new covering construction, and no descent assertion. In particular it does not silently replace 'every chart' by 'one surjective chart'. Its source is the final definitional step of 03XU, with the stronger explicit chartwise quantifier already present in the item's own statement.

I tested the hypotheses on the empty algebraic space (the chart conclusions are empty-source scheme statements) and on a representable space E=T with identity map (the tests are exactly etale scheme morphisms). For an infinite disjoint union of copies of a nonempty scheme over that scheme, the result remains local quasi-finiteness; the proof never concludes quasi-compactness, a finite total fibre, or a finite morphism. Non-surjective etale charts cause no problem because the hypothesis applies to every chart, and no argument assumes surjectivity. A nontrivial purely inseparable finite extension of fields is outside the etale/unramified hypothesis, so it cannot be smuggled in through mere finiteness of a fibre.

There was no statement dispute and no source correction. I corrected the missing proof by exposing its actual scheme input and reusing the general existing node. All steps have explicit sources, their `uses` union equals `proof_deps`, both quotes are verbatim, and every step is shorter than 2000 characters. I introduced no hidden sublemma, no circular use of the parent's representability theorem, no SGA route, and no Lean code or compiler invocation.

## Unfinished work

None within this one-level split. The delivery remains subject to the required server dry run and independent maintainer review.
