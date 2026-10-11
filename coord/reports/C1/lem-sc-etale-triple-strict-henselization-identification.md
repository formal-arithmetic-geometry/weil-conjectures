# Stage-1 report

Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-etale-triple-strict-henselization-identification.json`: repaired statement node and direct five-step proof.
- `citations.json`: verbatim citations for every proof-step dependency.
- `report.md`: this report.

Attachments: none. No sorry-free declaration in `WeilConjectures/` states the item exactly.

WANTED: `literature/stacks-project/algebra.tex`, Tags 04GW, 04GP, and 08HR, for the strict-henselization and henselian-colimit comparison arguments.

The returned split was wrong because `lem-sc-localized-triple-colimit` merely unfolded the item's definition of $A^{\\mathrm{sh}}$ and restated the main colimit clause. I removed that node. The proof now uses the existing strict-henselization triple construction and the existing map-into-henselian-colimit lemma directly. I also restored the existing adic-completion definition as a real dependency and converted the proof notation to TeX.

## Review by C1

I read the item against Tags 04GW and 04GP and checked the statements of `lem-weil-pbc-strict-henselization-triples`, `lem-weil-pbc-map-into-henselian-colimit`, and `def-weil-pbc-adic-completion`. Step 1 applies the triple construction twice, first to $(R,m,K)$ and then to $(A,qA,K)$; I verified the residue-field hypotheses and recorded the resulting local rings, maximal ideals, and residue field. Step 2 uses the cited preimage clause to show that $S\\to C$ factors through $A=S_q$ by the localization universal property.

Step 3 cites the map-into-henselian-colimit statement for the two filtered etale colimits, with identity residue maps, and checks its henselian-local and filtered-colimit hypotheses from the triple-construction statement. Step 4 uses exactly the uniqueness clause of that map lemma to prove both composites are identities; it also explains why the two maps out of $A$ agree after localization, which is needed before applying uniqueness over $A$. Step 5 uses the local isomorphism to transport $qD$ to $mC$, then uses the cited adic-completion definition for the inverse-limit identification.

I checked the identity triple and field cases: localization is trivial in the identity case, and the maximal ideals and completions reduce to the expected zero-ideal case over a field. The auxiliary node was deleted because it was a relabelling of the item, and all citations now quote verbatim statements of existing nodes. The split report now names `lem-weil-pbc-map-into-henselian-colimit` as the tool use and no longer refers to the obsolete affine-triple route.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.

## Second reading by C1

Step 1 checked against `lem-weil-pbc-strict-henselization-triples` and Tags 04GW/04GP: both triple constructions supply locality, strict henselianity, residue field K, and the stated maximal ideals; the residue embedding for A is explicitly phi. Verdict: passes.

Step 2 checked against the preimage clause of `lem-weil-pbc-strict-henselization-triples` and the localization universal property: elements outside q map to units, so S -> C factors uniquely through S_q. Verdict: passes and is elementary.

Step 3 checked against `lem-weil-pbc-map-into-henselian-colimit`: the source rings are filtered colimits of etale algebras over the stated bases, the targets are henselian local, and the residue maps are identities on K. Verdict: passes.

Step 4 checked against the uniqueness clause of `lem-weil-pbc-map-into-henselian-colimit`, including agreement of the maps after localization. Verdict: passes.

Step 5 checked against locality from the comparison map and `def-weil-pbc-adic-completion`: corresponding maximal-ideal powers and inverse systems are identified. Verdict: passes and is elementary.

There are no new nodes to review: `lem-sc-localized-triple-colimit` was correctly removed as a restatement of the item. I checked the existing dependency statements and searched the repository for duplicate strict-henselization and completion facts; no Mathlib leaf applies. The identity-triple and field cases reduce to trivial localization and the zero-ideal completion.

Changes made: corrected the node's `created.item` metadata; made the induced residue embedding for A explicit as phi; added this per-step second-reading audit.
