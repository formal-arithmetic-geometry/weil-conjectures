# Stage-1 delivery: lem-sfb-space-quasicoherent-geometric-stalk-tensor

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-quasicoherent-geometric-stalk-tensor.json: statement, split; unchanged statement and statement dependencies, three proof steps, no Mathlib match.
- citations.json: nine entries, one for every step/node pair; every quote was checked as a literal substring of the cited statement.
- searches.jsonl: five actual Mathlib search records, including two distinct semantic phrasings.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Read-only searches of lean/WeilConjectures for the blueprint tag returned no declaration. Searches for geometric stalk, quasi-coherent module and tensor comparisons found constant-coefficient tensor functors and ordinary scheme stalk material, not a declaration for the item. No compiler or Lake command was run.

## WANTED

None. All sources needed here are available in literature/stacks-project/.

## Findings and changes

The imported statement agrees with spaces-properties.tex Tag 05VP (lemma-stalk-quasi-coherent). Its ordinary chart stalk is not a geometric stalk; no residue-field fibre replaces either stalk. The statement and its hypotheses are unchanged. The item's preexisting blueprint.from.node is null, as printed by blueprint_refs.py ancestor; its detailed from.place and via chain are retained. The latest blueprint direct-images statement, proof (3), and unit were read. This is an existing support input below that route, not a replacement of a unit argument.

The source's colimit proof can be assembled using existing, more general DAG results. In particular, lem-sfb-etale-zariski-module-geometric-stalk already supplies the scheme scalar-extension calculation, and lem-sfb-ringed-topos-pullback-stalk supplies the formula for restriction to the chart and the pure-tensor normalization. No new colimit lemma, chart-stalk lemma or restatement of the conclusion is necessary. These dependencies were checked to have no path back to this item. The equivalence lemma is a generic tool from sk-i-curve-zero, declared in split_report.tool_uses.

The two semantic searches whose tool sessions disappeared during provider interruption completed successfully: their results are present in searches.jsonl (timestamps 14:17:48Z and 14:17:49Z). They were read from that log and not rerun. Hits are Tilde.toStalk, Tilde.stalkIso and localization/fibre maps, not the algebraic-space comparison. The Loogle results concern spectrum/rankAtStalk tensor statements. LeanSearch returns quasi-coherence predicates and ordinary spectrum localization stalks. The source of Modules/Tilde.lean was read to distinguish its ordinary localization computation from a geometric stalk. No search is recorded as unavailable or as a match.

## Not duplicates

No new nodes were created. Existing lemma lem-sfb-etale-zariski-module-geometric-stalk was reused: its scope is Zariski-to-etale pullback on a scheme, whereas this item additionally identifies the stalk on an arbitrary algebraic space through an etale scheme chart. The general ringed-topos pullback lemma was likewise reused rather than restated.

## Review by NH

I read spaces-properties.tex Tag 05VP, its referenced chart local-ring description Tag 04KF, the general pullback-stalk statement and proof in sites-modules.tex Tag 05V5, and the scheme comparison in etale-cohomology.tex Tag 04HX. I also read descent.tex Tag 03FH for the tensor definition of epsilon pullback and Tag 03DX for the quasi-coherent equivalence. These justify the chosen assembly of existing nodes. There are no new nodes needing a separate source audit.

Step 1 uses the statement of def-trf-algebraic-space that etale pullback is restriction on localized sites, the actual tensor formula in lem-sfb-ringed-topos-pullback-stalk, and the canonical isomorphisms in lem-sfb-space-strict-local-flatness. The given chart and geometric lift satisfy their hypotheses. The map from the algebraic-space geometric local ring to the chart geometric local ring is an isomorphism, not just a flat map. Multiplication by its inverse and the map m to m tensor 1 explicitly cancel scalar extension. No flatness criterion from that node is used.

Step 2 uses the forward tensor-pullback description and inverse restriction description of lem-trf-scheme-zariski-etale-quasi-coherent-equivalence; the module M_U is precisely the module specified by the item. The scheme stalk lemma applies to every Zariski module, so it imposes no extra finiteness assumption. Its strict henselization uses the residue-field embedding from the very same geometric point, and its structural map is the natural germ map. The tensor coefficient change therefore agrees with the A-algebra structures of the item.

Step 3 uses the pure-tensor sentence in the general ringed-topos lemma, the identity on open sections in the equivalence lemma, the germ representatives in the module-stalk definition and pure-tensor generation in the tensor-product definition. I checked those sentences in their statements, rather than using something hidden in their proofs. Applying the same general formula to epsilon_U verifies that the inverse of step 2 sends a germ tensor a ring germ to their product. The remaining argument is elementary equality on generators. The section representatives can be restricted to a common pointed neighbourhood, as in the definition of the geometric stalk; the formula does not choose an unrelated isomorphism.

I tested M=0, M=O_X, U=X when X is a scheme, a non-surjective etale chart containing the chosen lift, an ordinary strictly henselian local ring, arbitrary infinite direct sums, and non-Noetherian bases. The proof uses neither finite generation nor surjectivity of U to X. An empty chart has no geometric lift, so it supplies no counterexample; the assertion is then vacuous. All three steps are below 2000 characters and no sublemma has been hidden by shortening a long step. B1-B10 were checked (no new nodes, exact searches, exact source labels, retained provenance); C1-C8 were checked by reading all cited statements, testing dependency closure and declaring the sole off-unit tool; D1-D5 were checked by retaining an actual assembly and using no new restatements; E1-E7 were checked by the scalar-map and germ calculations above. No statement dispute or source error was found.

## Unfinished work

None in the split. The existing unsplit dependencies remain independent future items. Delivery validation is recorded below after the required server dry run.
