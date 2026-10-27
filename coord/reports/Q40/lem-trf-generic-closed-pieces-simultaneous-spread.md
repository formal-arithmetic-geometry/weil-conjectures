# Q40 stage-1 delivery

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-generic-closed-pieces-simultaneous-spread.json`: item split into six steps using existing nodes; Mathlib searches find no exact match or one-line specialization.
- `citations.json`: one verbatim statement excerpt for every cited node in every proof step.
- `searches.jsonl`: actual results of the five required search-command invocations, including the second semantic phrasing.
- `report.md`: this report. `prepare.py` is sandbox-only preparation code, not a proposed project file.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter record changed. The item's statement, statement dependencies, source, creation history and inherited blueprint ancestry are unchanged.

## Attachments

None. Searching `lean/WeilConjectures/` for the item id, its notions, generic closed pieces and simultaneous spreading found no declaration giving every clause for the supplied family. `AlgebraicGeometry.exists_open_fibre_dense_of_generic_dense`, `AlgebraicGeometry.exists_open_generic_fibre_closed_cover`, and `AlgebraicGeometry.exists_open_closed_subset_fibre_nonempty` supply separate existing tool nodes. They do not state the item. The generic-incidence and geometric-cover declarations instead choose a scalar extension or require geometric irreducibility and do not retain this given family in the original ordinary fibres.

## WANTED

None. All mathematical sources used are present in `literature/stacks-project/more-morphisms.tex`.

## Problems found and corrections

The item was unsplit and the sandbox contained only dispatcher brief markers; there was no prior proof, report or search log to supersede. There is no released repair note for this item. No statement dispute was found, and no statement was weakened or strengthened.

The current blueprint `latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md` now follows contracting correspondences, while this already-created item retains provenance through an earlier 055A/055B/05FH branch. I read the current proof and current unit text, retained the recorded ancestry, and reported the discrepancy in split_report.blueprint rather than inventing a current blueprint passage or altering the unit route. The item's immediate source, Stacks 0554, still contains precisely the subargument being split. The chapter record and unit record were read as instructed; no realization fields apply because this item is not the unit's key node.

A potential gap was avoided by explicitly constructing the homeomorphism from each ordinary fibre of the supplied closed subscheme to its support in the original fibre. No unsupported identification with a field-extended fibre or reduced fibre is used. The proof also does not infer irreducibility of specialized pieces.

## Unfinished work

None at stage 1. This delivery writes no Lean, runs no compiler or build tool, and leaves no newly created obligations.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs. Searches of the whole DAG by 054X, 054Y, 0554 and 055G, and of the blueprint by closed generic cover, dense complements and 0554, led to reuse of the three existing smooth-base-change tools. The parent lower-bound theorem and the reduced-closure model concern component counts and constructing a model, respectively; neither replaces this item's conclusion. General geometric generic-cover and incidence-spread results change the field or the family and are not duplicates of the supplied-family ordinary-fibre statement.

## Review by Q40

I read Stacks 0554, label `lemma-irreducible-components-in-neighbourhood`, including its whole proof from the component closures through the last choice of V. For density I read 054X, `lemma-nowhere-dense-generic-fibre`, including the reduction and generic-flatness argument. For covering I read 054Y, `lemma-cover-generic-fibre-neighbourhood`, its preceding fibre-topology discussion, and its non-Noetherian flat/generalization proof. For nonemptiness I read the image-of-flat-finitely-presented-family argument in 0554 and in 055G, `lemma-geometrically-connected-generic-fibre`; I also read the nearby nonempty-generic-fibre lemma. There are no new-node sources to audit.

Step 1 cites the statements of `def-weil-closed-immersion` and `def-pc-scheme-fibre`. The former explicitly includes a homeomorphism onto a closed subset; the latter explicitly includes the homeomorphism onto the set-theoretic fibre. Restricting the former and composing with the latter gives the displayed support homeomorphism. The equality h_i = f composed with j_i proves the image equality, including surjectivity onto D_i intersect f inverse(t), so no closed-immersion base-change theorem is being silently taken from a definition. Continuity makes D_{i,t} closed. This is a direct argument from the two cited statements.

Step 2 cites `def-weil-irreducible-components` for its actual definition of irreducibility. Incomparability makes C_i minus C_j nonempty; closedness of C_j makes the difference relatively open. If its closure were proper, that closure and C_i intersect C_j would be two proper closed subsets covering C_i. This writes out the density argument. The formula from Step 1 verifies the complement identification point by point. Nothing non-elementary is hidden here.

Step 3 cites `lem-sbc-generic-open-fibre-density`, whose statement concerns an arbitrary finite-type morphism, an open subset, a point with closure equal to the base, and ordinary scheme fibres. Here h_i is finite type by the item's hypothesis, W_ij is open, eta is generic in all of Y, and Step 2 proves exactly the required generic density. The cited conclusion is precisely a base open containing eta with fibre density. The support homeomorphism then sends the specified open subset to the required relative complement and preserves closure. Neither source nor base is assumed reduced, flat, separated or Noetherian.

Step 4 cites `lem-sbc-generic-fibre-closed-cover-spread` and `def-sc-generic-point`. I checked that the first gives an *ambient* open containing its selected point and a covering inclusion over the intersection with that point's closure, for any two closed subsets. Taking the first subset to be the finite union of the D_i, and the second to be empty, exactly meets its hypotheses. Finite type supplies locally finite type and quasi-compactness. The generic-point definition identifies the closure with all Y, so the resulting inclusion applies over the whole chosen open. Pulling it back via p_t proves coverage, also for the empty family. I do not invoke a missing theorem about finite unions spreading.

Step 5 cites `lem-sbc-generic-closed-subset-fibre-nonempty`. Its statement allows exactly the given finite-type f and a closed subset D_i meeting the set-theoretic generic fibre, with no reducedness, Noetherianity or separatedness assumption. Step 1 and nonemptiness of C_i supply this intersection witness. The cited statement gives nonempty set-theoretic intersections in all nearby fibres; the fibre projection lifts the witness to D_{i,t}. No further flatness or open-map theorem is invoked: that argument is inside the existing tool node, not assumed from its definition.

Step 6 uses only a finite intersection of opens and the conclusions already established. Both I and its subset of distinct ordered pairs are finite. Each factor contains eta. For empty I, Step 4 forces empty nearby fibres; for a singleton, the pairwise condition is vacuous and the cover and nonemptiness remain. I also tested the density argument on two intersecting lines, on a single irreducible generic piece which can acquire extra special components, and on a base with nilpotents. The argument claims only dense complements on the final open, so it does not assume that a chosen piece stays irreducible or that source reduction commutes with all fibres.

The three smooth-base-change nodes are generic scheme tools (054X, 054Y and nonempty closed images) already used by the parent's recorded 0554 route. I declared these off-unit citations in split_report.tool_uses with their reasons; I did not write maintainer-owned tool_uses. The existing same-unit nodes do not replace these general tools. Each citation's statement was opened and its literal used part recorded in citations.json; none uses a hidden construction from a cited proof.

I checked delivery-errors B through E against the item. There is no new node to be elementary, duplicate, a relocated clause or an unsearched Mathlib result. Every non-elementary step cites its actual theorem, with the hypotheses checked above; only the explicit topological identifications, irreducibility argument and finite intersection are elementary. The six step texts have lengths 767, 690, 638, 735, 576 and 620 characters, so none crosses the 2000-character hidden-lemma review threshold. All actual Mathlib search hits were read. They concern covers, cofiltered limit existence, dominant maps, preirreducible inverse images under open maps, or topological covering spaces, and do not state the item. The inherited Q55 searches remain provenance from the live item; the five appended Q40 searches are exactly the log produced by msearch.py. No SGA source is used, and no source error requiring a statement change was found.
