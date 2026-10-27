# Stage-1 report: lem-trf-finite-residue-tower-local-geometry

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-finite-residue-tower-local-geometry.json`: item, statement; split in seven steps with every dependency named. Mathlib verdict: no direct match for the complete tower statement; the individual Noetherian and localization ingredients already have Mathlib-leaf nodes and are reused.
- `citations.json`: fifteen verbatim statement quotations, one for every use in every proof step.
- `report.md`: this report.
- `searches.jsonl`: the required search command's log, read and incorporated into the item without inventing or editing searches.

No new nodes; zero new Mathlib leaves. No Lean files, compiler invocations, library writes or direct git commands.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag, finite-residue towers, residue-field closedness and Noetherian local geometry found no declaration stating every clause under these hypotheses. `WeilConjectures/ClosedPoints.lean` and `PointCount.lean` treat finite underlying residue fields or the forward closed-to-finite implication; these are not the full present assertion for an arbitrary field and finite-dimensional extensions. They were not treated as attachments.

## WANTED

None. All sources used are present under `literature/stacks-project/`.

## Corrections and dependency audit

The statement is unchanged, including both actual structural residue maps and the absence of quasi-compactness, separatedness, algebraic closedness and etaleness. The empty imported proof is replaced with an argument. Statement dependencies are retained; proof dependencies are exactly the union of the steps' uses.

The report does not mistake closedness in a fibre for ambient closedness. Step 3 uses the one-point spectrum of a field; Step 4 explicitly uses the closed inverse-image subspace. Both use the existing finite-residue fibre lemma, whose statement is limited to fibre closedness. I deliberately did not use `lem-kun-closed-point-field` on the whole of C or D: its statement assumes finite type, while this item assumes only locally finite type. Nor did I cite a locally-Noetherian definition as a theorem asserting that every affine open has Noetherian sections; Step 5 chooses members of the cover that definition actually supplies.

The item is an auxiliary tool extracted from the historical semistable branch below `lem-trf-local-term-locality`, as its inherited blueprint provenance records. I read the current main-20261015 unit and locality proof as well as the live parent `lem-trf-etale-completed-local-ring-iso`: the current blueprint uses contracting correspondences, whereas this already-created auxiliary branch remains in the live DAG. This delivery does not replace a unit step or change a chapter route. Its seven steps realize the local-geometry preparation that the parent uses at its Step 4.

## Not duplicates

No new nodes are created. Whole-DAG source/tag and keyword searches, and whole-blueprint searches for residue fields, Noetherianity, closed points, finite residues, localization and the pertinent source labels found the existing ingredients used here. In particular:

- Reuse `lem-trf-finite-residue-point-closed-in-fibre` for Tag 01TE, rather than making a second closedness node.
- Reuse `pqf-lem-locnoeth-lft` (Tag 01T6; Mathlib leaf) twice.
- Reuse `lem-weil-pbc-affine-open-stalk-localization` for Tag 01HV and actual germ maps.
- Reuse `lem-weil-pbc-localization-noetherian` for Tag 00FN.
- `lem-weil-pbc-finite-type-over-noetherian` has a global finite-type hypothesis; the locally finite-type statement needed here is already `pqf-lem-locnoeth-lft`.

Thus no new node restates the item, one of its clauses, or an elementary piece of the assembly.

## Review by Q84

I read Morphisms `lemma-algebraic-residue-field-extension-closed-point-fibre` (Tag 01TE), including both conclusions and its proof; `lemma-finite-type-noetherian` (01T6); Schemes `lemma-fibre-topological` (01K1) and `lemma-spec-sheaves` (01HV), especially (1) and (6); Properties `definition-noetherian` (01OV); and Algebra `lemma-Noetherian-permanence` (00FN) including its localization argument. The tags were checked against `literature/stacks-project/tags/tags`. No new-node source is needed because no new nodes are proposed.

For Step 1 I opened `def-weil-field`, `def-weil-pbc-noetherian-ring`, `def-weil-affine-spectrum`, and `pqf-def-locnoeth`. The first two give the inverse axiom and the finite-generation criterion, so the displayed argument that a field has just the zero and unit ideals proves Noetherianity. The spectrum definition supplies its section ring; the one-member affine cover then satisfies exactly the locally Noetherian definition. This is an elementary proof, not an unreferenced permanence theorem.

For Step 2 I opened `pqf-lem-locnoeth-lft`: it explicitly assumes a locally Noetherian target and a locally finite-type map, and explicitly concludes local Noetherianity of its source. Step 1 supplies the first target, and the first application supplies the second. The hypotheses on p and e are in the item. I checked that neither application tacitly asks for a finite cover or a globally Noetherian scheme.

For Step 3 I opened `def-weil-affine-spectrum`, `def-weil-residue-field`, `lem-trf-finite-residue-point-closed-in-fibre` and `def-pc-scheme-fibre`. The spectrum and residue definitions identify the unique base point and its actual structural field map with the supplied k-extension. The fibre lemma assumes local finite type and a finite-dimensional residue extension, both present, and concludes closedness only in the fibre. The fibre definition explicitly states a homeomorphism onto the inverse-image subspace. Because the inverse image here is all of C, the resulting closed singleton is ambiently closed. No arbitrary abstract field isomorphism is used to replace the supplied map.

For Step 4 the same fibre lemma applies to e using exactly the second finite extension, and the fibre definition gives exactly the subspace topology used. Step 3 has already made x closed. The inverse image under the continuous map e is therefore closed; the intersection formula in the step proves ambient closedness of y. This topology argument needs no closed-immersion lemma and is written out rather than assigned a new node. It uses the statements of the cited nodes, not an unexported argument in their proofs.

For Step 5 I reopened `pqf-def-locnoeth`: it gives an affine cover with Noetherian section rings. Selecting one covering member through each point is all the step does. This avoids silently using the stronger all-affine-opens characterization. U and V need not be compatible under e, which the item's conclusion does not demand.

For Step 6 I read the full statement of `lem-weil-pbc-affine-open-stalk-localization`. Its clause (c) is exactly the localization of the germ map at the corresponding prime, including the fraction formula and the induced isomorphism. The opens selected in Step 5 are affine and contain the points, satisfying all hypotheses. The formula shows that the isomorphisms here concern the actual stalks and actual germs, rather than unspecified abstract isomorphisms. I also read the matched Mathlib declaration `IsAffineOpen.isLocalization_stalk` at `AffineScheme.lean:834` and the separate local-Noetherian theorem at `Noetherian.lean:239`; neither by itself states the whole item.

For Step 7 I opened `lem-weil-pbc-localization-noetherian`, whose statement supplies the Noetherian conclusion for a ring with the three localization properties. Step 6 supplies those properties for each actual germ map and Step 5 supplies Noetherian source rings. I opened `def-weil-pbc-localization-at-prime`, which explicitly says a prime localization is local with maximal ideal pR_p. The isomorphisms from Step 6 then give locality of the two stalks. Thus both Noetherianity and locality have their own stated justifications.

I checked B1--B10, C1--C8, D1--D5 and E1--E7 of `coord/delivery-errors.md` against the written item and the open sources. No statement was disputed or corrected; there are no new-node statement-only, TeX, search-provenance or duplicate issues. Each quoted citation is an exact substring of the relevant statement. Existing off-unit proof ingredients are definitions or Mathlib leaves, so no new route approval is needed. The fibre-closedness lemma is in the item's own unit. No proof step exceeds 2000 characters (the longest is 601); none hides a further lemma.

For small cases I checked identity maps of Spec k, nontrivial finite field extensions (including purely inseparable ones), nonclosed generic points of positive-dimensional affine schemes, nonreduced finite-type schemes, and an infinite disjoint union of affine finite-type k-schemes. Finite residue extensions allow inseparability and nilpotents without affecting closedness or the Noetherian local models. A generic point with transcendental residue extension does not satisfy the hypotheses. The infinite-disjoint-union case confirms that the proof must and does use only local Noetherianity. Empty schemes contain no chosen y, so the quantified assertion has no instance there. Overlapping affine opens are never assumed affine.

The actual Mathlib search results were read from the command output and its log. In particular `isClosed_singleton_iff_locallyOfFiniteType` at `Morphisms/Finite.lean:221` has a Jacobson hypothesis and a local-finite-type hypothesis on the residue-point map, not directly the finite-residue tower hypothesis. Deriving that map's hypothesis is a further argument; I kept the existing Stacks fibre route instead of declaring this whole item a one-line Mathlib specialization. All successful calls and their exact queries are appended to the item's search history, retaining the earlier worker's searches.

## Unfinished work

None in this stage-1 split. This is a natural-language proof delivery; it asserts no new Lean proof or compiler result. The first server dry run rejected the Step 7 localization quotation as too short; I expanded it to the whole statement, including its hypotheses, and reran the check. The spectrum quotation in Step 1 also now quotes the global-sections clause used there. Final server validation and delivery follow this repair.
