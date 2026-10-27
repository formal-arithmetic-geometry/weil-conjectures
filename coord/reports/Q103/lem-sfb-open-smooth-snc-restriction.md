# Worker report: lem-sfb-open-smooth-snc-restriction

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-open-smooth-snc-restriction.json`: statement node, now split in eight steps; no Mathlib match for the complete assertion.
- `citations.json`: 21 verbatim statement extracts, one for every node cited by every proof step.
- `searches.jsonl`: five actual Mathlib search invocations for this item, in addition to the older searches preserved in the imported node. The two LeanFinder formulations, LeanSearch, Loogle and source grep were read.

There are **0 new nodes and 0 new Mathlib leaves**. All proof inputs already have nodes. No Lean files were written and no compiler, Lake or build was run. The helper scripts in this sandbox only write the delivery JSON.

## Attachments

None. Searching `lean/WeilConjectures/` for the item id, normal-crossing terminology and SNC produced no declaration stating this item. The Mathlib searches found individual restriction statements, not the combined assertion; the proof reuses the DAG's existing tools rather than duplicating them.

## WANTED

None. The ILO PDF and every Stacks source used here are present in `literature/`.

## Findings and changes

The statement is unchanged mathematically. The imported node omitted statement dependencies that its own text already names, including smoothness, projectivity, regular schemes and the SNC-boundary definition. These are restored, along with definitions of integral and reduced schemes and locally closed immersion. No target, chapter or unit record was changed.

Read the item's source in ILO Expose X: the relative-SNC definition after Theorem 2.1, printed p.149; proof 2.3 Step 1, p.150, and the conclusion of Step 3, p.152. Read also VIII Remark 4.2.2(i), p.118. They explain the return from the projective alteration to the original open and the intersection criterion for SNC. The detailed restriction proof here is marked agent-written: it expands that passage using the existing nodes and the cited Stacks sources, without introducing an alternative alteration route. No SGA source is used.

There is no imported blueprint ancestor: `blueprint_refs.py ancestor` returns None, agreeing with the inherited provenance. Searches of the whole blueprint for `strict normal crossings`, `normal crossing`, `open restriction` and `open subscheme` found no equivalent item. The provenance still identifies the old Step 8 of `lem-sfb-gabber-global-snc-alteration`, serving the alteration reduction in `det-thm-sf-ctf-stability-direct-images` proof (3).

## Reuse and duplicates

No new node was needed. In particular, I opened and reused `lem-pc-open-immersion-smooth-composition`, `lem-weil-pbc-thickening-open-restriction`, `lem-weil-pbc-open-subspace-irreducible-closed-correspondence` and `lem-weil-pbc-scheme-theoretic-union`. I did not create separate nodes asserting integrality of an open, preservation of Cartier generators, or unchanged regular parameters: the explicit arguments are elementary steps from the definitions. A candidate `lem-per-immersion-class-calculus` concerns cohomological cycle classes and was not used for geometric immersion composition. The existing smooth-open lemma gives exactly what is needed without taking any result out of another node's proof.

## Review by Q103

I checked delivery-errors B through E against the actual node statements and the sources, rather than treating the imported dependency list as a proof.

Step 1 uses the **statement** of `def-weil-open-immersion`, specifically the identification with the restricted structure sheaf. The inverse maps on germs are written out, so the local ring comparison does not rely on an unlisted restriction theorem. It applies at every point in the open and does not require density.

Step 2 uses `lem-pc-open-immersion-smooth-composition` for the smooth morphism to the field and for each smooth intersection. Its hypotheses are just an open immersion and a smooth map. Those are supplied by the inclusion and by the item's relative-SNC hypothesis, as stated in `def-trf-smooth-strict-normal-crossings-divisor`. I read Stacks 01VC (morphisms-lemma-open-immersion-smooth) and 01VA (morphisms-lemma-composition-smooth). No smoothness of a quotient, perfection of the field, or global equidimensionality is assumed.

Step 3 uses the finite-dimensional projective-space embedding actually supplied by `def-kun-projective`, the closed-image and immersion definitions in `def-weil-closed-immersion`, and clause (1) of `lem-weil-pbc-thickening-open-restriction`. That last node explicitly applies to any closed immersion, before its additional thickening clauses. I verified the order of the factorization: the open complement W of the closed image of R minus U makes U **closed in W**, so it gives closed followed by open as required. Merely saying that open followed by closed is an immersion would have hidden a theorem. Stacks 01IO defines exactly the factorization used, and 01QO gives the closed restriction.

Step 4 uses clauses (1) and (2) of that same closed-restriction node, not any assertion about arbitrary base change of a radical ideal. Its statement expressly gives equality of the restricted defining ideals on every open of the target open. The displayed fibre-product argument checks `def-pc-fibre-product` directly. In particular, the construction is the open preimage of U in each closed subscheme, not an invalid factorization of an arbitrary morphism based only on set-theoretic image.

Step 5 uses `def-pc-reduced-scheme` in its local-ring form, `def-nagata-effective-cartier-ideal` in its non-zero-divisor generator form, and `def-pc-integral-scheme` in its affine-domain form. The cancellation calculation in A_g explicitly proves that the Cartier generator remains regular on a smaller principal chart; the argument does not assume that an arbitrary ring map preserves non-zero-divisors. The integral case requires the component restriction to be nonempty, and that is the precise qualification in the item. I read Stacks 01J0/01J1, 01OK/01ON, and divisors-lemma-characterize-effective-Cartier-divisor. During this review I corrected its tag to **01WS**, after checking the tag map; 02ON is a different Cartier-divisor lemma and is not cited in the final split.

Step 6 uses the order correspondence expressly stated in `lem-weil-pbc-open-subspace-irreducible-closed-correspondence`, with the definition of components in `def-weil-irreducible-components`. I checked that it is stronger than mere irreducibility of a single open: it includes injectivity and reflection of inclusion, so it proves that surviving components do not coincide. The finite-union irreducibility argument is given explicitly. The scheme-theoretic component union is checked using the ideal-intersection assertion of `lem-weil-pbc-scheme-theoretic-union`, which I opened along with Stacks 0C4H/0C4J. This existing generic tool is declared in `split_report.tool_uses`; it changes no unit route. It is not a citation to a construction that occurs only in that node's proof.

Step 7 identifies intersections by their universal property and uses the **affine minimal-prime-height formulation actually written in** `def-trf-smooth-strict-normal-crossings-divisor`. An affine open of U is the same affine scheme when viewed as an open of R, and its ideal sections are unchanged by step 4. Thus the height statement is inherited on exactly the same ring; no uncited dimension-of-open or catenary dimension formula is needed. The parameter assertion uses `def-weil-pbc-regular-system-of-parameters`: the same local ring, maximal ideal, dimension and list of parameters are retained. The subset J may still be any subset of the original labels, including labels whose restricted component is empty.

Step 8 checks **all** clauses in `def-trf-strict-normal-crossings-boundary`, including regularity of every intersection and its local-ring dimension formula, not just smoothness. `def-weil-regular-scheme` includes the locally-Noetherian plus regular-stalk characterization. I deliberately cited `pqf-def-locnoeth` for its explicit sentence saying that opens of locally Noetherian schemes are locally Noetherian; the citation quotation includes that sentence, so this is not an unsupported theorem inferred merely from the name of a definition node. I read Stacks 01OW (properties-lemma-locally-Noetherian), 02IT (properties-lemma-characterize-regular) and 02IU (properties-lemma-locally-regular). Noetherianity is inherited from the given regular schemes, not inferred from an assertion about arbitrary stalks alone.

For the small cases I checked U empty, E empty, a nonempty open missing one component, and J empty. In the first case there are no points or surviving components; in the second the unit Cartier ideal is generated by 1; missing components are discarded without changing the other labels; J empty gives U and codimension zero. Two crossing coordinate axes in the affine plane give the same local parameter equations after removing any open complement. No statement dispute was found. No new statement was introduced, so there is no new-node small-case or shared-tag duplicate obligation left over. Every proof step is under 2000 characters, with no long-step extraction needed.

The server-only `review_split` check passed before this report was written. The initial repair dry run passed at 12cf461264f. The final dry run and push are performed after the repair below is finalized.

## Unfinished work

None in this stage-1 split. Formal Lean statements and proofs remain outside this worker's authorized stage.


## Repair of the promotion return — 2026-10-23

The return names the previously approved head `1311ae75328` and reports that its side completion had not been promoted into the live DAG read by the queue. I retained the delivered sandbox proof, report, citations and five logged searches; I did not treat the side completion as a live completion. The live item is currently `unsplit` with an empty proof. Its statement, source, creation record, chapter, unit and blueprint provenance agree exactly with the retained item. Its five original searches remain the initial five entries of the retained record. The sandbox additionally supplies the seven definition dependencies missing from the live list, the eight proof steps, their dependency list, proof provenance, split report and the five actual logged searches. The delivery tool rebuilds this overlay on current `origin/sheaf-dag` while preserving current maintainer-owned fields; the initial repair dry run passed at `12cf461264f`.

I re-read all 13 live statement dependencies and all 17 distinct proof dependencies, including every node behind the 21 step citations, rather than assuming the returned head's inputs remained valid. Every quotation in `citations.json` is still a verbatim substring of the current node's statement. In particular, the smooth-open composition statement still gives step 2; the closed-restriction statement still gives both clauses (1) and (2) used in steps 3 and 4; the irreducible-closed correspondence still reflects inclusion for step 6; and the SNC definitions still give the affine minimal-prime height condition for step 7 and the regular-intersection local dimension formula for step 8. No citation replacement or new node is required. The retained search results were read from `searches.jsonl`; the statement and search questions have not changed, so no searches were repeated.

For this repair I reopened ILO X pp.149–152 and VIII p.118, and Stacks 01QO, 01WS, 02IT and 02IU in their local sources. The current blueprint's direct-image proof (3) remains the compactification/open-immersion route; this child supplies the geometric open restriction used by its alteration inputs and changes no unit or chapter route. The live SNC-boundary statement explicitly requires a radical ideal, so I expanded step 8 to verify that clause on the same open sections: the ideal is the original ideal on each open of U, hence radical by the original boundary hypothesis. This is an elementary application of the already cited boundary definition and step 4, with no added assumption. All eight steps remain below 2000 characters. The finite component family, the nonempty qualification for an integral restricted component, and the three empty cases are unchanged. Searching the live project for the item tag and normal-crossing terminology still gives no finished declaration for the full assertion. This repairs the sole promotion/rebase point; it is not an unchanged re-push.
