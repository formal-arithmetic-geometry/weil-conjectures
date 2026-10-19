# Q153: lem-coef-interval-equivalence-cocartesian

## Files written

- dag/nodes/sec-six-functors/lem-coef-interval-equivalence-cocartesian.json — statement, split into seven steps; no Mathlib match.
- citations.json — verbatim statement quotations for every step citation.
- searches.jsonl — actual search-command log. write_split.py is sandbox scratch, not part of the delivery.

No new nodes and no Mathlib leaves are created. The item's statement, source and statement dependencies are unchanged. No unit realization is due: this is an auxiliary descendant of prop-coef-integral-exceptional-adjoint, not the key statement of its unit.

## Attachments

None. A search of /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the item tag and cocartesian/Cocartesian returned no declaration; there is no exact project proof to attach. Master remains reference only.

## Sources and WANTED

WANTED: Lurie, Higher Algebra, Lemma B.2.4 proof (a), printed pp.1483-1484, for lem-coef-interval-equivalence-cocartesian; the cited online PDF is not archived in literature/.
WANTED: Lurie, Higher Topos Theory, Proposition 2.4.4.3 (opposite-category form) and Proposition 1.2.7.3, for lem-coef-interval-equivalence-cocartesian; not archived in literature/.

I read HA B.2.4(a) in the author's online PDF. It asserts the invariance used by the parent, without expanding its proof; it does not supply an extra hypothesis or a new proof node. I read HTT 2.4.4.3: its cartesian mapping-square criterion dualizes to the existing cocartesian criterion. I also read HTT 1.2.7.3 and the ancestor's main-20261015 statement and proof in sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.md and .proof.md. The ancestor's second paragraph is the derived coefficient mapping-complex adjunction; the item is an auxiliary invariant within its existing marked-model ancestry. The unit and chapter records were read but not changed. This expansion is authored here, so proof_origin.by is agent. No SGA source was used.

## Mathlib and duplication searches

The existing item's recorded searches were retained. This session additionally ran the search command with two leanfinder phrasings, Loogle SSet.Quasicategory, grep of AlgebraicTopology, and LeanSearch. All completed successfully; the semantic results concern ordinary categories with Hom sets or the inner-horn definition of a quasicategory. I read FiberedCategory/Cocartesian.lean:43-78 and Quasicategory/InnerFibration.lean:29-97. These do not prove equivalence invariance for quasicategories. Exact queries and returned names are in the node and searches.jsonl.

I searched the entire DAG and blueprint index for cocartesian and equivalence, and read the statements of the mapping criterion, mapping composition, Hom bifunctor, Joyal equivalence test, invertible interval, and enhanced cone calculus nodes. The blueprint search gives no imported cocartesian statement. The existing item and general mapping criterion are distinct; the latter assumes an arbitrary inner fibration and characterizes an individual edge by mapping squares, with no equivalence of total categories. No new node is needed. Therefore there are no new/existing same-tag pairs needing a Not duplicates entry.

## Corrections and unfinished work

The imported statement is correct as written; no STATEMENT-DISPUTED is raised. The original node had no proof. Its implicit categorical-equivalence-to-coherent-inverse conversion and its extension from image targets to all targets are now explicit. A temporary absence of the item during the first shared-snapshot read resolved on refresh. The first delivery probe, before a sandbox item existed, exited with the expected no-node-files diagnostic; no delivery invocation was left running.

The split is complete. The underlying cited nodes retain their existing states and future work; this delivery does not claim those dependencies are Lean-proved.

## Review by Q153

I checked delivery-errors B through E against the written node and the cited statements. No definitions or statement-only children were added, avoiding both duplicate nodes and restatements of clauses. The statement introduces E, F, p, q and v with the precise hypotheses required by the general criterion. In particular neither projection is assumed cocartesian, and v is not assumed a fibration. I did not require its quasi-inverse to commute strictly with the base.

For step 1 I opened lem-coef-joyal-functor-equivalence-test and checked its equivalence with the ordinary homotopy-category precomposition test, including sufficiently large universes. With C=E essential surjectivity produces w; with C=F full faithfulness lifts the second isomorphism and its inverse. I opened lem-coef-quasicategory-invertible-interval: it supplies an actual J-path for an isomorphism in hD, applied with D the two functor quasicategories. The inverse triangles inside J produce the coherent equivalences required by def-cbc-enhanced-diagrams-cones. Thus the statement of each node says exactly what step 1 takes from it, without treating a model weak equivalence as a strict inverse over the interval.

For step 2 I checked that lem-cbc-enhanced-functor-cone-calculus explicitly says both that functor equivalences induce mapping-space equivalences and that coherent equivalences are detected at vertices. These give full faithfulness and the edges vwz to z. This is a generic tool from another unit, declared in split_report.tool_uses, not a different coefficient route.

For step 3 I read the exact right-pinched mapping-space formula in def-cbc-enhanced-diagrams-cones. The monotone simplex into [1] is unique for i<=j and absent otherwise; the whole initial face is constant, as required by that definition. This is genuinely elementary. It also proves emptiness of mapping spaces with decreasing base label, rather than assuming a homotopy fiber models a strict fiber.

For step 4 I opened lem-coef-infinity-cocartesian-mapping-criterion and verified the inner-fibration, quasicategory and fixed-universe hypotheses for both p and q. Its statement explicitly allows the absence of any other cocartesian lifts. I calculated its specified path pullback: over two points it is Map(x,t); when the bottom left corner is empty it is empty. The upper left corner is empty in the latter case by step 3. Thus all missing-fiber and empty-mapping-space cases really are covered. This reduction is a short application of the existing criterion, not a hidden child lemma.

For step 5 I opened lem-coef-infinity-hom-bifunctor-functoriality and checked that it supplies coherent naturality for the actual maps of right-pinched mapping spaces under v. It supplies precisely the square with precomposition by u and v(u), not merely an equality on component sets. Full faithfulness from step 2 makes its vertical arrows equivalences. The written homotopy-group argument proves the two-out-of-three comparison, with basepoint-change paths accounted for; it uses no unquoted homotopy-pullback-invariance theorem.

For step 6 I read all clauses of lem-coef-infinity-mapping-composition. Its inverse-triangle/component characterization and unit/associativity homotopies show explicitly that postcomposition by e' is inverse to postcomposition by e, and that this comparison commutes up to homotopy with precomposition. I read lem-cbc-simplicial-homotopy-equivalence-weak, whose hypotheses are precisely the two displayed inverse homotopies; it has no nonemptiness hypothesis. Its generic use from another unit is declared. Applying q to inverse triangles shows that q(e) must be an identity of [1], so the comparison respects exactly the required target label. Step 7 only assembles the two directions already proved and is elementary. Each citation has a verbatim statement quotation in citations.json, with the complete statement used when several separate clauses are needed.

I tested identity v, an equivalence with extra isomorphic target objects, empty E and F, either missing endpoint fiber, all three possible base-edge labels 00, 01, 11, and empty Map spaces. If E is empty, categorical equivalence forces F to be empty, and there are no edges to test. For an edge above 01, only targets above 1 require a mapping equivalence; targets above 0 contribute an empty comparison. For an edge above 11 the same applies; above 00 both target labels are tested. Thus the argument does not silently restrict to edges over 01. The statement is unchanged in all cases. I also checked the transitive dependency closure of every prospective citation and found no return path to the item. Every non-elementary step is under 1100 characters; none exceeds the human's 2000-character inspection threshold.

## Continuation after interruption

The interrupted dry-run process was no longer running. The resumed dry run completed and reported B4 in step 5: the matrix row separator directly adjoined the next TeX command. I inserted a newline after each row separator, preserving the formula and argument. I reread all ten statement/proof dependencies and verified all twelve citation entries against their current statements; all quotations remain verbatim. The seven proof steps remain below 1100 characters, and the source statement and hypotheses remain unchanged. No searches were repeated or added.
