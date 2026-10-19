# Worker report

1. Files written:

- `dag/nodes/sec-proetale-coefficients/lem-sfb-topological-stratified-lisse-lattices.json`: split into six proof steps; the statement is preserved verbatim. Zero new nodes and zero new Mathlib leaves.
- `citations.json`: six verbatim statement excerpts, covering every node citation in the proof.
- `report.md`: this report. The search command maintains `searches.jsonl`.

2. Attachments: none. Searches of `WeilConjectures/` in the read-only slopmaster2 checkout for the blueprint id and for lattice/stratification terminology found no declaration stating this result. In particular, `AlgebraicGeometry.WeilGroup.IsLisse.exists_lattice`, `EtaleCohomology/Purity/RealSheaves/LocalSystems.lean:274`, concerns a Weil-group representation and a nonempty open of a curve, chooses its coefficient field, and does not give the required theorem for arbitrary topologically Noetherian schemes with a fixed field. It is not an attachment. No upstream-master sorry is treated as a finished proof.

3. WANTED: none.

4. Problems corrected in the earlier sandbox attempt:

- Its final step stopped at an abstract integral model although the statement requires an embedded lattice. New step 6 constructs the map using the scalar-extension isomorphism, checks its injectivity in finite-free charts, and takes its image.
- The earlier assertion that a pullback lemma also supplies the scalar-extension compatibility exceeded that node's statement. Step 4 now cites the explicit cartesian-coefficient theorem for the comparison with sheaf inverse image and checks the pulled isomorphism using bases and inverse matrices.
- The Noetherian hypothesis on each stratum, total disconnectedness needed for the coefficient comparison, and qcqs hypothesis on the target of the stratification theorem are now justified in the proof text.
- The earlier JSON text contained tab characters from incorrectly escaped TeX. The proof was rewritten with single TeX backslashes and no tab characters.

5. Nothing remains mathematically unfinished at this split level. The six supporting statements already exist; their proofs are separate DAG items. This worker does not change them, the chapter, the unit, the live project, or any Lean file. Only the required `--no-push` dry run is performed; the second reader delivers.

## Not duplicates

No new nodes were created. Searches of the whole DAG for `6.8.13`, `03S0`, and lattice/stratification terms, and `tools/blueprint_refs.py search lattice`, located the existing support lemmas now cited. The blueprint `sk-lem-stratified-lattice` has the standing separated finite-type hypotheses over a positive-characteristic field, so its statement cannot be applied to the arbitrary topologically Noetherian schemes here. `lem-weil-pbc-continuous-lisse-stratified-lattices` supplies constructible integral models on the strata, whereas this item requires lisse embedded lattices; its statement does not suffice. I reused its smaller étale-local and pullback inputs and the already-existing finite-étale descent theorem instead of introducing copies. The item's blueprint ancestor is `thm-sfb-extend-scalars-localization`; the split realizes its essential-surjectivity paragraph through the first paragraph of Bhatt–Scholze Lemma 6.8.13. No unit route is replaced.

## Review by Q124

I read Bhatt–Scholze, *The pro-étale topology for schemes*, Definitions 6.8.1 and 6.8.3, Lemma 6.8.2, Proposition 6.8.4(6), and the first paragraph of Lemma 6.8.13 (printed pages 58–61). The first paragraph first produces an étale-local lattice, then passes to strata with finite étale covers and obtains a lattice there. This is the argument implemented here. The item retains its finite extension, underlying-topology Noetherianity, local finite rank, and condensed coefficient conventions; it adds no normality, finite-type, characteristic, constant-rank, or global-lattice hypothesis. I also read the current rationalization unit and its blueprint essential-surjectivity paragraph. This item is a supporting node, not the unit's key theorem, so no realization fields are changed.

Step 1 uses the actual statement of `lem-weil-pbc-continuous-coefficient-realizations`: the canonical comparison is an isomorphism for totally disconnected coefficients and commutes with continuous ring maps. Clopen ultrametric balls check this hypothesis for both rings. The finite-union argument establishes qcqs from topological Noetherianity. Transport along the two coefficient isomorphisms uses the same actions and finite bases. Evaluation of an internal bilinear action and the sheaf tensor universal property explicitly identify the internal and sectionwise module conventions; no stronger categorical comparison is assumed silently.

Step 2 uses exactly the existence statement of `lem-weil-pbc-continuous-etale-local-lattice`, which I opened. It supplies a qcqs source, an étale surjection, an integral locally finite free module and its rationalization isomorphism. A finite extension with its p-adic norm meets its normed-field and finite-dimensional hypotheses. Its rank and empty-scheme clauses were read, rather than replaced by a constant-positive-rank reduction.

For step 3 I read Stacks `etale-cohomology.tex`, label `lemma-etale-stratified-finite`, Tag 03S0, and the statement of `lem-weil-pbc-etale-stratified-finite`. They assert the finite constructible locally closed stratification and finite étale base changes under qcqs hypotheses on source and target, both available here. The surjectivity argument is written with residue-field fibres. A locally closed stratum is topologically Noetherian because it is an open subspace of a closed subspace, so the descent hypothesis survives.

Step 4 uses `lem-weil-pbc-continuous-locally-free-pullback` only for its stated preservation of local finite freeness. Its statement does not assert a tensor comparison. That comparison is now checked separately: `sk-prop-sfb-cartesian-coefficients`(1) identifies the inverse-image coefficient rings and says the coefficient-module pullback is the lift of sheaf inverse image. Pulling the finite bases and the mutually inverse matrices then verifies the scalar-extension isomorphism on charts. The matrices and their inverses glue because they are pulled from the same maps. No Tate-twist or invertibility-on-the-scheme clause of the cartesian theorem is used: its untwisted assertions explicitly impose no such hypothesis.

Step 5 uses the full hypothesis and conclusion of `lem-weil-pbc-lisse-lattice-finite-etale-descent`, whose statement I read. Every application is on a topologically Noetherian stratum, with the finite extension, finite étale surjection, and lisse integral model already produced. That statement explicitly needs no descent datum on the given model. It concludes the existence of a lisse integral module with a rationalization isomorphism; I do not extract an embedding from its statement.

Step 6 supplies that embedding directly. On a chart the scalar-extension unit is the finite coordinatewise injective map of continuous-function coefficient sheaves. The sheaf uniqueness axiom proves global injectivity. Its image is isomorphic to the lisse model, and the map induced by the inclusion after tensoring is the original rationalization isomorphism. This is an elementary step, not a new lemma restating the item's conclusion. Empty schemes use an empty partition, empty strata are discarded, and zero-rank charts give the zero submodule. These checks also show why varying ranks cause no issue. A one-point scheme with a constant rank-one module has the usual valuation-ring lattice; nothing in the argument demands that all lattices on all strata coincide.

I checked B–E against the revised node and sources: there are no new unsplit statements, hidden clause-nodes, unsupported borrowed proof constructions, or duplicate support nodes. Each non-elementary invocation has its node and a literal witness in `citations.json`. Supporting generic results from other units are declared individually in `split_report.tool_uses`. The specializations use exactly their available hypotheses, and the proof never assumes that the chosen cover lattice itself descends. Fresh command-logged searches used LeanFinder with two phrasings, Loogle, grep with two patterns, and LeanSearch. The returned locally free sheaf definitions, algebraic rank lemmas, modules of locally constant functions, and local-field facts do not state this result. I read the returned locally free sheaf definition and the Mathlib pro-étale coefficient file; neither supplies stratified integral forms. All added search records come directly from this sandbox's command log, including its grep subdirectory, with no invented query.

Dry-run repair: the first server preflight objected to the phrase “the item’s statement” in step 2 (B2). I replaced it by the explicitly named pulled condensed coefficient rings $A_U$ and $B_U$; the mathematical content did not change.

## Second reading by Q124

- Step 1 checked against Bhatt–Scholze Definitions 6.8.1 and 6.8.3, Lemma 6.8.2, and the continuous-coefficient realization and internal-module equivalence nodes; verdict: sound after adding the explicit internal-to-sectionwise module citation.
- Step 2 checked against Bhatt–Scholze Proposition 6.8.4(6) and `lem-weil-pbc-continuous-etale-local-lattice`; the finite-extension, topological-Noetherian, qcqs, variable-rank, and zero-rank hypotheses match; verdict: sound.
- Step 3 checked against Stacks `etale-cohomology.tex`, label `lemma-etale-stratified-finite`, Tag 03S0, and `lem-weil-pbc-etale-stratified-finite`; base-change surjectivity and Noetherianity of locally closed strata were verified; verdict: sound.
- Step 4 checked against `lem-weil-pbc-continuous-locally-free-pullback`, `sk-prop-sfb-cartesian-coefficients`, `def-sfb-module-upper-star`, and `def-sfb-finite-upper-star-monoidal`; the scalar-extension pullback is identified via the strong monoidal inverse image and the matrix check is valid; verdict: sound after adding the two interface citations.
- Step 5 checked against `lem-weil-pbc-lisse-lattice-finite-etale-descent`; its finite-etale, surjective, topologically Noetherian hypotheses and no-descent-datum conclusion are applied exactly; verdict: sound.
- Step 6 checked against the coefficient inclusion on continuous-function sheaves and the finite-free chart definition; injectivity, image identification, empty strata, and rank zero were tested; verdict: sound and elementary.
- New nodes: none were introduced; all six supporting results are existing DAG nodes, and duplicate, Mathlib, and Lean-closed searches found no replacement.

Changes made in this second reading: added the existing internal-module equivalence citation to step 1 and its dependency; added the existing module-pullback and strong-monoidal inverse-image citations to step 4 and its dependencies; added verbatim citation entries for those three nodes; and recorded this audit. No statement, source, or route was changed.
