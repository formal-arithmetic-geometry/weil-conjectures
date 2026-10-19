## Files written

- `dag/nodes/sec-nagata-compactification/det-nagata-refinement-common-dense.json`: split statement, seven proof steps; no whole-item Mathlib match.
- No new nodes and no new Mathlib leaves. Existing Mathlib leaves are cited rather than duplicated.
- `citations.json`: every step/cited-node pair, with its verbatim statement. `searches.jsonl` records the seven actual search calls.

## Attachments

No whole-item attachment. The pairwise portion has closed project declarations in `WeilConjectures/Compactification/CommonRefinement.lean`: `AlgebraicGeometry.Compactification.inf` (line 94), `AlgebraicGeometry.Compactification.isPullback_infFst` (138), `AlgebraicGeometry.Compactification.isPullback_infSnd` (146), `AlgebraicGeometry.Compactification.isSchemeTheoreticallyDominant_inf_i` (155), and `AlgebraicGeometry.Compactification.exists_common_refinement_isSchemeTheoreticallyDominant` (163). I read their definitions and statements and checked the five names in `local/sorry_map_slopmaster2_7d675a26.jsonl.gz`: `s=false`, `ts=false` for each. The project refinement structure only records the two commuting equations; the two pullback theorems supply the stronger boundary condition of this item. No declaration for the finite nonempty dense-family conclusion was found, so the pairwise theorem alone is not an attachment of this item.

## WANTED

None. The current blueprint and required Stacks sources are present locally.

## Audit findings and changes

The main-20261015 node file states the conclusion, without a proof section. Its current unit `_section.md` likewise states the common-dense-refinement result without proof steps; the DAG unit record retains the older graph-construction step (i), which is the route followed here. The imported JSON supplies a proposed proof. I read that proof against unit `sk-prop-nagata-sketch-comp-category`, step (i), and the local Stacks text. The split keeps its graph/closure/finite-induction route and the exact statement.

The imported proof cites quasi-compactness but omits nodes for the closed graph, properness under base change/composition, and a closed subscheme of a proper scheme. Those citations are now explicit. For quasi-compactness of the graph immersion I apply the open quasi-compactness lemma only to the open map `j_1`, base-change that map, and write the closed-subspace argument. In particular I do not silently identify the old finite-type cancellation node with its updated locally-finite-type Lean declaration.

The imported inverse-image argument says scheme images commute with open restriction; its existing cited node's printed statement also assumes quasi-separatedness, although its blueprint_update drops that unnecessary hypothesis. I avoid needing either version: on each open product chart the graph is closed, while its inclusion in the closure is scheme-theoretically dense. Its closed ideal is therefore zero. This proves equality as subschemes, including nilpotents, rather than merely equality of point sets.

The singleton case in the induction is written using the pair `(c_1,c_1)`. Taking `c_1` itself would not suffice when it is not dense. The induction explicitly computes the inverse image for a composite refinement. The target statement is unchanged; no statement dispute arose.

`def-nagata-scheme-theoretic-image` has an erroneous old phrase “largest closed subscheme”; its current blueprint_update correctly defines the image by the largest quasi-coherent kernel ideal (equivalently the smallest closed subscheme). I read and use that update, solely for the existence of the closed image factor, not the erroneous extremum. This existing dependency was not edited. Likewise the compactification and density definitions are read with their current updates: an input open immersion need not include quasi-compactness in its data, so the proof derives it; for the resulting quasi-compact open the sheaf-injectivity description of density applies.

## Existing-node and blueprint search

I searched all DAG statements and the project source for compactification/common refinement, graphs of separated morphisms, proper base change/composition, closed immersion base change, quasi-compact base change and scheme images. I opened each cited node. `tools/blueprint_refs.py ancestor det-nagata-refinement-common-dense` gives the item itself. Blueprint searches included `refinement`, `closed immersion`, `common dense`, `refinement-common`, `scheme-theoretic image restriction open`, and `immersion open scheme image`. The category proposition uses a weaker notion of refinement for arbitrary nondense inputs and has other clauses; it is not substituted for this item and is not listed as same_as. No other node states exactly this whole item. The generic tools needed by the proof already exist, so no new node requires a duplicate exception.

The logged Mathlib queries were tried with two semantic phrasings, Loogle for both Compactification and toImage, and grep for both the whole theorem and the image machinery. The Compactification identifier was unknown to the Loogle service, and grep found no compactification/common-refinement statement in Mathlib. The second searches did find image, proper projection and immersion machinery; I read the relevant source sections in `IdealSheaf/Subscheme.lean`, `Morphisms/Immersion.lean`, and `Morphisms/SchemeTheoreticallyDominant.lean`. Those are ingredients represented by existing nodes, not a whole-item match. No unavailable search was reported as absence.

## Unfinished work

None in this one-level split. No Lean was written and no compiler, Lake or build tool was run. No delivery was pushed. The sandbox is for the required independent second reading.

## Review by Q53

I read the current blueprint `main-20261015/.../det-nagata-refinement-common-dense.md`, its enclosing unit and chapter, and Stacks `morphisms.tex` Tags 01W3, 01W4, 01W5, 01RG, 01R7, 01RE and `schemes.tex` Tags 01JY, 01K5, 03GI. These sources allow arbitrary schemes; they impose no noetherian, reducedness, finite-presentation or flat-base-change assumption here. The finite-type and separated hypotheses of the item supply the quasi-compactness hypotheses actually used. There are no new-node statements to check against sources.

For Step 1 I opened `lem-weil-pbc-proper-base-change` and `lem-weil-pbc-proper-composition`: they state exactly the two permanence properties applied to `p_2` and `p_1`. The separatedness conclusion is part of the definition `def-weil-proper-morphism`, not an uncited theorem about proper maps. The product's structure map is the projection followed by `p_1`.

For Step 2, `lem-weil-pbc-open-immersion-base-change` gives the open product chart. I checked the universal property in `def-pc-fibre-product`: the explicit square pulls back the diagonal of `p_2`, not a diagonal over the wrong base. `def-weil-proper-morphism` states closedness of that diagonal, and `lem-weil-pbc-closed-immersion-base-change` states closedness of its pullback. `def-weil-closed-immersion` defines an immersion as closed then open, exactly the factorization here. Exchanging the indices gives the second graph by the same displayed construction; it needs separated `p_1`, which is available.

For Step 3, `lemma-nagata-open-immersion-qc-over-separated-target` has the finite-type composite and separated target hypotheses, both checked for `j_1,p_1,f`. `lem-pc-quasi-compact-base-change` gives quasi-compactness of the open product chart's inclusion for arbitrary base change. `def-weil-finite-type-morphism` defines quasi-compactness by inverse images of affine opens, and `def-weil-closed-immersion` provides the closed topological embedding of the graph. The remaining closed-in-quasi-compact argument is written out using a finite subcover, so it is an elementary combination of precisely those statements.

For Step 4, `lemma-nagata-immersion-open-in-scheme-image` explicitly gives all three properties of the factor map: quasi-compact, open, and scheme-theoretically dense. No conclusion is taken from its proof. `def-nagata-scheme-theoretic-image`, interpreted by its current update, gives the closed image inclusion. Clause (c) of `lem-weil-pbc-closed-immersion-proper` gives properness of its composite with the proper structure map of the product. The fibre product definition gives the projection equations, while `def-nagata-compactification` and `def-nagata-dense-compactification` identify the resulting data as the claimed compactification. This does not require quasi-separatedness of the ambient scheme for the image-factor lemma's printed statement.

For Step 5, the only cited inputs are the affine closed-immersion characterization and the injective sheaf map in `def-nagata-scheme-theoretically-dense-open`. I checked that the whole copy of X lies in each open product chart: its composite with the appropriate projection is `j_k`. The graph factor through the closed image is therefore a map of closed subschemes on that chart. The local quotient `A/I` to `A/J` is surjective because `I` is contained in `J`; the zero-kernel conclusion follows from restricting the already known dense-open injection. This is an elementary restriction and quotient-ideal argument; it invokes no scheme-image base-change theorem and no inference from mere point containment to scheme factorization.

For Step 6 I reread all three conditions in `det-nagata-definition-refinement`. The proof supplies the over-S equation, the equality on X, and equality of inverse-image open subschemes. The second application of the open quasi-compactness lemma checks both inputs, including the version where the updated compactification definition only assumes open. For Step 7 the same refinement definition explicitly states its composition equations; I also wrote the inverse-image equation in the proof. The positive induction changes only the compactifications, so the fixed `f`, finite type, separatedness and qcqs S hypotheses remain available every time Steps 1–6 are used.

I tested the argument with X empty (its scheme image is empty and is still a proper dense compactification of the empty morphism), with one input having a disjoint proper component, with the singleton family not dense, and with nilpotents on the boundary. The empty case uses the zero sheaf and causes no exception; disjoint components are removed by the image; the singleton is densified before induction; and the ideal-injection step rules out residual nilpotent thickening of X. An empty family is deliberately not claimed. These checks repaired the imported proof's omitted permanence citations and made the scheme-structure equality and induction explicit. The target's statement, chapter, unit and import flags were preserved.

## Earlier second reading (a previous round; superseded)

- Step 1 was checked against the current blueprint statement and Stacks Morphisms Tags 01W3, 01W4 and 01W1: the two properness permanence applications and the separatedness consequence have the required hypotheses and conclusions.
- Step 2 was checked against Stacks Schemes Tag 01JY, Morphisms Tag 01QR and the fibre-product definition: the displayed graph square is the base change of the diagonal of $p_2$, and the exchanged-index graph has the same construction.
- Step 3 was checked against the current blueprint update of `lemma-nagata-open-immersion-qc-over-separated-target`, Stacks Tags 01K5 and 03GI, and the finite-type, proper and closed-immersion definitions: the proof now supplies quasi-compactness of the composite and quasi-separatedness of each proper target before applying the lemma.
- Step 4 was checked against Stacks Tags 01RG, 01R7 and 01W5 and the current scheme-theoretic-image update: the open dense factor, closed image inclusion, proper structure map, and compactification equations are all stated by cited nodes.
- Step 5 was checked against the closed-immersion affine characterization and the injectivity definition of scheme-theoretic density: factoring the closed graph through the inverse-image closed subscheme gives an ideal inclusion, and the restricted dense-open injection forces that ideal to vanish, including nilpotents.
- Step 6 was checked against the refinement definition and the current quasi-compactness lemma update: the two projection maps satisfy all three refinement conditions, and the input open maps meet the updated lemma hypotheses by the explicitly repeated proper/separated/quasi-separated argument.
- Step 7 was checked against the refinement composition equations: the positive finite induction has a valid singleton base, computes the inverse-image equation for composites, and makes no empty-family claim.
- There were no new nodes to review; all cited nodes were opened and their quoted statements were regenerated verbatim in `citations.json`.

Changes made in this second reading:

- Repaired Steps 3 and 6 to follow the current blueprint update of the quasi-compact open-immersion lemma, adding the proper, finite-type, closed-immersion, and quasi-separated definition citations needed for its hypotheses.
- Removed the uncited Tag 01RE mention from the elementary Step 5 source field; its argument is now tied directly to the cited density definition.
- Regenerated `citations.json` and `proof_deps` after the citation repairs.

- Final E5 repair: Step 2 now proves the graph pullback for each $k$ with $\ell=3-k$, using the full test-scheme universal property; it no longer defers the second graph to an exchanged-index argument. Steps 3 and 6 spell out that the closed diagonal has affine inverse images $\operatorname{Spec}(A/I)$, verifying quasi-compactness directly.
- Independent second-reader searches used the broader grep `Compactification|IsCofiltered.*compact|exists_common_refinement` and the logged finite-collection semantic query. The grep returns topological compactifications; no exact whole-item declaration was found. No new node was introduced.
- Validation before this final wording repair: the required dry run printed `OK (not pushed) deliver/Q53/det-nagata-refinement-common-dense at 73a3f4a3e6: preflight passed`. The final files are validated again below by the delivery command.

## Second reading by Q53

- Item statement: checked against blueprint `main-20261015` node `det-nagata-refinement-common-dense` and its unit record; hypotheses $S$ qcqs, $f$ separated finite type, two compactifications, scheme-theoretic image, proper dense compactification, both refinement equations, and the finite nonempty conclusion all agree. Verdict: unchanged.
- Step 1: checked against the statements of `lem-weil-pbc-proper-base-change`, `lem-weil-pbc-proper-composition`, and `def-weil-proper-morphism`; the two projection/composition applications and separatedness conclusion have the required hypotheses. Verdict: sound.
- Step 2: checked against `lem-weil-pbc-open-immersion-base-change`, `def-pc-fibre-product`, `def-weil-proper-morphism`, `lem-weil-pbc-closed-immersion-base-change`, and `def-weil-closed-immersion`; the displayed test-scheme pullback proves both graph closed immersions and the immersion factorization. Verdict: sound.
- Step 3: checked against the current blueprint lemma `lemma-nagata-open-immersion-qc-over-separated-target`, the finite-type, compactification, proper, closed-immersion, quasi-separated, and base-change statements; the composite and diagonal hypotheses are explicitly established and the closed-subspace finite-subcover argument is elementary. Verdict: sound.
- Step 4: checked against `lemma-nagata-immersion-open-in-scheme-image`, the scheme-image definition, closed-immersion properness, fibre-product, compactification, and dense-compactification statements; the cited image definition supplies only the closed factor needed here, while the updated blueprint kernel interpretation supplies the intended meaning. Verdict: sound.
- Step 5: checked against the affine closed-immersion characterization and `def-nagata-scheme-theoretically-dense-open`; factorization gives $I\subseteq J$, and restricting the injective structure-sheaf map forces the closed ideal to vanish, including nilpotents. Verdict: sound.
- Step 6: checked against `det-nagata-definition-refinement` and the same updated quasi-compactness route as Step 3; all three refinement conditions and the $S$-morphism condition are supplied. Verdict: sound.
- Step 7: checked against the composition clauses in `det-nagata-definition-refinement`; the singleton base uses $(c_1,c_1)$, the positive induction composes inverse-image equalities, and no empty family is asserted. Verdict: sound.
- New nodes: none; there were no new node statements or Mathlib leaves to review. Existing-node searches covered compactification/common-refinement, graph, properness, scheme image, and refinement terms; no duplicate node was introduced.
- Small cases: checked the empty scheme, a singleton family whose input is not dense, a compactification with an extra proper component, and nilpotent boundary structure; each is covered by the stated image and ideal arguments. No statement dispute found.

Changes made in this second reading: no further mathematical or structural repair was needed; appended this per-step audit, recorded that the existing imported scheme-image node has the old “largest closed subscheme” wording while the current blueprint defines the kernel-ideal construction, and retained the proof's explicit kernel-only use. The sandbox's required dry run had already reported `OK (not pushed) deliver/Q53/det-nagata-refinement-common-dense at 73a3f4a3e6: preflight passed`.
