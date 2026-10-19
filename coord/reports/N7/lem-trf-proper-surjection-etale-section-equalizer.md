## Files written

- `dag/nodes/sec-trace-formula/lem-trf-proper-surjection-etale-section-equalizer.json`: statement unchanged; eight-step split, 16 existing proof dependencies, no new nodes. Mathlib search verdict: no match for the item.
- `citations.json`: 23 entries, one for every cited node in every proof step, using verbatim portions of the current statements.
- `report.md`: this report. `searches.jsonl` was produced by the required search command; `write_split.py` is sandbox-only preparation, not a delivery node.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` tree for the exact item id and for proper/surjective/equalizer/descent terminology, including the algebraic-geometry sites and etale base-change files. There is no project declaration stating this equalizer. The underived proper-base-change theorem found in `SixFunctors/Etale/BaseChangeTheorems/UnderivedExchange.lean` ends in `sorry`; its docstring is not a finished proof of the item. The DAG's existing, unrestricted geometric-point exchange node is used as an open dependency instead.

## WANTED

None. All sources used are already in `literature/stacks-project/`. No source was downloaded, no Lean was written, and no compiler, Lake, build, or local delivery-check command was run.

## Audit of the imported item

The imported statement is correct and was preserved byte for byte. Its properness, surjectivity, arbitrary abelian coefficients, the double fibre product, the specific units and the two projection maps all remain as stated. The item initially had no proof, so there was no existing sandbox split or report to resume. The inherited blueprint ancestry and searches were retained. Whole-blueprint and DAG searches for the equalizer, proper surjections, 0DDW and 0A3T found the existing comparison chain and the geometric-point exchange tool, not another blueprint node stating this item exactly. `blueprint.same_as` remains empty. The item is not the key statement of `sk-i-curve-zero`, so no unit record is changed.

The actual Stacks 0DDW proof applies to every sheaf of sets, and therefore to the underlying sets of abelian sheaves without torsion assumptions. Its last paragraph repeats “first factor/first projection” where the second occurrence should refer to the second factor/projection. This is an expository typo, not a false item statement. I replaced that terse intersection-of-images argument with the explicit calculation along `(id_W,e a)` on each geometric fibre. The rational point e is obtained from the existing Jacobson and closed-point residue-field nodes; its existence is not asserted over U, or even over an etale neighbourhood of U. No statement correction or STATEMENT-DISPUTED is required.

## New nodes

None: 0 new nodes and 0 new Mathlib leaves. The split uses existing nodes even when their statement is more general, and does not move the equalizer assertion into a new child. In particular 0A3T is supplied by the existing `lem-weil-pbc-proper-geometric-point-exchange` together with the existing geometric-point pullback/stalk identification; the torsion-only statement of `lemma-weil-pbc-proper-underived-exchange` is not used.

## Not duplicates

No new-node pairs exist. The closed-point construction is a short application of `lem-sc-lft-over-field-jacobson-space` and `lem-weil-pbc-closed-point-residue-field-base`, not a new rational-point lemma. The equalizer contraction is a proof step, not a node restating the item over a field. Proper base change, composition, surjectivity under base change, exact stalks, conservative stalks, and sectionwise limits are all cited from existing nodes.

## Mathlib searches

Ran the required `msearch.py N7 lem-trf-proper-surjection-etale-section-equalizer` commands, and read the returned hits. The exact queries and result digests are in `searches.jsonl`, and the item records those queries without editing them. The inherited five search records were preserved.

- LeanFinder, “Proper surjective morphism descent equalizer of sections of inverse image small etale abelian sheaf”: hits were scheme transition-limit section results and general coherent-topology local-surjectivity results. They do not state the requested descent theorem.
- Loogle, `"IsProper", "equalizer"`: zero hits.
- grep, `proper.*(equaliz|descent)|equaliz.*proper|surjective.*etale.*sheaf`: generic equalizers, condensed equalizer conditions, scheme flat descent, and ring flat equalizers; none proves the small-etale proper-surjection assertion.
- LeanSearch, “Proper surjective descent for sections of a small etale abelian sheaf”: generic local-surjectivity, the definition of the small etale topology, and flat descent; none is the item.
- Second LeanFinder phrasing, “Small etale sheaves have unique gluing of pulled back sections along a proper surjective map”: ordinary topological open-cover gluing and scheme gluing results. Their open-cover hypotheses do not cover an arbitrary proper surjection.

All five services returned usable results (including the empty Loogle result); no outage was treated as evidence of absence. No new nodes require further searches.

## Review by N7

I read Stacks `etale-cohomology.tex`, Tag 0DDW (`lemma-describe-pullback-pi-ph`), including the entire proper-surjection equalizer proof, and Tag 0A3T (`lemma-proper-pushforward-stalk`) and the beginning of 0A3U (`lemma-proper-base-change-f-star`). I also read the current `main-20261015` unit text and `lem-trf-local-term-locality.proof.md`, the DAG chapter and unit records, and the item's recorded blueprint origin. This delivery expands only the proper-surjection equalizer input in the inherited ph/etale comparison chain for normal-cone specialization. It does not change the chapter or unit route and uses no forbidden source.

For step 1 I opened the statements of `def-weil-pbc-direct-image`, `def-weil-pbc-sites-and-cohomology`, and `lem-weil-pbc-sheafification-exact`. The first supplies the actual precomposition direct image, the second supplies the inverse-image adjunction and composition conventions, and clause (1) of the third states that kernels/limits are computed sectionwise. Thus H, J, the unit maps, and the sheaf E exist with the claimed formulas. The two composites of units coincide by the formula for the unit of a composite adjunction, which is written explicitly. This is not an application of sheafification exactness to claim that global sections are exact on short exact sequences: only the sectionwise limit clause is used. I checked that clause against `sites.tex`, Tag 00W2 (`lemma-limit-sheaf`), and `sites-modules.tex`, Tag 03CO(2) (`lemma-limits-colimits-abelian-sheaves`).

For step 2 the statements of `lem-weil-pbc-proper-base-change` and `lem-weil-pbc-proper-composition` give exactly the two properness facts needed for q. I read their sources in `morphisms.tex`, Tags 01W4 (`lemma-base-change-proper`) and 01W3 (`lemma-composition-proper`). The geometric double-product identification uses the universal property stated in `def-pc-fibre-product`: both maps to the fibre are fixed by their projections. There is no assumption of an isomorphism between a scheme fibre product and a set-theoretic fibre product.

For step 3 I opened `lem-weil-pbc-proper-geometric-point-exchange` and verified its statement explicitly allows arbitrary commutative coefficient rings with no torsion hypothesis. Both applications have proper morphisms, an algebraically closed geometric point, and the prescribed cartesian square. Choosing Z merely expresses an abelian group as its canonical integer module. `lem-weil-pbc-geometric-point-pullback-stalk`, clause (2), states exactly the global-sections/stalk identification used for all three groups. I checked Tags 04JN (`remark-stalk-pullback`) and 04JQ (`lemma-equivalence-abelian-sheaves-point`) in `etale-cohomology.tex`. The composition of inverse images is explicitly in `def-weil-pbc-sites-and-cohomology`. This step does not infer a theorem from a definition of properness.

For step 4 the cited statement of `def-weil-pbc-underived-exchange` contains the actual representative formula, not just the name of an exchange map. I used its final paragraph to track a section z on V times_U T all the way to the geometric fibre. The two restrictions after a projection have identical two projections into V times_U T, so the cited fibre-product universal property proves their equality. `lem-weil-pbc-inverse-image-stalk-germ` states precisely compatibility of the inverse-image unit with germs; it applies with the geometric point and pointed etale neighbourhood used here. I read its source Tag 03Q1(3) (`lemma-stalk-pullback`), including the colimit calculation. This checks the specified arrows rather than merely choosing abstract isomorphisms between their endpoints.

For step 5 I read `lem-weil-pbc-surjective-base-change`: it allows an arbitrary base change and its conclusion is surjectivity, which makes W nonempty because Spec k is nonempty. Its source is `morphisms.tex` Tag 01S1 (`lemma-base-change-surjective`). Proper base change and the definition of properness give finite type over k. The statement of `lem-sc-lft-over-field-jacobson-space` says closed points are dense in every closed subset; applying it to all of W gives a closed point, since the closure of the empty set cannot be nonempty W. I read `varieties.tex` Tag 0478 (`lemma-locally-finite-type-Jacobson`). The last sentence of `lem-weil-pbc-closed-point-residue-field-base` identifies the structural composite from Spec of the residue field with an isomorphism, so composing its inverse gives exactly the required section e. I checked this against `morphisms.tex` Tag 01TB (`lemma-jacobson-finite-type-points`) and its Nullstellensatz explanation. This uses finite type of a geometric fibre, not finite type or noetherianity of U.

Step 6 is the short calculation that finishes the fibre argument. It uses only the stated fibre-product universal property and the adjunction/composition conventions. Pulling equality along h=(id,e a) gives z=a-sharp(e-sharp z); pulling a descended section back along e gives its original value because ae=id. The existence, uniqueness, and converse are all written separately. The maps on coefficients use e^{-1}a^{-1}L=L and h^{-1}b^{-1}L=a^{-1}L under those same composition identifications. I did not use connectedness, reducedness, finite components, or a rule saying that every constant-sheaf section is globally constant. This is the explicit completion of 0DDW's last paragraph, so there is no missing constant-section theorem.

For step 7 I checked the full statements of `prop-weil-pbc-geometric-stalks-exact` and `lemma-weil-pbc-geometric-stalk-conservative`: they apply to arbitrary abelian etale sheaves. Exactness computes the stalk of the kernel E, and conservativity applies to the actual map theta, whose composite to H was fixed in step 1. I read the sources `etale-cohomology.tex` Tags 03PT(3) (`lemma-stalk-exact`) and 03PU (`theorem-exactness-stalks`). For step 8 the same sectionwise-limit clause and direct-image formula from step 1 identify the resulting equalizer with the exact diagram in the item, including uniqueness and its two particular arrows.

I checked B through E of `coord/delivery-errors.md` against the finished split. Every non-elementary input is a node; every step's cited statement actually contains the fact taken from it; the citations file contains verbatim quotes for every occurrence. There are no new statements to test, and the item was checked on the empty base, the zero sheaf, the identity surjection, a disconnected finite fibre, and a nonreduced finite fibre. For empty U no geometric fibre is chosen; for nonempty geometric fibres the section e exists independently of smoothness. Every step has fewer than 2000 characters, and none hides a standard comparison or lemma: proper exchange, the actual arrow formula, point existence, stalk exactness, and sheaf limits have explicit separate citations. The cross-unit statements are general tools expanding the prescribed stalk argument; each is declared in `split_report.tool_uses` with its role. The item statement, chapter, unit, import metadata and ancestry were preserved.

## What could not be finished

Nothing mathematical remains at this one-level split. The open proof obligations are the existing dependencies, not unrecorded assertions or newly created duplicates. Required server dry run and push are performed after this report is written.
