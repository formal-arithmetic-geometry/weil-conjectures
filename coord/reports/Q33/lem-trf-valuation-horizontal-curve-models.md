# Worker report: lem-trf-valuation-horizontal-curve-models

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-valuation-horizontal-curve-models.json`: repaired item split with six proof steps.
- `dag/nodes/sec-trace-formula/lem-trf-valuation-torsionfree-flat.json`: new statement-only Stacks 0539 dependency; Mathlib searches found no exact match.
- `citations.json`: verbatim excerpts for every node cited by every proof step.

## Attachments

No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` states the item. The exact blueprint tag is absent from that source tree.

## WANTED

WANTED: `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf`, especially Remark 4.1 (pp. 24--25), the opening paragraph of §4.2 (p. 26), and Lemma 3.5.1 (p. 20). The archival PDF is absent locally; the online source named in the imported node was used as the source reference.

## Source correction repaired

The earlier repair incorrectly changed “reduced modification” to “reduced eta-modification” and used a cusp counterexample. That counterexample is not a modification: the map `Spec(V[t^2,t^3]) -> Spec(V[x])` with `x` mapping to `t^2` has degree two over `D(x)`, so it is not an isomorphism on a schematically dense open. I restored the original clause. In the proof, the generic points of a reduced source lie in the schematically dense isomorphism open; therefore the generic-fibre map is proper, quasi-finite, and birational onto the smooth (hence normal) generic curve, and is an isomorphism. This is the clause required by `lem-trf-valuation-stable-reduction`.

## Review by Q33

I read the current item, the returned entry, the unit ancestry, Temkin’s cited Remark 4.1, §4.2 opening, and Lemma 3.5.1 references, plus the statements of every cited DAG node. I checked the restored statement hypothesis by hypothesis against the source route and verified that the item’s original reduced-modification clause is retained. I searched the DAG and blueprint for the torsion-free-flat fact and for finite-presentation variants before adding the new node; no existing node states Stacks 0539, while `lem-trf-flat-finite-type-dense-presentation` states the needed dense-open finite-presentation criterion.

Step 1 uses only the flatness, finite-presentation, and dimension definitions. It checks injectivity into the generic localization, reducedness from smooth generic fibre, and finiteness of components. Step 2 now explicitly proves the generic-fibre isomorphism from reducedness, schematic density, properness, quasi-finiteness, birationality, and normality of the smooth generic curve. It uses the new Stacks 0539 node for torsion-free implies flat and the dense-open finite-presentation node for finite presentation; I verified all their hypotheses, including finite height making the generic open retrocompact and schematically dense. Step 3 checks the kernel closure formula, torsion-freeness and flatness of the quotient, finite presentation via the same dense-open criterion, finite freeness via the existing valuation-module node, and pure dimension via the existing dimension node. It now spells out that the ideal of `D` pulls back to zero by torsion-freeness, so the closure map factors through the closed marking, is proper, and is an eta-modification because the generic fibres are identified and schematically dense. Step 4 compares kernels of two flat closures and is elementary after the cited flatness definition. Step 5 is the localization argument for quasi-compact restrictions. Step 6 repeats the integral birational quasi-modification construction, explicitly cites Stacks 0539 and the dense-open finite-presentation criterion, and checks the finite-presentation and pure-dimension hypotheses.

For the new node I checked the exact Stacks label 0539 and tested the statement on a valuation ring itself, a field (where every module is flat), and a torsion-free submodule of a fraction-field vector space. Mathlib searches were rerun and logged for the item and the new node using LeanSearch, LeanFinder, Loogle, and Mathlib grep; the hits provide only Dedekind/Bézout or localization criteria, so there is no exact Mathlib leaf. The closure statement was compared against nearby DAG nodes for finite presentation, flat dense generic fibres, valuation-module freeness, and common modifications; none duplicates it. The new node is strictly smaller than the item and does not restate an item clause.

## Not duplicates

`lem-trf-valuation-torsionfree-flat` vs `lem-sc-valuation-fp-torsionfree-free`: the new node applies to arbitrary torsion-free modules and concludes flatness; the existing node requires finite presentation and concludes finite freeness.

`lem-trf-valuation-torsionfree-flat` vs `lem-trf-flat-finite-type-dense-presentation`: the new node is the valuation-ring flatness criterion; the existing node extends finite presentation of a flat finite-type module from a dense open.

## What was wrong or incomplete

The returned version had weakened the reduced-modification hypothesis, relied on a false cusp counterexample, omitted the Stacks 0539 dependency, cited finite presentation only through a node that needs finite presentation as input, and did not explain why the closure pair map is proper or an eta-modification. These are repaired in the item and citations. The item’s original hypothesis and downstream use are now aligned.

## What remains

No Lean code was written and no compiler or build tool was run, as required. The remaining check is the required server-side DAG/review dry run.

`lem-trf-valuation-torsionfree-flat` vs `lem-weil-pbc-pid-torsion-free-module-flat`: the new node covers arbitrary valuation rings and arbitrary modules; the existing node covers torsion-free modules over principal ideal domains, a narrower base class.

`lem-trf-valuation-torsionfree-flat` vs `lem-sbc-punctured-dvr-normalization-stalk-domain`: the new node concludes flatness from torsion-freeness; the existing node concludes that a normalization stalk is a domain in a finite-etale/DVR setup.

`lem-trf-valuation-torsionfree-flat` vs `lem-sbc-punctured-dvr-normalization-stalk-torsion-free-injective`: the new node is the general valuation-ring flatness criterion; the existing node proves injectivity of a specific normalization stalk map.

`lem-trf-valuation-torsionfree-flat` vs `lem-sbc-punctured-dvr-normalization-stalk-torsion-free`: the new node concludes flatness for arbitrary torsion-free modules over valuation rings; the existing node only establishes torsion-freeness of a particular normalization stalk over a DVR.

`lem-trf-valuation-torsionfree-flat` vs `lem-sbc-root-normalization-generic-stalk-flat`: the new node is the general module criterion; the existing node proves flatness of a particular normalization stalk under root-divisor, regularity, and finite-normalization hypotheses.

`lem-trf-valuation-torsionfree-flat` vs `lem-weil-pbc-adic-tor-flat-cohomology`: the new node is a module-level valuation-ring theorem; the existing node is a derived sheaf Tor/flatness equivalence whose valuation-ring fact is only an ingredient.
