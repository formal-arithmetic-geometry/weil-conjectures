## Files written

- `dag/nodes/sec-trace-formula/lem-trf-valuative-domination-eta-normal.json`: repaired split, nine steps; statement unchanged; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-riemann-zariski-birational-neighbourhoods.json`: new statement-only lemma, unsplit; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-base-modification-comparison-fibre-image.json`: new statement-only lemma, unsplit; no Mathlib match.
- `citations.json`: exact statement quotes for every node cited by each step. `searches.jsonl` retains the original and repair searches. Three stale dependency copies inherited in the sandbox were moved to `retained-context/`; they are not part of this delivery, and the current shared dependency statements are cited.

## Attachments

None. Read-only searches in `WeilConjectures/` for the blueprint tag and for eta-normality, valuative domination, modifications, and Riemann–Zariski spaces found no project declaration proving the whole item. The upstream master is reference material, not evidence of completion. No Lean was written or compiled.

## WANTED

WANTED: Michael Temkin, *Stable Modification of Relative Curves*, arXiv:0707.3953v3, Proposition 5.2 (printed pp. 34–35), Proposition 3.2.1, Lemma 3.2.2 and Corollary 3.2.7 (printed pp. 15–17). The PDF is absent from the local archive. I read the online PDF at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf without downloading it. Accordingly the expanded graph proof has `proof_origin.by = agent`.

## What was wrong and what changed

The return's D3/D5/E5 objection is correct. A valuation section can sweep out a positive-dimensional fibre when its residue field is transcendental; the original step 2 supplied no valid contradiction. This repair removes that argument entirely, including the attempted use of Stacks 0GSH to obtain a valuation inside the fixed function field. It follows the first paragraph of Temkin's actual proof: spread the comparisons to birational quasi-models, use quasi-compactness to choose finitely many, refine to one proper modification of the base, and glue.

The remaining non-elementary descent input is now an explicit smaller lemma: given the flat reduced finite-type diagram, eta-normality of Y, a single proper birational base modification and a comparison over it, the image of a projection fibre over a closed point is finite in the other family's fibre. This is the fibre-image subclaim in the second paragraph of Proposition 5.2, before connectedness is invoked, with the missing flatness argument supplied by faithful flatness and formal functions. The new node has no valuation-comparison hypothesis and no conclusion that a global factorization exists. Thus it is neither the item nor one of its conclusions renamed. The item's proof still carries the spreading, finite covering, gluing, graph construction, surjectivity, finite graph fibres, finiteness, and eta-normal descent arguments. I have not hidden the finite-image inference in a step citing only definitions.

For C1, the finite-height bound is the existing `lem-trf-abhyankar-finite-type-field-height`; the duplicate created during repair was removed. Step 8 cites `pqf-lem-proper-lqf-finite` for proper locally quasi-finite implies finite, as requested. It also cites the relative-dimension-zero criterion and proper fibre-dimension upper semicontinuity, instead of silently passing from closed-point fibres to local quasi-finiteness.

For the two E5 objections, Step 5 spreads the generic comparison over a dense base open and uses separatedness of a to make its graph closed. Flatness proves that graph is the closure of its generic graph, giving an actual open isomorphism of the graph projection. The two schematic-density statements are distinct: flatness gives density in Y, while the defining kernel of schematic closure gives density of the inverse-image open in Γ. Step 2 writes out the separated-equalizer uniqueness argument used on all integral birational models. Step 9 is the unchanged final projection argument.

The item statement and its target hypotheses remain unchanged. No disputed statement or route change is needed; the proof now follows the source's proper base-modification mechanism rather than the returned pointwise argument. No SGA source is used.


## Source error

Temkin’s printed sentence on p. 35 says that the image of a closed subset of $(X\times_S S')_s$ lying in the relative closed-point locus “must be s-quasi-finite.” This inference is false as written: a quasi-finite closed subset of $X_s\times_s S'_s$ can be the graph of a nonconstant map $S'_s\to X_s$, whose image in $X_s$ is a curve. The returned review’s example $X=\operatorname{Bl}_s(S)$, $Y=C=S$, $S'=X$, with the diagonal comparison, exhibits exactly this failure; it violates flatness of $X$, which the source sentence does not use. I corrected the node by retaining the flatness hypotheses and adding the missing eta-normality hypothesis already present in Proposition 5.2. The corrected argument uses faithful flatness of the local ring map at a candidate non-closed image point, then proper formal functions and the Stein factorization of $Y'\to Y$ to force its residue field to be finite over $\kappa(y)$; Zariski’s lemma then rules out a positive-transcendence-degree image point. The report and Step 7 explicitly identify this repair and the source error.

## Unfinished work

The two new non-elementary lemmas are deliberately statement-only, as required for a one-level stage-1 split. The fibre-image node now records the corrected flatness/formal-functions route and is not claimed as proved in Lean. There is no remaining gap in the item's argument relative to its cited statements after this repair.

## Review by Q134

I read Proposition 5.2 in the online Temkin PDF, including both paragraphs rather than just its statement. I read §§3.2.1–3.2.2 and the neighbourhood assertions of §3.2 for the fixed-K Riemann–Zariski lemma. This source permits parameter field K itself; replacing K by a separable closure would not justify the item's given valuation hypothesis. I also checked the source's finite-image assertion on printed p. 35 before its use of Stein-factor connectedness. That assertion, with the flat reduced finite-type modification diagram retained, is exactly the second new node. The new nodes have no proof steps and are not circular prerequisites claiming domination itself.

For Step 1 I opened all three cited statements. Noetherian permanence starts with Spec Z, algebraic finite presentation applies on Noetherian affine charts, and the Abhyankar lemma bounds every valuation of a finitely generated field over its prime subfield. The field-generation argument is included so that finite height is not assumed for arbitrary valuations of an unspecified field.

For Step 2 I read the flat torsion-free sections lemma: it really allows any domain and any flat scheme, with L=O, and requires neither properness nor a valuation base. The proper-morphism definition includes separatedness; the affine flatness criterion and the tensor-preserves-injections definition justify base-change flatness by the explicit tensor calculation. Localizing the injectivity and pulling back the separated diagonal gives the asserted generic uniqueness. C need not be separated over S, and the argument never assumes it is.

For Step 3 I compared the fixed-K neighbourhood lemma and the full morphism-descent statement. The affine transition, directedness, qcqs initial term and finite-presentation hypotheses are all verified. Descent is applied over the inverse system of C-base changes, so the descended map is over C. The proper morphisms a and b are finite type over the Noetherian C, so the affine finite-presentation theorem from Step 1 applies directly; tensoring finite presentations proves base-change finite presentation. This avoids assuming separatedness of C to descend the equation ah=b. Quasi-compactness supplies the finite list.

For Step 4 I opened the common-cover node: it is genuinely birational with fixed component function fields, and its hypothesis is a finite family covering all centred valuations. It produces a reduced proper modification with open comparison maps, not just a separable alteration. The dense open makes its total space integral here. Generic density and separatedness then justify gluing on the overlaps.

For Steps 5–6 I reread proper-permanence, morphism descent and the fibre-product definition. The graph is closed relative to Y because a is separated; no absolute separatedness is used. Descent of h_eta gives a dense base open, and the defining kernel of schematic closure proves both the generic graph identification and density in Γ. The map from Y′ factors through Γ by flat generic density; its graph and proper base change prove it proper, and its image contains the dense generic graph. Thus its surjectivity, including on fibres, is justified.

For Step 7 I opened the new fibre-image statement and the closed-point field lemma. The supplied q is integral, proper birational with function field K; all original C,X,Y remain reduced flat finite type with proper generic isomorphisms. The point y is closed in Y and hence in its fibre. Zariski's lemma applies to Y_s over κ(s), not to a valuation residue field. The finite-dimensional tensor-algebra calculation then proves dimension zero for the actual graph fibre, even when valuation residue fields elsewhere are transcendental.

For Step 8 I opened the proper fibre-dimension, relative-dimension-zero and proper locally quasi-finite finiteness statements. Their exact conclusions give respectively the open set, local quasi-finiteness and finiteness. Properness supplies local finite type. Noetherianness of Y supplies the closed point in a nonempty closed complement; no density-of-closed-points assumption on a general scheme is substituted. Both schematic-density clauses of the eta-modification and generic-fibre isomorphism were checked in Step 5 before eta-normality is used. Step 9 uses only the fibre-product identity and the inverse of p.

I checked small cases: over a field the valuation space has its identity model and the graph is already the generic graph. For the fibre-image node, q=id makes its assertion the image of one closed point, closed over κ(s) by the finite residue extension; X=Y=C with identity comparisons gives a constant projection image for any q. The node deliberately asserts finiteness, not a singleton without eta-normality. Flatness of X is essential: if X is the blow-up of a surface S at a closed point, Y=C=S and S′=X, the base-changed comparison can map the exceptional fibre onto a curve; X is not S-flat and is excluded. I also retained the reviewer's transcendental-residue objection and did not reuse the invalid valuation-section argument. The corrected fibre-image node is tested on q=id and on the non-flat blow-up counterexample, which is excluded exactly by its flatness hypothesis. All proof steps are below 2000 characters; no long step conceals another comparison lemma. I checked B–E for exact hypotheses, source places, statement dependencies, real progress in the split, verbatim citation quotes, and new-node duplication/Mathlib searches.

## Searches and reuse

The retained item searches are preserved verbatim. For each new node I ran LeanFinder, LeanSearch, Loogle and the mandated Mathlib grep command, and read the returned hits. Each also has a second natural-language phrasing. The searches are recorded exactly from `searches.jsonl`, including tool/query, hit summaries and digests. Valuative criteria for a single morphism, ordinary scheme quasi-compactness, base-change stability instances and finite global sections of proper schemes do not state either new lemma. No Mathlib leaf was newly created. The DAG and blueprint searches found the Abhyankar bound and birational common-cover lemma, which are reused, but not the fixed-K neighbourhood package or the finite-image descent input. In particular the separable-closure Riemann–Zariski node cannot be specialized by putting its separable closure equal to a general K.

## Not duplicates

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-abhyankar-finite-type-field-height: bounds prime chains in valuation rings; it does not construct valuation neighbourhood models or control comparison fibre images.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-abhyankar-finite-type-field-height: bounds prime chains in valuation rings; it does not construct valuation neighbourhood models or control comparison fibre images.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-birational-quasi-modification-common-cover: constructs a common proper model from an already finite valuation cover; it supplies neither the local limit/neighbourhood theorem nor the comparison fibre-image result.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-birational-quasi-modification-common-cover: constructs a common proper model from an already finite valuation cover; it supplies neither the local limit/neighbourhood theorem nor the comparison fibre-image result.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-finite-fibre-valuation-domination: states finite fibre-valuation test for domination of curve modifications; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-finite-fibre-valuation-domination: states finite fibre-valuation test for domination of curve modifications; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-geometrically-reduced-eta-normal: deduces eta-normality from geometric reducedness over a normal base; neither new node assumes or concludes this.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-geometrically-reduced-eta-normal: deduces eta-normality from geometric reducedness over a normal base; neither new node assumes or concludes this.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-marked-curve-finite-type-model: states finite-type integral models of multipointed curves; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-marked-curve-finite-type-model: states finite-type integral models of multipointed curves; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-marked-nodal-dualizing-degrees: states marked dualizing line bundle and contracted-component degrees; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-marked-nodal-dualizing-degrees: states marked dualizing line bundle and contracted-component degrees; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-no-isolated-contracted-fibre-component: states a curve modification cannot contract an isolated whole fibre component; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-no-isolated-contracted-fibre-component: states a curve modification cannot contract an isolated whole fibre component; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-nodal-normalization-adjunction: states normalization adjunction for a component of a nodal curve; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-nodal-normalization-adjunction: states normalization adjunction for a component of a nodal curve; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-normal-approximation-finite-eta-modification: descends a finite eta-modification over a normal affine base with geometrically reduced fibres to a Noetherian model; neither new node assumes normality or constructs such a finite-modification model.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-normal-approximation-finite-eta-modification: descends a finite eta-modification over a normal affine base with geometrically reduced fibres to a Noetherian model; neither new node assumes normality or constructs such a finite-modification model.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-riemann-zariski-finite-refinement: fixes a separable closure L of k(T) and allows finite separable generic extensions; the neighbourhood node fixes K itself, and the fibre-image node concerns a given comparison diagram.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-riemann-zariski-finite-refinement: fixes a separable closure L of k(T) and allows finite separable generic extensions; the neighbourhood node fixes K itself, and the fibre-image node concerns a given comparison diagram.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-semistable-marked-base-change: states arbitrary base change of semistable marked curves and fibrewise stability; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-semistable-marked-base-change: states arbitrary base change of semistable marked curves and fibrewise stability; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-single-valuation-semistable-extraction: states extract one residual-dimension-one valuation on a strict semistable model; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-single-valuation-semistable-extraction: states extract one residual-dimension-one valuation on a strict semistable model; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-stable-curve-diagram-noetherian-model: states normal finite-type models of finite semistable modification diagrams; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-stable-curve-diagram-noetherian-model: states normal finite-type models of finite semistable modification diagrams; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-stable-modification-finite-presentation-spread: states finite-presentation spreading of a marked modification from a valuation ring; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-stable-modification-finite-presentation-spread: states finite-presentation spreading of a marked modification from a valuation ring; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-stable-modification-spreading: states spreading a prescribed stable valuation model to a quasi-alteration; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-stable-modification-spreading: states spreading a prescribed stable valuation model to a quasi-alteration; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-stable-modification-stability-locus: states constructible stable locus and dense isomorphism open for a spread modification; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-stable-modification-stability-locus: states constructible stable locus and dense isomorphism open for a spread modification; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-stable-modification-uniqueness-normal: compares stable marked curves over a normal base; neither new node assumes curves or stability, or concludes uniqueness.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-stable-modification-uniqueness-normal: compares stable marked curves over a normal base; neither new node assumes curves or stability, or concludes uniqueness.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-strict-semistable-model-normal: states normality of a strictly semistable model with smooth generic fibre; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-strict-semistable-model-normal: states normality of a strictly semistable model with smooth generic fibre; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-valuation-algebraic-height: compares heights under an algebraic extension of valued fields; neither new node makes an algebraic field extension.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-valuation-algebraic-height: compares heights under an algebraic extension of valued fields; neither new node makes an algebraic field extension.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-valuation-common-strict-semistable-refinement: states common strict semistable refinements of curve models; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-valuation-common-strict-semistable-refinement: states common strict semistable refinements of curve models; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-valuation-component-factorization: states factorization of curve modifications detected on contracted components; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-valuation-component-factorization: states factorization of curve modifications detected on contracted components; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-valuation-contracted-component-inclusion: states inclusion of contracted fibre components in a common semistable model; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-valuation-contracted-component-inclusion: states inclusion of contracted fibre components in a common semistable model; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-valuation-exceptional-blowdown: states one exceptional blow-down over a finite-height valuation ring; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-valuation-exceptional-blowdown: states one exceptional blow-down over a finite-height valuation ring; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-valuation-exceptional-closed-image-criterion: states closed-image exceptional components detect stability; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-valuation-exceptional-closed-image-criterion: states closed-image exceptional components detect stability; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-valuation-horizontal-curve-models: states horizontal curve models and schematic closures of markings; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-valuation-horizontal-curve-models: states horizontal curve models and schematic closures of markings; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-valuation-marking-semistable-separation: states separate the marking on a strictly semistable curve; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-valuation-marking-semistable-separation: states separate the marking on a strictly semistable curve; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-valuation-semistable-dominates-stable: states valuation comparison from semistable to stable modifications; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-valuation-semistable-dominates-stable: states valuation comparison from semistable to stable modifications; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-valuation-semistable-stable-contraction: states contract a given semistable modification to a stable one; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-valuation-semistable-stable-contraction: states contract a given semistable modification to a stable one; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-valuation-stable-reduction: states stable reduction over finite-height separably closed valuation fields; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-valuation-stable-reduction: states stable reduction over finite-height separably closed valuation fields; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-valuation-strict-semistable-cofinality: states strictly semistable modifications are cofinal over a strict model; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-valuation-strict-semistable-cofinality: states strictly semistable modifications are cofinal over a strict model; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-valuation-strict-semistable-local-uniformization: states strictly semistable local uniformization along centred valuations; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-valuation-strict-semistable-local-uniformization: states strictly semistable local uniformization along centred valuations; the new nodes instead concern fixed-function-field model neighbourhoods and projection-fibre images, with no marking, nodal-curve, stability, extraction or contraction conclusion.

lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-valuative-domination-eta-normal: is the full valuation-to-global factorization criterion; neighbourhood models and finite fibre images under one supplied comparison are smaller inputs, neither of which concludes global domination.

lem-trf-base-modification-comparison-fibre-image vs lem-trf-valuative-domination-eta-normal: is the full valuation-to-global factorization criterion; neighbourhood models and finite fibre images under one supplied comparison are smaller inputs, neither of which concludes global domination.


lem-trf-base-modification-comparison-fibre-image vs def-trf-multipointed-curve-modification: the existing definition packages morphisms and stability of marked curves; the new lemma concerns arbitrary reduced flat finite-type C-schemes, a proper birational base change, eta-normality, and finiteness of a projection-fibre image.
lem-trf-riemann-zariski-birational-neighbourhoods vs def-trf-multipointed-curve-modification: the existing definition concerns eta-modifications of multipointed curves; the new lemma constructs fixed-function-field valuation neighbourhoods for an integral scheme with no curve or marking data.
lem-trf-base-modification-comparison-fibre-image vs def-trf-multipointed-curve: the existing definition only defines flat finitely presented multipointed curves and pure fibre dimensions; the new lemma proves a finite image statement for proper comparisons after a base modification.
lem-trf-riemann-zariski-birational-neighbourhoods vs def-trf-multipointed-curve: the existing definition only defines marked relative curves; the new lemma constructs the fixed-K Riemann-Zariski topology and filtered birational models.
lem-trf-base-modification-comparison-fibre-image vs lem-trf-abhyankar-inequality: Abhyankar bounds value-group rank and residue transcendence for finitely generated field extensions; the new lemma uses flatness, eta-normality and formal functions to prove finite projection-fibre images.
lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-abhyankar-inequality: the Abhyankar node gives only a numerical valuation inequality; the new lemma gives quasi-compact valuation neighbourhoods and filtered affine models.
lem-trf-base-modification-comparison-fibre-image vs lem-trf-birational-riemann-zariski-neighbourhoods: the existing node gives quasi-compact valuation spaces and birational model neighbourhoods; the new lemma concerns finite images of fibres under a supplied comparison and does not construct the valuation space.
lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-birational-riemann-zariski-neighbourhoods: the existing node states a general Val_F topology and unique lifts to models, while the new lemma fixes K and records the affine filtered-limit construction used in Temkin’s Proposition 5.2 route.
lem-trf-base-modification-comparison-fibre-image vs lem-trf-elementary-semistable-chart-globalization: the existing node constructs local semistable chart blowups over finite-height valuation rings; the new lemma has no semistable charts or valuation-ring base and proves a finite image in a flat comparison diagram.
lem-trf-riemann-zariski-birational-neighbourhoods vs lem-trf-elementary-semistable-chart-globalization: the existing node is a local semistable blowup construction over a finite-height valuation ring; the new lemma is the global fixed-function-field Riemann-Zariski neighbourhood theorem.
