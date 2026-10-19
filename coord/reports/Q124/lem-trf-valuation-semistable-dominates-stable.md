# Q124: lem-trf-valuation-semistable-dominates-stable

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-valuation-semistable-dominates-stable.json`: item, statement retained, six proof steps, status split.
- `dag/nodes/sec-trace-formula/lem-trf-valuation-common-strict-semistable-refinement.json`: statement-only lemma, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-valuation-contracted-component-inclusion.json`: statement-only lemma, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-valuation-component-factorization.json`: statement-only lemma, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-valuation-separable-closure-extension.json`: statement-only lemma, no Mathlib match.

`citations.json` contains one verbatim statement quotation for every proof-step citation. Four new nodes, zero new Mathlib leaves. The scratch scripts and search log are sandbox evidence, not project source files.

## Attachments

None. I searched the project declarations under both read-only WeilConjectures trees for the item tag and the semistable/stable-modification and contracted-component notions. There is no project declaration giving this comparison, or any of these new auxiliary statements. The master checkout was reference material only, never evidence of a closed proof.

## Literature wanted

WANTED: Michael Temkin, Stable modification of relative curves, arXiv:0707.3953v3, Sections 2.1, 3.5, 4.2--4.5 and Appendix B, for lem-trf-valuation-semistable-dominates-stable and its common-model, contracted-component, and component-factorization nodes. The path named by the existing node has no local PDF. I read the primary PDF online at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf; I did not download or write it. The item is marked agent-written because the archival document is absent and the arbitrary-field descent is written out here.

The valuation-extension node also uses the locally available Stacks `more-algebra.tex`, Tag 0ASH (`lemma-inequality-general`) and Tag 0539 (`lemma-valuation-ring-torsion-free-flat`), and `algebra.tex`, Tag 00HR (`lemma-local-flat-ff`). The fpqc descent input is the existing node for Tag 023Q, `descent.tex`, `lemma-fpqc-universal-effective-epimorphisms`, whose statement and proof were read locally. No SGA source is used.

## What needed repair or care

The imported item has no proof, and its statement is stronger in field generality than the displayed Proposition 4.5.1: the whole of Temkin Section 4 assumes a separably closed fraction field. This is not a statement dispute: valuation extension followed by fpqc descent gives the asserted arbitrary-field result without altering any hypothesis. In particular one cannot apply the valuation theorem on the overlap V^s tensor_V V^s: that ring need not be a valuation ring. Step 5 instead proves equality of the two comparisons over the overlap using flatness over the original domain V and the relative separated diagonal.

I initially considered the existing stable-reduction node for the common refinement. Its current proof depends on lem-trf-stable-modification-uniqueness-normal, whose proof depends on this item, so using it here would introduce a dependency cycle. I report this upstream dependency hazard; I do not modify the other node. The delivered route uses the stronger strict semistable cofinality of Remark 4.5.2, independently of global uniqueness. It is not a second statement of stable reduction: it constructs a strict model refining arbitrary specified models, while stable reduction constructs a stable contraction.

The draft conditional-minimality and closed-pair-descent nodes were removed. Conditional minimality would move too much of the item into one child, so I separated the actual component-inclusion claim from the general geometric factorization criterion. Closed-pair descent is assembled from the existing representable descent theorem. Likewise marking factorization and generic uniqueness are steps, not new nodes. All new statements include their own objects and definitions and contain no proof sketch.

Early search records were associated with the wrong item argument. The first dry run rejected their absence from this item's log; nothing was pushed. I replaced these records with the searches actually present in this sandbox's searches.jsonl, after reading those results. I have not represented the earlier calls as searches logged for this item. Subsequent semantic searches use a second phrasing; the successful Loogle patterns use qualified names. All final recorded queries are literal queries from this item's log.

## What could not be finished

No mathematical subargument of the split is left implicit as a proof obligation of the item. The four explicitly stated auxiliary lemmas are deliberately unsplit, as required for a one-level stage-1 split. No Lean was written and no compiler, Lake, or build tool was run.

## Review by Q124

I read Temkin Section 4's standing finite-height and separably-closed hypotheses (printed p. 24), Proposition 4.2.3 (p. 27), the definition of strict semistability and Proposition 4.3.1 (pp. 27--28), Lemma 4.4.2 and Corollary 4.4.3 (pp. 30--31), and the construction and final comparison paragraph of Proposition 4.5.1 and Remark 4.5.2 (p. 33). The comparison in the item has the direction of Corollary 4.4.3: the semistable model dominates the stable model. The base curve is allowed to be nonproper and nonseparated; properness is needed only for the modification maps. Stability is relative to the map to C, not absolute stability of the entire curve. Empty marking is permitted throughout.

For the strict-common-model node I checked the strict cofinality assertion of Remark 4.5.2, with smooth (therefore strictly semistable) generic curve and etale generic marking. The common-model form comes from taking the reduced closure of the common generic graph in the product of the two proper models, giving a proper common modification, and then a strict semistable refinement. The reduced horizontal model and its marking are curves as in the existing lem-trf-valuation-horizontal-curve-models. This fact is about arbitrary input models, not models already known to be stable. The standing assumptions finite height and separably closed fraction field are retained. Both outputs map to the original common base, and the common marking is its generic marking's closure. I did not assert that every semistable model is itself strict.

For the contracted-component node I checked the first sentence of the proof of Corollary 4.4.3(i). It is exactly the component claim the source derives from Lemmas 4.4.2 and B.3: a component of the common semistable fibre collapsed to the semistable target must also collapse to the stable target. This is weaker than the item's comparison conclusion and does not introduce a comparison morphism. No analogous assertion for two arbitrary semistable targets is claimed; different blowups give counterexamples to that stronger assertion. Stability and the marked-pair hypotheses are essential here.

For the component-factorization node I read Proposition 4.2.3 and its proof. On a common model the displayed condition is the inclusion of surviving fibre-component generic points used there. A common image graph over Y has finite fibres under that condition: each positive-dimensional component lying over a point of Y is contracted in X as well. The graph projection is proper, quasi-finite, and a generic isomorphism, hence a finite eta-modification. The proof in the source uses normality only to conclude that such a finite modification is an isomorphism. Stating precisely eta-normality in the child is therefore valid; it is what the existing Proposition 3.5.2 node supplies. This formulation also handles disconnected curves component by component and does not require that X or Y be separated over S. I checked the direction: contraction by b implies contraction by a, hence Y maps to X, not conversely. Removing eta-normality would permit a finite normalization map with no inverse, so that hypothesis has not been dropped.

For the valuation-extension node I read Stacks 0ASH, 0539 and 00HR at their labels. The first gives finite index of value groups in each finite subextension. In an algebraic extension every value is in such a finite subextension, so the quotient of value groups is torsion. A subgroup inclusion with torsion quotient induces a bijection on convex subgroups (extend by isolator and contract), preserving their chain length; thus an arbitrary finite height is preserved, not only rank one. A valuation extending to the separable closure exists by the usual valuation extension theorem, already stated in lemma-nagata-valuation-ring-extension. The dominating inclusion is injective and torsion-free as a V-module, so 0539 makes it flat and locality makes it faithfully flat by 00HR. Affineness supplies quasi-compactness. The lemma adds the genuinely needed height/flatness conclusions beyond the existing existence node; it does not substitute an algebraic closure for a separable closure or assume discreteness.

Step 1 uses only the strict-common-model statement, which explicitly supplies both pair maps as eta-modifications and their equality over C. Step 2 uses only the component-inclusion statement, with the given f stable and g semistable; its quote says the same contraction implication. Step 3 uses the existing eta-normality statement for the semistable target and the new component-factorization statement for the implication just established. I checked that an affine valuation base is normal, integral and qcqs; the short integrality argument is written in the step. Reducedness also follows from flatness and reduced smooth generic fibre. For the marking, the existing torsion-free-sections node is applied with L=O on flat affine opens of D'; it asserts multiplication by every nonzero base element is injective without properness assumptions. Thus the pullback ideal is zero, giving the actual marking morphism, not just inclusion of its points.

Step 4 uses the valuation-extension node for a finite-height, faithfully flat base with separably closed fraction field; proper-fp-permanence for the proper maps; and marked-base-change for multipointedness, semistability, generic smoothness/etaleness and geometric stability. I opened that last node and respected its explicit warning: it does not assert preservation of modifications. The generic isomorphisms and schematic density under this flat base change are checked separately in the step by tensoring the injective chart maps. One may choose a quasi-compact schematically dense isomorphism open since these flat curves with smooth generic fibre have finitely many irreducible components. A finite affine cover computes its sections by an equalizer, preserved by the flat tensor functor. No general arbitrary-base-change claim for modifications is used.

Step 5 again uses the proper-base-change clause and the torsion-free-sections theorem, now over the original domain V. I checked B is flat over V, so both the curve and marking on the overlap are flat V-schemes even if B has zero divisors. The equalizer ideal of the two maps is defined by a closed relative diagonal (proper over C, not separated over S). It vanishes upon localizing at all nonzero elements of V and therefore is zero by torsion-freeness. This proves the actual cocycle on schemes, not only equality on geometric points. Step 6 uses the existing representable-fpqc-descent statement, which provides both existence and uniqueness for any scheme target and an fpqc cover with equal overlap restrictions. It applies separately to the curve and marking; uniqueness reflects the commuting equations. Since f_eta is invertible, the required generic formula follows from fh=g.

I searched the whole DAG and blueprint for the literature places and key notions (4.2.3, 4.4.3, strict semistability, common model, contracted components, valuation extension, finite height) and read the nearby stable-reduction, horizontal-model, strict-cofinality, marking-separation, base-change, eta-normality, fpqc-descent and generic-section nodes before choosing the final children. Existing strict cofinality assumes an already strictly semistable base curve, whereas the new common model permits arbitrary base C; neither replaces the other. The general off-unit torsion-free-sections tool is declared in split_report.tool_uses; it changes no unit route. The other off-unit permanence and representable descent inputs are existing Mathlib leaves.

I read the Mathlib hits: minimal Weierstrass equations over DVRs concern a specific elliptic equation, not general multipointed curves; rational-map representatives only give maps on open subsets, not the component criterion; valuative-criterion declarations neither construct semistable resolutions nor compare contractions; matroid contraction is unrelated. HasExtension instances assume rather than construct extensions, and the rank-at-most-one result does not preserve arbitrary finite height. The flat/torsion criterion is an ingredient, not a one-line specialization of the whole extension lemma. The final node records retain the exact query texts and result summaries. No final child is already a Mathlib theorem or a one-line specialization of a hit.

For B--E I checked every new node is statement-only, self-contained and in the item's chapter/unit, with current blueprint ancestry and no duplicate blueprint statement. TeX uses single backslashes after JSON decoding, definitions are cited or supplied inline, and no unrecorded tag is used as a proof step. All uses edges have verbatim quotes in citations.json and are exactly the proof_deps union. No step exceeds 2000 characters, and no contraction, graph-factorization, or valuation-extension lemma is hidden in a long step. The descent, ideal-zero and normality arguments are written in the item because they are short assemblies of the cited statements.

Small cases checked: V a field (height zero) forces every eta-modification to be an isomorphism and the comparison is the given inverse; no discrete-height-one assumption appears. Empty markings give the unique empty maps. Disconnected smooth generic curves and a reducible nodal special fibre are treated componentwise. An extra rational tail in the semistable model is contracted toward the stable model, consistent with the contraction direction. A retained stable component cannot be produced by contracting it in the semistable target because the exceptional-tree comparison prevents it. An algebraic valuation extension with divisible value group may be nondiscrete but has the same height, which the new extension lemma allows. The overlap argument explicitly allows a nonintegral overlap base.

## Not duplicates

lem-trf-valuation-separable-closure-extension vs lem-sbc-punctured-dvr-normalization-stalk-domain: a normalization stalk is a domain under DVR hypotheses; it constructs no valuation extension or height preservation.

lem-trf-valuation-separable-closure-extension vs lem-sbc-punctured-dvr-normalization-stalk-torsion-free: torsion-freeness of a specified normalization stalk, not extension of a valuation to a separable closure.

lem-trf-valuation-separable-closure-extension vs lem-weil-pbc-adic-tor-flat-cohomology: equivalence of adic Tor and sheaf-flatness conditions, not existence of a finite-height valued field extension.

lem-trf-valuation-separable-closure-extension vs lem-sbc-root-normalization-generic-stalk-flat: flatness of a particular root-normalization stalk over a height-one point, not valuation extension and equal height.

lem-trf-valuation-separable-closure-extension vs lem-sbc-punctured-dvr-normalization-stalk-torsion-free-injective: injectivity of a normalization stalk map under DVR hypotheses, not construction of a valuation on a separable closure.

lem-trf-valuation-separable-closure-extension vs lem-pc-local-flat-faithful-flat-reflects-surjective: assumes a flat local map; does not construct a valuation extension or establish flatness and preservation of finite height.

lem-trf-valuation-separable-closure-extension vs lem-weil-pbc-finite-projective-descends-flat-local: descent of finite projectivity along an already flat local map, not existence and rank of a valuation extension.

lem-trf-valuation-separable-closure-extension vs lem-weil-pbc-pid-torsion-free-module-flat: flatness over a PID only, not arbitrary nondiscrete finite-height valuation extension.

lem-trf-valuation-separable-closure-extension vs lem-weil-pbc-flat-local-hom-faithfully-flat: assumes flatness of a local map, whereas the new lemma constructs the valuation extension and preserves arbitrary finite height.

lem-trf-valuation-separable-closure-extension vs lemma-nagata-valuation-ring-extension: the existing theorem gives a dominating valuation on an arbitrary field extension; it states neither finite-height preservation under algebraicity nor faithful flatness/fpqc covering.

lem-trf-valuation-common-strict-semistable-refinement vs lem-trf-valuation-stable-reduction: the existing theorem constructs a stable modification, not a strict semistable common refinement of two specified models. Its current proof also depends on this item's parent and cannot be cited without a cycle.

lem-trf-valuation-common-strict-semistable-refinement vs lem-trf-valuation-strict-semistable-cofinality: the existing cofinality assumes the base curve is strictly semistable; the new node permits an arbitrary multipointed base with smooth generic fibre and simultaneously refines two models.

The delivery duplicate scanner also classifies the arXiv number 0707 in the shared Temkin PDF filename as a Stacks-tag collision. I opened each of the twelve listed statements and retain the sources; these are the substantive comparisons requested by that check.

lem-trf-valuation-common-strict-semistable-refinement vs lem-trf-valuation-semistable-dominates-stable: the new node constructs a common strictly semistable curve-pair refinement of two arbitrary specified models over a fixed finite-height valuation base; the existing node compares a given stable model with a given semistable model without assuming a common model or component data.

lem-trf-valuation-common-strict-semistable-refinement vs lem-trf-abhyankar-finite-type-field-height: the new node constructs a common strictly semistable curve-pair refinement of two arbitrary specified models over a fixed finite-height valuation base; the existing node bounds heights of valuations of a finitely generated field.

lem-trf-valuation-common-strict-semistable-refinement vs lem-trf-birational-quasi-modification-common-cover: the new node constructs a common strictly semistable curve-pair refinement of two arbitrary specified models over a fixed finite-height valuation base; the existing node produces a proper modification with open charts dominating a valuative cover by quasi-modifications, without any semistability conclusion.

lem-trf-valuation-common-strict-semistable-refinement vs lem-trf-geometrically-reduced-eta-normal: the new node constructs a common strictly semistable curve-pair refinement of two arbitrary specified models over a fixed finite-height valuation base; the existing node proves reducedness and eta-normality from flatness and geometrically reduced fibres.

lem-trf-valuation-common-strict-semistable-refinement vs lem-trf-marked-curve-finite-type-model: the new node constructs a common strictly semistable curve-pair refinement of two arbitrary specified models over a fixed finite-height valuation base; the existing node descends one curve pair to a finite-type base.

lem-trf-valuation-common-strict-semistable-refinement vs lem-trf-marked-nodal-dualizing-degrees: the new node constructs a common strictly semistable curve-pair refinement of two arbitrary specified models over a fixed finite-height valuation base; the existing node constructs a dualizing line bundle and computes its degrees on stable fibres.

lem-trf-valuation-common-strict-semistable-refinement vs lem-trf-riemann-zariski-finite-refinement: the new node constructs a common strictly semistable curve-pair refinement of two arbitrary specified models over a fixed finite-height valuation base; the existing node gives common models of the base in a fixed separable function-field extension and refinements of their valuation spaces.

lem-trf-valuation-common-strict-semistable-refinement vs lem-trf-semistable-marked-base-change: the new node constructs a common strictly semistable curve-pair refinement of two arbitrary specified models over a fixed finite-height valuation base; the existing node preserves geometric semistability and stability under base change.

lem-trf-valuation-common-strict-semistable-refinement vs lem-trf-stable-curve-diagram-noetherian-model: the new node constructs a common strictly semistable curve-pair refinement of two arbitrary specified models over a fixed finite-height valuation base; the existing node descends an entire existing stable/semistable diagram to a Noetherian base.

lem-trf-valuation-common-strict-semistable-refinement vs lem-trf-stable-modification-finite-presentation-spread: the new node constructs a common strictly semistable curve-pair refinement of two arbitrary specified models over a fixed finite-height valuation base; the existing node spreads an existing proper valuation model to a quasi-model of a finite-type base.

lem-trf-valuation-common-strict-semistable-refinement vs lem-trf-stable-modification-spreading: the new node constructs a common strictly semistable curve-pair refinement of two arbitrary specified models over a fixed finite-height valuation base; the existing node spreads an existing stable valuation modification to a stable modification on a base quasi-model.

lem-trf-valuation-common-strict-semistable-refinement vs lem-trf-stable-modification-stability-locus: the new node constructs a common strictly semistable curve-pair refinement of two arbitrary specified models over a fixed finite-height valuation base; the existing node shrinks a spread model to the locus where its fibres and morphism are stable.

lem-trf-valuation-component-factorization vs lem-trf-valuation-semistable-dominates-stable: the new node turns contracted-component data on a specified common curve model into a factorization through an eta-normal target, with no stability assumption; the existing node compares a given stable model with a given semistable model without assuming a common model or component data.

lem-trf-valuation-component-factorization vs lem-trf-abhyankar-finite-type-field-height: the new node turns contracted-component data on a specified common curve model into a factorization through an eta-normal target, with no stability assumption; the existing node bounds heights of valuations of a finitely generated field.

lem-trf-valuation-component-factorization vs lem-trf-birational-quasi-modification-common-cover: the new node turns contracted-component data on a specified common curve model into a factorization through an eta-normal target, with no stability assumption; the existing node produces a proper modification with open charts dominating a valuative cover by quasi-modifications, without any semistability conclusion.

lem-trf-valuation-component-factorization vs lem-trf-geometrically-reduced-eta-normal: the new node turns contracted-component data on a specified common curve model into a factorization through an eta-normal target, with no stability assumption; the existing node proves reducedness and eta-normality from flatness and geometrically reduced fibres.

lem-trf-valuation-component-factorization vs lem-trf-marked-curve-finite-type-model: the new node turns contracted-component data on a specified common curve model into a factorization through an eta-normal target, with no stability assumption; the existing node descends one curve pair to a finite-type base.

lem-trf-valuation-component-factorization vs lem-trf-marked-nodal-dualizing-degrees: the new node turns contracted-component data on a specified common curve model into a factorization through an eta-normal target, with no stability assumption; the existing node constructs a dualizing line bundle and computes its degrees on stable fibres.

lem-trf-valuation-component-factorization vs lem-trf-riemann-zariski-finite-refinement: the new node turns contracted-component data on a specified common curve model into a factorization through an eta-normal target, with no stability assumption; the existing node gives common models of the base in a fixed separable function-field extension and refinements of their valuation spaces.

lem-trf-valuation-component-factorization vs lem-trf-semistable-marked-base-change: the new node turns contracted-component data on a specified common curve model into a factorization through an eta-normal target, with no stability assumption; the existing node preserves geometric semistability and stability under base change.

lem-trf-valuation-component-factorization vs lem-trf-stable-curve-diagram-noetherian-model: the new node turns contracted-component data on a specified common curve model into a factorization through an eta-normal target, with no stability assumption; the existing node descends an entire existing stable/semistable diagram to a Noetherian base.

lem-trf-valuation-component-factorization vs lem-trf-stable-modification-finite-presentation-spread: the new node turns contracted-component data on a specified common curve model into a factorization through an eta-normal target, with no stability assumption; the existing node spreads an existing proper valuation model to a quasi-model of a finite-type base.

lem-trf-valuation-component-factorization vs lem-trf-stable-modification-spreading: the new node turns contracted-component data on a specified common curve model into a factorization through an eta-normal target, with no stability assumption; the existing node spreads an existing stable valuation modification to a stable modification on a base quasi-model.

lem-trf-valuation-component-factorization vs lem-trf-stable-modification-stability-locus: the new node turns contracted-component data on a specified common curve model into a factorization through an eta-normal target, with no stability assumption; the existing node shrinks a spread model to the locus where its fibres and morphism are stable.

lem-trf-valuation-contracted-component-inclusion vs lem-trf-valuation-semistable-dominates-stable: the new node asserts only that contraction in a semistable target forces contraction in a stable target on a supplied common semistable model, not existence of a factorization; the existing node compares a given stable model with a given semistable model without assuming a common model or component data.

lem-trf-valuation-contracted-component-inclusion vs lem-trf-abhyankar-finite-type-field-height: the new node asserts only that contraction in a semistable target forces contraction in a stable target on a supplied common semistable model, not existence of a factorization; the existing node bounds heights of valuations of a finitely generated field.

lem-trf-valuation-contracted-component-inclusion vs lem-trf-birational-quasi-modification-common-cover: the new node asserts only that contraction in a semistable target forces contraction in a stable target on a supplied common semistable model, not existence of a factorization; the existing node produces a proper modification with open charts dominating a valuative cover by quasi-modifications, without any semistability conclusion.

lem-trf-valuation-contracted-component-inclusion vs lem-trf-geometrically-reduced-eta-normal: the new node asserts only that contraction in a semistable target forces contraction in a stable target on a supplied common semistable model, not existence of a factorization; the existing node proves reducedness and eta-normality from flatness and geometrically reduced fibres.

lem-trf-valuation-contracted-component-inclusion vs lem-trf-marked-curve-finite-type-model: the new node asserts only that contraction in a semistable target forces contraction in a stable target on a supplied common semistable model, not existence of a factorization; the existing node descends one curve pair to a finite-type base.

lem-trf-valuation-contracted-component-inclusion vs lem-trf-marked-nodal-dualizing-degrees: the new node asserts only that contraction in a semistable target forces contraction in a stable target on a supplied common semistable model, not existence of a factorization; the existing node constructs a dualizing line bundle and computes its degrees on stable fibres.

lem-trf-valuation-contracted-component-inclusion vs lem-trf-riemann-zariski-finite-refinement: the new node asserts only that contraction in a semistable target forces contraction in a stable target on a supplied common semistable model, not existence of a factorization; the existing node gives common models of the base in a fixed separable function-field extension and refinements of their valuation spaces.

lem-trf-valuation-contracted-component-inclusion vs lem-trf-semistable-marked-base-change: the new node asserts only that contraction in a semistable target forces contraction in a stable target on a supplied common semistable model, not existence of a factorization; the existing node preserves geometric semistability and stability under base change.

lem-trf-valuation-contracted-component-inclusion vs lem-trf-stable-curve-diagram-noetherian-model: the new node asserts only that contraction in a semistable target forces contraction in a stable target on a supplied common semistable model, not existence of a factorization; the existing node descends an entire existing stable/semistable diagram to a Noetherian base.

lem-trf-valuation-contracted-component-inclusion vs lem-trf-stable-modification-finite-presentation-spread: the new node asserts only that contraction in a semistable target forces contraction in a stable target on a supplied common semistable model, not existence of a factorization; the existing node spreads an existing proper valuation model to a quasi-model of a finite-type base.

lem-trf-valuation-contracted-component-inclusion vs lem-trf-stable-modification-spreading: the new node asserts only that contraction in a semistable target forces contraction in a stable target on a supplied common semistable model, not existence of a factorization; the existing node spreads an existing stable valuation modification to a stable modification on a base quasi-model.

lem-trf-valuation-contracted-component-inclusion vs lem-trf-stable-modification-stability-locus: the new node asserts only that contraction in a semistable target forces contraction in a stable target on a supplied common semistable model, not existence of a factorization; the existing node shrinks a spread model to the locus where its fibres and morphism are stable.

