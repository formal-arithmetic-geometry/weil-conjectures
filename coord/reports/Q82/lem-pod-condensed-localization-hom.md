# Stage-1 report: lem-pod-condensed-localization-hom

## Files written

- `dag/nodes/sec-poincare-duality/lem-pod-condensed-localization-hom.json`: item, now split into eight steps; statement unchanged; no Mathlib match.
- `dag/nodes/sec-poincare-duality/lem-pod-stratified-dualizable-bounded.json`: new statement-only lemma; no Mathlib match.
- `dag/nodes/sec-poincare-duality/lem-pod-stratified-dualizable-hom-continuity.json`: new statement-only lemma; no Mathlib match.
- `citations.json`: a literal statement quotation for each step/dependency pair.

## Attachments

None. I searched the live `lean/WeilConjectures/` for the blueprint tag, condensed localization, stratified dualizability, and the relevant Hom/continuity notions. The ring-object and rationalization declarations do not state this arbitrary-condensed-ring, arbitrary-qcqs Hom comparison. No declaration qualifies for ATTACH.

## WANTED

None. Hemo–Richarz–Scholbach, Constructible sheaves, arXiv:2305.18131, is present in the literature directory. I read its Definition 3.3 (p. 7), Lemma 4.10 and Corollary 4.11 (p. 11), Lemma 5.3 and its proof (p. 14), and Section 5.3 including Proposition 5.5 and its proof (p. 15). The two new nodes are the general geometric inputs of that proof, not consequences of scalar localization.

## Problems in the imported material

The item is a correct formulation of the Hom-group part of HRS Proposition 5.5. No statement correction or dispute is needed. Its imported proof was empty. The point that must not be omitted is the common lower bound on the target telescope: HRS Remark 5.4 explicitly rules out an unrestricted colimit assertion. I supply this using HRS Corollary 4.11 before invoking Lemma 5.3. The full faithfulness here concerns the raw scalar localization, and no essential-surjectivity or Karoubi-completion statement is inferred from the source's stronger categorical formulation.

The current blueprint's sk-def-perfect final local-model equivalence is the ancestor. This split supplies its qcqs rational-local-model comparison, not the proof of Poincare duality. The unit and chapter records need no change: this item is not the unit's key node.

## Not duplicates

lem-pod-stratified-dualizable-bounded vs lem-sfb-bounded-constructible-iff: that node characterizes a bounded-constructibility predicate already involving boundedness and classical cohomology sheaves; the new lemma derives boundedness from finite stratified dualizability for any condensed ring on a qcqs scheme.
lem-pod-stratified-dualizable-bounded vs lem-zl-condensed-dualizable-local-perfect-models: that node's local scalar perfect-model equivalence assumes locally finitely many irreducible components; this lemma has no such condition and applies to stratified dualizable objects.
lem-pod-stratified-dualizable-hom-continuity vs lem-sfb-condensed-bounded-hom-continuity: the existing node assumes topologically Noetherian X and finite E/Q_l and its locally finitely presented constructibility predicate; the new lemma assumes only qcqs and arbitrary condensed coefficients and stratified dualizability.
lem-pod-stratified-dualizable-hom-continuity vs lem-sfb-constructible-internal-hom-continuity: the existing node concerns internal sheaf Hom under topological Noetherianity and O_E/E finite-constant local models; the new lemma concerns global Hom groups for arbitrary condensed coefficients and qcqs schemes.
lem-pod-stratified-dualizable-hom-continuity vs lem-sfb-dc-hom-filtered-colimit: the existing node assumes internal-Hom continuity as a hypothesis and deduces a scalar extension comparison; the new lemma proves global-Hom continuity under geometric stratified-dualizability hypotheses, with no coefficient extension in the conclusion.
lem-pod-stratified-dualizable-hom-continuity vs lem-weil-pbc-condensed-qcqs-pushforward-continuity: the existing node is the direct-image/cohomology continuity of HRS 5.3(1), not its constructible-source Hom assertion 5.3(2).
lem-pod-stratified-dualizable-hom-continuity vs lem-sfb-internal-hom-localization-comparison: that node assumes continuity and concludes a localization comparison for internal Hom; the new node supplies general geometric global-Hom continuity and does not assert localization.

I searched the whole DAG by source title, Proposition 5.5, Lemma 5.3, Corollary 4.11, Lemma 4.10, and the boundedness/duality/colimit concepts, and inspected the candidate statements above. Whole-blueprint searches included localization, filtered colimits, dualizable, stratified dualizable, and bounded-hom. No blueprint node states either new general-qcqs assertion. Mathlib searches used msearch.py only: five searches for each new node, including two natural-language phrasings, Loogle, grep, and LeanSearch. The raw results are retained in searches.jsonl and search-*.txt. Loogle's unknown-identifier replies are retained as such, not interpreted as evidence of absence. The independent LeanFinder and source queries do not state either result. I inspected the discrete condensed fully faithful functor, Condensed AB5, and derived t-structure candidates in their Mathlib source: none provides the missing geometric theorem.

## Review by Q82

I read HRS rather than inferring the result from a definition of constructibility. Definition 3.3 says lisse means dualizable and constructible means stratified lisse; on qcqs schemes it gives a finite global stratification. Thus its predicate is exactly the item's predicate. Corollary 4.11 explicitly says every such object is bounded; no finite dimension or Noetherian assumption appears. Lemma 5.3 explicitly gives internal Hom continuity and then global derived Hom continuity on uniformly bounded-below diagrams. The strict termwise diagrams in the new statement-only continuity lemma are a specialization; taking cohomology gives every integer r and the cocone-leg formula. These are the sources read for the two new nodes. Each has its own complete statement, introduces all objects, and has no proof or proof dependencies.

Step 1 uses the definition of section localization to identify the coefficient telescope, then the derived scalar localization reflection node for exactness, termwise computation, and the unit normalization. The complex-colimit node states the comparison with every leg, not only an abstract colimit existence assertion. I checked all its hypotheses: commutative ring sheaves on a small site, actual localization, exact extension/restriction, and the unit x maps to 1 tensor x. The reflection statement supplies the hypotheses for the telescope statement. No assertion about continuity is taken from a definition.

Step 2 uses precisely the two new HRS statements. The boundedness lemma provides a termwise bounded-below representative of N, and every stage of its scalar telescope is this same complex. The continuity node therefore applies to the small filtered category N with a uniform lower bound. The induced transition in Hom is scalar t, and the colimit leg is the leg already normalized in Step 1. M need not be globally dualizable. I did not replace constructibility by perfectness or invoke finite cohomological dimension.

Step 3 uses the ordinary module-localization colimit lemma, whose statement gives both the isomorphism and the fraction f/t^n for the n-th leg. I wrote the inverse balanced maps identifying module localization with tensoring by R[1/t]; this is elementary algebra, not another node. Step 4 cites the derived coefficient adjunction, whose statement contains the Hom bijection and both representative normalization formulas. These show that the resulting comparison is the requested canonical map t^(-n)(1 tensor f), for all shifts, rather than an unspecified bijection.

Step 5 proves naturality, identities and composition by explicit fraction equations and invokes only the defining scalar-localization category formulas. It does not use a category-theoretic full-faithfulness theorem to hide the Hom argument.

For Step 6 I read the ordinary ringed-site closed symmetric monoidal theorem and the ringed-topos derived tensor pullback theorem. The latter applies to the identity geometric morphism with coefficient map B to B', so it supplies the invertible tensor comparison in exactly these ordinary derived categories. Closure under tensor is written directly using a common finite refinement and the tensor of two dual pairs. This remains elementary duality algebra; there is no claim that arbitrary stratified objects are globally dualizable.

Step 7 uses the cited native tensor-constraint statement, which gives the associator, unitors and Koszul symmetry on actual tensor generators. I checked the forward and inverse balanced maps and the three coherence calculations in the step. Equalities on the local generators give equal sheafified chain maps; passing to derived maps preserves these equalities. No coherence theorem with stronger geometric assumptions is invoked.

Step 8 uses the actual pro-etale inverse image and the monoidal pullback-from-point composition isomorphism, the general ringed-topos tensor comparison, and the scheme constructible-preimage statement. The composition-isomorphism node explicitly gives the required inverse-image identification and its monoidality. I added this citation during the self-review so that the coefficient identification is not inferred merely from the definition of the point pullback. Both coefficients and their telescopes pull back, and on representatives the scalar-extension/restriction comparison is the identity on the pulled-back generator. Pulling back the evaluation and coevaluation preserves their equations. The strata remain a finite constructible locally closed stratification, deleting empty strata if desired. This checks both the naturality of the Hom map under restriction and compatibility of tensor/unit comparisons; it makes no assertion about direct images.

I checked every uses entry against the cited node's statement, and citations.json contains only literal quotations from those statements. I declared the off-unit generic tools in split_report.tool_uses, since none is a substitute for a step of the perfectness unit. There is no SGA reference. The new nodes are neither clauses of the localization conclusion nor relabelings of the item: boundedness and bounded-below Hom continuity are independent inputs, and the item carries the telescope, adjunction, fractions and coherence arguments.

Small-case checks: Y empty and the zero coefficient ring give zero Hom groups; t=1 leaves the identity comparison; nilpotent t gives zero localized coefficients and the zero colimit of the nilpotent scalar tower. Neither module localization nor the sheaf reflection input assumes t nonzero or regular. A nonperfect quotient module is not assumed dualizable on the point; the hypotheses do not silently include it. The two new lemmas allow arbitrary condensed coefficients but keep exactly the qcqs and bounded-diagram hypotheses of HRS. No step exceeds 2000 characters; the two non-elementary HRS inputs were extracted instead of being hidden in a long step.

## Unfinished work

None at this split level. The two new statement-only dependencies are deliberately left unsplit for future stage-1 work. No Lean files were written, and no compiler, Lake, local DAG checker, or library build was run.
