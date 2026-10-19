# Stage-1 report: prop-sf-dualizable-hom

## Files written

- `dag/nodes/sec-six-functors/prop-sf-dualizable-hom.json`: repaired statement split, 14 proof steps, no Mathlib match.
- `dag/nodes/sec-six-functors/lem-sf-rational-slice-completed-evaluation.json`: statement-only lemma, no Mathlib match.
- `dag/nodes/sec-six-functors/lem-sf-rational-thick-evaluation.json`: statement-only lemma, no Mathlib match.
- `dag/nodes/sec-six-functors/lem-sf-rational-local-global-power-torsion.json`: statement-only lemma, no Mathlib match.
- `dag/nodes/sec-six-functors/lem-sf-rational-bounded-cone-torsion.json`: statement-only lemma, no Mathlib match.
- `citations.json`: verbatim statement quotes for every cited node in every proof step.

## Attachments

None. The declaration in `WeilConjectures/SixFunctors/Etale/Derived/Perfect/Dual.lean` assumes `IsDualizable` and proves only a categorical `Nonempty` isomorphism, so it does not state this item under the item hypotheses.

## WANTED

None.

## What was repaired

The returned version had two non-elementary steps longer than 2000 characters. Former step 8 combined slice compatibility of completed operations, exactness and naturality of the rational operations, thick closure of the evaluation class, and the bounded-complex induction. Former step 9 combined construction of an integral cone, finite-cover refinement, local scalar vanishing, uniform power torsion, bounded cohomology, and truncation induction. I extracted the hidden arguments into four strictly smaller statement-only nodes and replaced those two paragraphs by six short steps. The proposition statement, finite-level calculation, integral reduction argument, and common-stage algebraically closed coefficient argument are unchanged in substance.

The four new statements were searched in the whole DAG and blueprint first. No existing node states any of them, and their sources are the rational-stage clauses of the blueprint unit. The Mathlib searches were run with `msearch.py`; the hits were generic triangulated-category, localization, or condensed-module declarations and none states the required sheaf coefficient result. No Stacks tag was added to a new node, so there was no duplicate-tag pair requiring a `Not duplicates` section.

## Review by Q94

I reread the item source `literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-dualizable-biduality/prop-sf-dualizable-hom.md`, the unit route in `literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-dualizable-biduality/_section.md`, and the corresponding declarations and docstrings in `WeilConjectures/SixFunctors/Etale/Derived/Perfect/Dual.lean`. The item keeps the exact finite-field, coefficient-stage, local site-perfect, and arbitrary-target hypotheses.

For steps 1–7 I checked every cited statement in the DAG: the finite-level slice restriction and module adjunction nodes, finite-projective evaluation, bounded exact-term Hom, K-flatness and tensor descent, the signed total-complex calculation, locality, and integral reduction/completeness. Each cited node says the operation or comparison used by its step; the quotes in `citations.json` are copied verbatim from those statements. The finite-level argument still handles the zero finite-free summand and arbitrary module targets, and the local-to-global step uses sheaf separatedness rather than stalkwise perfectness.

For repaired steps 8–10, I checked the new slice-compatibility node against the completed-operation definition: it explicitly covers reductions, finite tensor, countable products, Roos cones, internal Hom, and scalar localization. I checked the new thick-evaluation node against the cited exact-operation and triangle-isomorphism statements; it supplies precisely the closure used by the bounded truncation induction. The bounded local model step cites the site-perfect definition and the existing degreewise-split derived triangle, and its induction starts from the zero truncation above the finite degree interval.

For repaired steps 11–13, I checked the integral cone and constructibility hypotheses against the integral triangulated-subcategory node. The finite-cover step states the finite affine refinement and cites the localization-tensor and exact restriction statements; the new local-global node supplies the maximum-power argument and explicitly concludes global cohomology-sheaf annihilation. The bounded-cone step cites the uniform reduction interval, exact countable products, the long-exact cohomology bound, and the new truncation-torsion node; the latter states the exponent and uses the existing Hom-into-triangle exactness. Step 14 is the unchanged finite common-field passage, including exact scalar extension and compatibility of inverse equations.

I also checked the small edge cases mentioned by the proof: an empty scheme gives no cover to detect, a zero complex is covered by the truncation induction, and the finite-projective retraction may have rank zero. All new node statements are self-contained, unsplit statements with no hollow data or Lean claims.


## Interrupted repair resumed

The first resumed dry run exited with `SEARCH CHECK FAILED`; it pushed nothing. The retained new-node records had paraphrased several actual search queries. I replaced those records using the exact tool/query pairs in the retained `searches.jsonl`, copied the recorded hit names, and added a second semantic phrasing for each of the four different lemma questions. The new grep searches distinguish the completed-operation question, the triangulated-transformation question, local scalar detection, and bounded cohomological nilpotence. Every unavailable service would be recorded as such; these retained searches succeeded, so their verdict is a mathematical nonmatch, not service failure.

I removed proof sketches from all four unsplit statements, introduced the coefficient field, uniformizer, scheme, objects, bounds and exponent in each statement itself, added their actual definition dependencies and inherited chapter/unit fields, and made their blueprint places identify the exact source sentences. The current main-20261015 node proof has the same local finite-projective argument as the older snapshot. Its unit again describes exactness and direct summands. The four auxiliary statements make explicit the completed/rational supplements in the returned proof; they are not claimed as verbatim theorems of the blueprint. Their future proofs must establish these comparisons and torsion assertions independently.

The proposition's statement and Lean record agree exactly with the current repository, as do proof steps 1–7. Step 14 keeps the same common-field argument, with its rational-step reference updated to 8–13. The inherited maintainer-owned review and tool-use records were retained; this report supplies the current worker review, not a replacement maintainer review.

## Not duplicates

- lem-sf-rational-slice-completed-evaluation vs lem-weil-pbc-ringed-internal-hom-exact-restriction: the existing statement identifies ordinary derived internal Hom on a ringed-site slice; the new statement also compares the Roos completed tensor and the actual rational evaluation map.
- lem-sf-rational-slice-completed-evaluation vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback: the existing theorem concerns ordinary derived tensor, not completed tensor, its countable inverse-limit model, or scalar-localized evaluation.
- lem-sf-rational-thick-evaluation vs lem-sf-generating-class-determination: the existing theorem assumes exact functors and a shift-compatible natural transformation. The new lemma establishes precisely those properties for the completed/rational evaluation comparison as well as the resulting closure; those hypotheses cannot be obtained by simply substituting functor names in the existing theorem.
- lem-sf-rational-local-global-power-torsion vs lem-weil-pbc-localization-module-tensor: the existing theorem is a tensor/localization comparison for one module; it does not assert a single exponent for the cohomology sheaves of a complex on a finite site covering.
- lem-sf-rational-bounded-cone-torsion vs lem-sc-generic-primary-annihilator: the existing node concerns a curve's finite primary generic-stalk module. The new lemma concerns the identity in the derived category of a bounded integral complex, deduced from annihilation of all its cohomology sheaves.

### Additional substantive checks by Q94

For the first returned paragraph (former step 8), steps 8 and 9 now cite respectively the completed slice/evaluation comparison and the exactness/closure lemma, with definitions identifying their operations. In step 10 I corrected a C4 failure in the interrupted extraction: the canonical truncation theorem has quotient $H^r(P)[-r]$, not the required finite-projective term $P^r[-r]$. The corrected step uses brutal truncations and their explicitly degreewise split sequence, citing the existing Mathlib leaf `lem-weil-pbc-degreewise-split-derived-triangle`. Its statement gives exactly that sequence's distinguished triangle, with no K-injectivity hypothesis. The scalar-localization definition says its image triangle is distinguished. The induction starts at zero above the finite interval and uses each actual finite-projective retract; it neither requires a common integral perfect lattice nor completes the rational category by formally adjoining idempotents.

For the second returned paragraph (former step 9), step 11 keeps the integral numerator construction from the returned proof. Raw scalar localization has the same objects and maps given by tensoring integral Hom with $E$, so a finite sum of fractions has one denominator; multiplication by that invertible denominator does not change cone vanishing. The integral triangulated-subcategory theorem supplies its integral cone. Step 12 now also cites `def-weil-pbc-proetale-site`: its statement explicitly gives the finite affine refinement of a covering over an affine. Finite type supplies a finite affine cover of $X$; these facts provide the finite cover required by the local-global lemma. That new lemma's conclusion is exactly uniform annihilation of every $H^d(C)$, not integral vanishing of $C$. Step 13 uses the uniform reduction interval in the integral-category definition, sectionwise exact countable products and the displayed Roos triangle. The long exact sequence bounds $C$ in $[u,v+1]$, and the bounded-cone lemma applies with that interval. Its exponent is deliberately a harmless upper bound: when the support interval has length one, one power already suffices and the displayed larger power still kills the identity. When $N=0$, every cohomology sheaf is zero and $C=0$; when $C=0$ or $X$ is empty, both new torsion statements hold. These checks avoid replacing rational local vanishing with integral vanishing.

The new slice lemma is a statement about slice restriction, not an arbitrary scheme inverse image preserving countable products. The closure lemma concerns the actual natural evaluation comparison and its shift/triangle compatibility, not merely the existence of unrelated isomorphisms. For each new node I checked that it is strictly smaller than the proposition, contains no proof steps or proof dependencies, and cites each definition used in its statement. I reread the source proof in Stacks `sites-cohomology.tex`, Tag 08JJ, label `lemma-dual-perfect-complex`, including its reduction to the strictly perfect model and ordinary evaluation with arbitrary target; the integral and rational extensions remain marked agent-written. No prohibited SGA source is used.

All non-elementary proof steps have fewer than 2000 characters. The largest retained non-elementary step is the 1103-character integral step; I read it as the reduction/completeness argument already accepted in the returned proof. Every cited node was opened and its used assertion checked; `citations.json` was regenerated after the statement and dependency repairs so that its quotes are verbatim current statements. No unresolved mathematical point or requested repair remains in this stage-1 split.

The slice lemma also explicitly supplies preservation of derived-complete constructible objects and their uniform reduction bounds. This is the domain fact needed to apply the finite-cover lemma to the restricted integral cone. I searched that preservation question separately and recorded the actual etale-site hits as nonmatches.
