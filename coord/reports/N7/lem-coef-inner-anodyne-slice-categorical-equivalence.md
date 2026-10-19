# Worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-inner-anodyne-slice-categorical-equivalence.json`: repaired statement node, status `split`.
- `dag/nodes/sec-six-functors/lem-coef-inner-anodyne-joyal-equivalence.json`: new statement-only node, unsplit and not a Mathlib leaf.
- `dag/nodes/sec-six-functors/lem-coef-right-fibration-categorical-base-change.json`: new statement-only right-fibration base-change node, unsplit and not a Mathlib leaf.
- `citations.json`: verbatim statement quotes for every cited node in every proof step.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the archived upstream source for the item id, title, and slice/categorical-equivalence terminology; no project declaration states this item or the new auxiliary lemma.

## WANTED:

- Kerodon Proposition 7.3.1.14 (02YL) and Corollary 5.6.7.6 (029H), the online source for the slice comparison; no archival copy is present in `literature/`.
- HTT Theorem 2.2.5.1, for the Joyal model-structure formulation; no archival copy is present in `literature/`.

## What was wrong or incomplete

The returned item used a cocartesian pullback theorem on the right fibration `C_{/c} -> C`, while the proof only gave an informal horn sketch and did not cite a theorem applicable to that variance. It also asserted that inner anodyne implies Joyal categorical equivalence without a cited bridge from inner-fibration lifting to the Joyal weak factorization system. I added the auxiliary inner-anodyne/Joyal-equivalence node and a dedicated statement-only right-fibration pullback node in the dual variance used by the slice. Step 2 now cites that applicable node directly, with no unsupported horn sketch. The target statement and all hypotheses, including the absence of quasicategory assumptions on `L`, `K`, `L_{/c}`, and `K_{/c}`, are unchanged.

I searched the whole DAG and blueprint for duplicates of both the new auxiliary statement and the left/right/cartesian base-change fact. The existing cocartesian base-change node has the opposite variance and is not cited; the new right-fibration node is intentionally statement-only because importing the existing cartesian base-equivalence node would create a dependency cycle through the parent pointwise-Lan node.

## Review by N7

I reread the item, its chapter and unit records, the current blueprint ancestor, and the complete B–E delivery checklist. For Step 1 I read the full statements of the new `lem-coef-inner-anodyne-joyal-equivalence`, `lem-coef-inner-anodyne-pushout-product`, and `lem-coef-joyal-model-structure` nodes. The new statement-only lemma says exactly that an inner anodyne is a Joyal categorical equivalence. It records the precise bridge that the later proof must establish from the Joyal weak factorization system, so the item no longer hides that non-elementary inference in a horn sketch.

For Step 2 I read the full statements of `lem-coef-infinity-slice-right-fibration` and the new `lem-coef-right-fibration-categorical-base-change`. The slice node supplies that `C_{/c}` is a quasicategory and its projection is a right fibration. The new statement-only node is exactly the dual right-fibration pullback theorem needed here: it takes a categorical equivalence over a quasicategory base and concludes categorical equivalence after pullback, with no quasicategory assumption on either indexing simplicial set or either pullback. I checked that the map is over `C`, that `c` is a vertex, and that the theorem matches the stated `L_{/c}` and `K_{/c}` constructions.

For Step 3 I reread `def-cbc-enhanced-diagrams-cones`; its degreewise pullback convention identifies the constructed map with the stated `i_c` and preserves all hypotheses. I checked the edge cases `L=K`, empty `L`, `C=Delta^0`, and the inner horn `Lambda^2_1 -> Delta^2`. Every citation quote in `citations.json` is copied verbatim from its node statement, and `proof_deps` is the union of the step uses. The new Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch; they found no exact Mathlib theorem. No SGA source is used.

## Not duplicates

lem-coef-right-fibration-categorical-base-change vs lem-coef-cocartesian-categorical-base-change: the new statement assumes a right fibration and concludes invariance for pullback over a quasicategory base, whereas the existing statement assumes a cocartesian fibration and has a different variance and hypotheses.

lem-coef-inner-anodyne-joyal-equivalence vs lem-coef-joyal-model-structure: the new statement specializes the model structure to the implication from the inner-anodyne lifting class to categorical equivalence; the existing node constructs the full Joyal model structure and does not state that implication for arbitrary inner anodynes.

lem-coef-inner-anodyne-joyal-equivalence vs lem-coef-inner-anodyne-slice-categorical-equivalence: the auxiliary node states the general Joyal equivalence of every inner anodyne map, while the item states the specific pullback map in a quasicategory slice.

lem-coef-inner-anodyne-joyal-equivalence vs lem-coef-inner-anodyne-pointwise-lan-invariance: the auxiliary node is the model-structure bridge for inner anodynes; the existing parent node is a pointwise left-Kan invariance theorem and does not state that bridge as its conclusion.

lem-coef-right-fibration-categorical-base-change vs lem-coef-inner-anodyne-slice-categorical-equivalence: the auxiliary node is the general right-fibration base-change theorem, while the item specializes it to the slice right fibration and an inner anodyne inclusion.

lem-coef-right-fibration-categorical-base-change vs lem-coef-inner-anodyne-pointwise-lan-invariance: the auxiliary node concerns pullback of arbitrary categorical equivalences along right fibrations; the existing parent node concerns preservation of pointwise left Kan cocones and is strictly stronger in different directions, with the auxiliary theorem as an input.
