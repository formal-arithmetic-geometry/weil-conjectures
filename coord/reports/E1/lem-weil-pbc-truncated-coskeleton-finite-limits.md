# Stage-1 delivery: lem-weil-pbc-truncated-coskeleton-finite-limits

## Files written

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-truncated-coskeleton-finite-limits.json`: statement split into six proof steps. No new node; the existing Mathlib leaf `lem-weil-pbc-presheaf-finite-limits-objectwise` supplies objectwise evaluation.

## Attachments

None. The slopmaster2 source has no declaration tagged with this id or stating the finite-limit preservation of coskeleta; its Mathlib coskeleton declarations require right Kan extensions and do not assert clauses (2)-(4).

## Wanted

WANTED: `literature/stacks-project/simplicial.tex`, Lemmas 0183, 0184, 0185, and `literature/stacks-project/hypercovering.tex`, Lemma 01GD, for lem-weil-pbc-truncated-coskeleton-finite-limits. The source TeX directory recorded as obtained in `literature/LIST.md` is absent in this checkout. I read the Stacks pages for those tags online; the node marks its expanded proof as agent-written until the local document is restored.

## Findings

The imported item had no proof. Its statement agrees with the formula and counit of Stacks 0183-0185. The assertion that a finite-limit-preserving functor carries this coskeleton to a coskeleton, the functoriality in a truncated morphism, and sectionwise evaluation are consequences of that formula used in the proof of 01GD, but were not proved in the imported node. No statement change was needed. Its blueprint reference already specified the exact ancestor and place, and the whole-blueprint search for `coskeleton` found no equivalent blueprint node.

## Unfinished

None in this split. The local Stacks TeX restoration is a literature maintenance task recorded above, not a missing proof step.

## Review by E1

I read Stacks Simplicial tags [0183](https://stacks.math.columbia.edu/tag/0183) (lemma-existence-cosk), [0184](https://stacks.math.columbia.edu/tag/0184) (lemma-trivial-cosk), and [0185](https://stacks.math.columbia.edu/tag/0185) (lemma-recover-cosk), and Hypercoverings tag [01GD](https://stacks.math.columbia.edu/tag/01GD) (lemma-acyclicity). The item states the same finite diagram and limit as 0183. Tag 0184 says the identity arrow is final in the slice when the degree is at most the truncation, and 0185 derives the counit isomorphism. Tag 01GD invokes the finite-limit construction in the passage through sheafification. Its brief sentence does not give the preservation and naturality arguments, so steps 4-6 spell them out. There are no new nodes whose separate hypotheses require source checking.

Step 1 uses `def-galois-finite-limits-colimits` for limits of finite diagrams and `def-weil-pbc-simplicial-set` and `def-weil-pbc-simplicial-object` for the simplex category and contravariance. The finite-object and finite-arrow counts use the explicit finite ordinals in the statement. The limit projections uniquely define each simplicial operator, and their equations prove identity and composition. This is the construction given by 0183; the uniqueness calculation is written in the step.

Step 2 uses `def-weil-pbc-simplicial-coskeleton` for the required Hom-set bijection and `def-weil-pbc-simplicial-object` for naturality. The formulas `g_{n,alpha}=t_k V(alpha)` and `U(psi)t_k V(alpha)=t_{k'}V(alpha psi)` explicitly check both directions of the bijection. They match the identity-component argument in 0183 and require no hidden theorem.

Step 3 uses the coskeleton definition for its counit. The identity `[k] -> [k]` is final in the indexing slice and initial after taking opposites; I checked this for `m=0,k=0` and for `m=1,k=1`. Projection at that object is the inverse image of the unique cone map, giving the isomorphism claimed by 0184-0185. No extra limit hypothesis is used.

Step 4 uses the already assumed finite-limit preservation and the same diagram's finiteness from step 1. It checks that the image cone is limiting, then repeats the explicit Hom-set calculation from step 2 in the target category, which does not need to have all finite limits. For an `m`-coskeletal `K`, the equation `Phi(epsilon) sk_m(Phi(c))=id` identifies the image isomorphism with the canonical map. This proves the consequence cited in 01GD, rather than assuming preservation of a right Kan extension.

Step 5 uses the coskeleton mapping property and the limit projections already constructed. It checks naturality of the cone maps, the counit equation, identity, composition, and inverse using uniqueness. Preservation by `Phi` is equality for the image coskeleta expressly chosen in step 4; no arbitrary choice of coskeleton is equated on the nose. The edge case `m=0` reduces to a map of products indexed by vertices, with the same equations.

Step 6 cites `lem-weil-pbc-presheaf-finite-limits-objectwise` clause (1), whose statement covers set-valued functors on the opposite of a category and the evaluation functor. A category can be given the trivial topology to instantiate that node's site parameter; its presheaf assertion does not depend on the topology. I checked the empty finite diagram (terminal presheaf) and a binary product sectionwise. The citation says both facts used by this step.

I searched the full DAG and blueprint for coskeleton and objectwise finite-limit statements and searched the slopmaster2 Lean source by id and concept. The existing presheaf node has already been reviewed as a Mathlib leaf, so this split creates no duplicate. Against delivery-errors B-E: there is no unsplit new node; every expression in the statement introduces its data and the item retains its definition citations; each proof step has its actual cited statements and uses no tag as a substitute for a node; the six steps prove the four clauses rather than restating them; the finite-limit assumption is applied only to finite indexing categories and no finite limits are assumed in the target category. I corrected the imported proof gap by adding the Hom-set calculation and the preservation, functoriality, and evaluation arguments. No source statement was weakened.
