# Stage-1 report: lem-trf-perfect-complex-derived-biduality

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-perfect-complex-derived-biduality.json`: split statement; no new nodes and no new Mathlib leaves.
- `citations.json`: excerpts copied literally from each cited node's statement, one entry per step/node pair.
- `report.md`: this report. The sandbox also retains the search log and the local refinement script.

## Attachments

No whole-item attachment. I searched the project source by the item tag, perfect-complex terminology, derived dual and biduality. `DerivedCategory.IsPerfect.ihom_unit`, in `WeilConjectures/CategoryTheory/DerivedCategory/Perfect.lean:435`, states the first clause but its body at line 437 is `sorry`. The canonical-bidual declaration `DerivedCategory.IsPerfect.isIso_toIhomIhomUnit` at line 545 addresses the other clause with a chosen braiding. Neither gives a closed attachment of every clause of this item. The exact item tag has no hit.

## WANTED

None. All sources used are present locally.

## What was checked and changed

The statement remains unchanged. I read Stacks `more-algebra.tex`, Tag 07VI (`lemma-dual-perfect-complex`, lines 19175 onwards), and Tag 0A66 (`lemma-RHom-out-of-projective`, lines 18708 onwards). I also read the Hom-complex differential in `sites-cohomology.tex` Section 0A8X, its canonical internal-Hom evaluation construction (Tag 0A97), and the Koszul exchange convention in `more-algebra.tex` Tag 0FNG. The proof follows the source's bounded finite-projective Hom model. It computes an actual dual complex, rather than introducing data chosen from an unproved existence claim.

I searched the DAG and whole imported blueprint for Tag 07VI, derived biduality, duals of perfect complexes and bounded finite-projective complexes. `prop-pod-biduality-at-the-point` has related conclusions but its statement restricts to the Poincare coefficient conventions. It cannot be specialized to an arbitrary commutative B. I reuse its generic ingredients individually, whose statements have the required arbitrary-ring or arbitrary-ringed-site hypotheses. No new node was needed. In particular no elementary finite-product collapse or componentwise inverse lemma was made into a node, and no clause was moved into a new statement. The ancestor and the existing unit/chapter records were read; this generic algebraic tool serves the established relative-duality branch and does not replace the normal-cone route of `sk-i-curve-zero`.

The initial delivery dry run found four quotations that were not verbatim: two had specialized the source variable R to B and two quoted a proof sentence or changed sentence capitalization. I corrected these by copying the statements directly. A later mathematical self-review made the one-object-site interpretation explicit and checked both quasi-isomorphism hypotheses of the canonical-bidual normalization; it also wrote the chain-map sign calculation out. Those refinements are now in the item. Every proof step is below 2000 characters.

The seeded item's prior Mathlib searches were preserved. Fresh searches were run with `msearch.py` using two conceptual phrasings and Loogle project-name patterns, followed by LeanSearch and proper Mathlib source-directory searches. The actual raw result summaries and digests are appended to `mathlib_searches`. LeanFinder returned generic K-projective/localization or tensor-Hom identities; LeanSearch returned ordinary-module duality. Grep in `Algebra/Homology/DerivedCategory` found only a comment about dualizing an Ext file, and grep in `LinearAlgebra/Dual` found the ordinary termwise ingredients already covered by `lem-sf-finite-projective-dual`. Two early grep calls incorrectly supplied `Mathlib` as the relative subdirectory (the script already appends Mathlib); those zero outputs remain in the immutable search log but are excluded from absence evidence and from the newly appended node records. Unknown project-specific Loogle identifiers are likewise not treated as sufficient evidence by themselves. No search was fabricated, and no unavailable service was classified as a mathematical nonmatch.

## What remains unfinished

Nothing in the assigned one-level split. The cited prerequisite nodes retain their own independent status; none was edited. Only stage 1 was performed, with no Lean writing, compiler, Lake, git command in the shared project, agent spawning, or shared-project mutation.

## Review by Q63

For Step 1 I read `def-pc-perfect-ring-complex`, whose statement supplies exactly an isomorphism to a bounded finite-projective representative. `def-pc-perfect-rhom-base-change-map` explicitly realizes ordinary modules as sheaves on the bottom-topology one-object site, so I use its identity-ring-map setting only for that interpretation, not for its base-change conclusion. I spell out the inverse evaluation/constant constructions and their effect on complexes and operations. `def-sc-module-total-hom-complex` supplies the product formula and signed differential used from this point onward.

For Step 2 I checked that `lem-sf-finite-projective-dual` assumes only a commutative ring and a finitely generated projective module, and concludes finite generation and projectivity of its dual. Its hypotheses apply term by term with no Noetherian or field assumption. The sole nonzero factor of the total Hom is in degree -r; inserting zero in the other coordinates proves the product collapse directly. The differential has square zero because the original differential does. The bounded-above projective hypotheses of `lem-pod-projective-hom-evaluation-model` hold for P; its canonical comparison identifies the actual E with the derived dual, and the original perfect definition then proves its perfectness.

For Step 3 I reopened the statements of the projective Hom model and `lem-sfb-ringed-site-duality-maps`. The latter's bidual normalization specifically requires two quasi-isomorphisms into Hom with the fixed K-injective resolution and, unlike its tensor comparison clause, requires no K-flatness. The item now explicitly proves both hypotheses using the canonical natural comparison for T=P and T=E, naturality in the resolution map, and the localization/cohomology factorization in `def-weil-abstract-derived-category`. Both P and E are bounded above and projective, as already proved. `def-pur-derived-internal-hom` identifies the fixed-resolution targets with the specified derived Homs. Thus the canonical-map node is applied to exactly the representatives and comparisons it states, not merely to isomorphic unspecified objects.

For Step 4 the canonical-map node states the signed formula for the actual bidual map, and the ordinary-dual node states reflexivity of each finite-projective term. I checked the chain-map equation against the Hom differential: for x of degree p and phi of degree -p-1, the outer Hom differential gives (-1)^(p+1) phi(d_P x), exactly evaluation of delta(d_P x). Only degree -p contributes to the value of delta(x), so its degree-p component is (-1)^p times reflexive evaluation. Inverting the components gives a chain inverse by cancellation, without an uncited comparison theorem. Step 5 quotes both naturality clauses and writes the resulting square with the chosen representative isomorphism; all its other factors are images of isomorphisms, so it proves invertibility of the canonical map itself.

I tested zero and rank-zero complexes, the zero coefficient ring, and a rank-one module shifted to odd degree (where the sign is essential). No extra ring hypothesis appears. All citations are actual statement excerpts and proof_deps is exactly their union. The three cross-unit statement tools are declared in split_report.tool_uses; they are generic algebra/Hom/map interfaces absent from the trace unit's own statements. No SGA route, statement dispute, duplicate new node, cycle-producing appeal to a caller, or hidden long-step lemma is present.
