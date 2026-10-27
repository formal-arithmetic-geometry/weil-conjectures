# Stage-1 delivery: lem-sfb-integral-simple-reflection-gauss-chart

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-integral-simple-reflection-gauss-chart.json: statement, split into seven steps; no Mathlib match.
- citations.json: verbatim statement citations for every step/use pair.
- report.md: this report. searches.jsonl contains the searches run by the required command.

No new nodes and no Mathlib leaves. The item statement and all maintainer-owned fields are retained.

## Attachments

None. Searched the live lean/WeilConjectures/ source for the exact blueprint id and simple-reflection, integral-reflection and Gauss terminology. The Gauss hits concern polynomial arithmetic, Gaussian elimination and unrelated matrix arguments. No declaration proves this item. No Lean was written and no compiler was run.

## WANTED

WANTED: Brian Conrad, Reductive group schemes, https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, local archival copy, Lemma 6.3.8, equation (6.3.4), printed pp.220--222, for this item. I read the original PDF online. No SGA source is cited or used. This root-coordinate computation has no Stacks tag; inventing a tag would be misleading.

## What needed repair

The imported item has a correct statement but no proof. The support assertion is an agent refinement of Conrad, not a quotation of his lemma. I supplied the morphism and the scheme-theoretic support and inverse arguments, rather than assuming an ambient integral reductive group or a group law on mixed-sign support.

The coordinate on the final positive simple-root factor is -v chi_a(t)/d, not -v/d: the positive factor must be moved past the reflected torus. The denominator in the item is correct. There is no statement dispute or changed hypothesis. The existing from.node is null; blueprint_refs.py ancestor confirms None, and I retained the inherited provenance instead of inventing an ancestor. The current unit has moved/changed in latest; I read the current latest section, the recorded unit and chapter and kept the existing supporting integral-model route. This item is not the unit's key statement, so no unit file is changed.

## Not duplicates

No new nodes. Reused the one-sign integrality, full Weyl/root-subgroup calculus, rational rank-one centralizer and local rank-one matrix-model nodes. Whole-DAG searches by 6.3.8, 6.3.4, rank-one, root-coordinate support and linked generator, and whole-blueprint searches for integral simple reflection Gauss chart, root subgroup, rank one and closed roots found no node that could replace this item. Existing longest-Weyl and birational-law nodes depend on this item and were not cited backwards. The Weyl-calculus dependency closure has no path to this item.

## Review by Q17

I read delivery-errors sections B through E, both copies, and checked the actual cited statements rather than their proof text. The source for the item is Conrad's proof of Lemma 6.3.8 on printed pp.220--222. I read the displayed decomposition (6.3.4), the middle rank-one product and the unit condition. No new node needs a separate source review.

Step 1 uses the one-sign node's actual rational Gauss identity and signed conjugation statements. The existing Weyl-calculus statement gives the linked generator, torus reflection and square of its representative. To justify that its linked generator is exactly our supplied opposite parameter, I cited the rank-one centralizer and local matrix-model statements, which really provide the centralizer and its matrix model, not only a definition of rank one. Over Q the centralizer has roots {a,-a}, is reductive and has the same full maximal split torus; Q is nonzero and Noetherian, as required. In the matrix model rescale the upper parameter and write the lower entry as kv. The torus factor is a-coroot(1+kuv); comparison with the supplied identity and application of a gives coefficient equation 2k=2, so k=1. The central factor does not affect this calculation. The elementary simple-root coefficient argument proves the permutation of all other positive roots. It does not presume an integral realization.

Step 2 uses precisely the one-sign statement's arbitrary-order polynomial isomorphisms and polynomial group laws; these construct L' and R' in the correct separate sign groups. Step 3 uses precisely its opposite-root Gauss identity, and D_Z(s_a) from the diagonalizable-group definition. I checked q, t', both torus characters, both signs and the final torus commutation. The torus pullback d^{<m,a-coroot>} chi_{s_a m} is an invertible Laurent monomial in the localized ring, even for negative exponents. This constructs an actual morphism. Step 4 substitutes the torus and every root axis into that formula; it uses the one-sign node's signs and axis identifications, and verifies d=1 and the identity explicitly.

Step 5 uses the Weyl-calculus statement's closed, no-opposites root-product theorem over Q, where an ambient rational group is already assumed. P and both intersections satisfy its exact closedness definition: sums of roots in a positive system remain positive when they are roots. The integral reordering statements are from the one-sign node. Vanishing of integer polynomial coefficients after tensoring with Q proves equality of the coordinate ideals in both ordering directions. This establishes scheme equality, not only equality of field-valued points.

Step 6 first proves d=1 on C_P using the fact that a positive system chooses exactly one root from each opposite pair. The cited rational closed-root-product theorem identifies the entire rational coordinate subspace with U_P in negative-before-positive order. Signed conjugation identifies it with U_{s_a P}; injectivity of the hypothesized open immersion gives the actual output support equations. Every forbidden coordinate is then an integer polynomial on C_P (d=1), so rational vanishing implies integral vanishing. This works over nonreduced rings after base change; it does not claim that two arbitrary maps agreeing on geometric points agree.

Step 7 uses the Weyl-calculus statement's n_a squared equals a-coroot(-1), so the fourth power is 1. Both support systems are already known to lie in the domain. Four alternating restrictions equal the identity by coefficient injectivity on the polynomial rings of C_P and C_{s_a P}. The triple iterate is therefore an actual two-sided inverse. No claim of involutivity of F_a was made: its square can be a nontrivial torus sign action.

I tested rank zero (there is no simple root), rank one in SL2, identity and all root axes, both choices P={a} and P={-a}, characteristic two sign collapse, and nonreduced rings. In SL2 direct multiplication yields torus d/t and coordinates -u t^2/d and -v t^2/d, confirming the formula. For mixed P, the proof uses rational subgroups only for the polynomial identities; no mixed integral group structure enters. All steps have complete uses lists and verbatim quotes in citations.json. Each non-elementary step is below 2000 characters; the remaining steps are explicit substitutions, ring formulas or coefficient comparisons from the cited statements. The source's omitted support argument has been supplied rather than silently delegated to a restatement node. Searches returned abstract root-system lemmas and unrelated Gauss/Jordan-Chevalley lemmas, not an integral algebraic-group chart. I read returned signatures and local Mathlib source before recording no match.

## Unfinished

Nothing in the one-level split. The cited open nodes remain existing independent prerequisites, not assertions that their Lean proofs are complete.
