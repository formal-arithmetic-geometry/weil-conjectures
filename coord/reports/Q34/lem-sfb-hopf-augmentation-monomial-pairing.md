## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-hopf-augmentation-monomial-pairing.json — statement, split; no Mathlib match, all clauses retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-bialgebra-counit-word-product-rule.json — statement-only unsplit prerequisite; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.
- citations.json — exact statement excerpts for every proof-step citation.

## Attachments

None. I searched WeilConjectures/ by the exact blueprint tag, augmentation, convolution, HopfAlgebra and cotangent. WeilConjectures/RingTheory/HopfAlgebra/Cartier.lean has relevant proved partial results: AlgHom.finiteDimensional_cotangent, AlgHom.exists_isHomogeneous_sub_aeval_mem_pow_succ and AlgHom.eq_zero_of_isHomogeneous_of_aeval_mem_pow_succ. The last assumes characteristic zero, and none supplies all-degree admissible-characteristic factorial convolution evaluation and annihilation, so these are not an exact attachment. Its invariant-derivation existence results likewise do not state the new word-product formula.

## WANTED

None: Milne's Algebraic Groups PDF and the current blueprint are available and were read.

## Findings and source correction

The item has no earlier sandbox split, report or search log to preserve; its live statement, proof-source qualification and inherited metadata were retained. The current blueprint was read at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/: _section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. This is a supporting algebra input of the inherited direct-image proof (3) chain, not a change of its route. tools/blueprint_refs.py ancestor returns None for this deeply created chain. I retained that inherited null ancestor and via list, prepending this item for its child, rather than inventing a blueprint ancestor. Searches of the whole blueprint for augmentation, Hopf, cotangent, monomial, Leibniz and convolution found no equivalent node.

Milne, Lemma 11.27, printed p.218 (PDF p.230), states the basis result. Sections 11e, 11.24--11.26, printed pp.216--218, explain the counit tangent functionals and invariant extensions. The printed proof gives the invariant derivation the wrong codomain k and asserts a global coordinate derivative identity. It is false globally even on G_m: C=k[t,t^{-1}], epsilon(t)=1, x=t-1 and v(x)=1 give D_v(x)=t, not 1. Evaluation gives epsilon(D_v(x))=1. The item's existing source qualification already makes this correction. No change to the item's statement is needed. I use the direct ordered convolution product rule to compute at the counit, without asserting global coordinate derivatives or commuting invariant derivations.

## Not duplicates

lem-sfb-bialgebra-counit-word-product-rule vs lem-sfb-bialgebra-distribution-tangent-calculus: the existing node identifies tangent functionals with invariant derivations and proves the distribution order bound; it does not state the ordered subsequence product formula on arbitrary factors.
lem-sfb-bialgebra-counit-word-product-rule vs lem-sfb-convolution-linear-map-algebra: the existing Mathlib leaf supplies associativity and the unit on the full linear dual, not a product rule for counit derivations.
lem-sfb-bialgebra-counit-word-product-rule vs lem-sfb-hopf-augmentation-monomial-pairing: the new lemma is an arbitrary-factor identity in a bialgebra, without finite type, chosen coordinates, a factorial hypothesis, a basis assertion or an ideal-annihilation assertion. The item's steps derive those assertions using counting and quotient expansion; the new lemma does not restate a clause.
lem-sfb-bialgebra-counit-word-product-rule vs lem-sfb-characteristic-zero-distribution-enveloping: the latter identifies the whole enveloping algebra and distribution algebra in characteristic zero; it does not state the new product formula.
lem-sfb-bialgebra-counit-word-product-rule vs lem-sfb-borel-graded-bialgebra-monomial-basis: the existing node concerns finite-dimensional connected signed graded bialgebras over perfect fields and bounded nilpotent generators, not unsigned counit-functionals on an arbitrary commutative bialgebra.
lem-sfb-bialgebra-counit-word-product-rule vs lem-sfb-graded-bialgebra-coordinate-derivations: that node supplies signed coordinate derivations for a finite connected graded algebra; it does not give the ordered convolution product formula for arbitrary ungraded commutative bialgebras.
lem-sfb-bialgebra-counit-word-product-rule vs lem-sfb-restricted-rational-differentiation: that node assumes positive-characteristic affine groups and states restricted Lie and coaction calculus, not the arbitrary-factor ordered product formula.

## Argument retained for the new prerequisite

The new node is left statement-only. Its proof can expand the iterated coproduct into r tensor slots. Coassociativity identifies the evaluation against v_1 tensor ... tensor v_r with the ordered convolution word; multiplicativity of Delta makes this iterated coproduct an algebra map. In each slot, repeated use of the binary counit Leibniz identity for v_i on c_1 ... c_m chooses exactly one factor, with epsilon on every other factor. The choices are functions from the r positions to the m labelled factors. Regrouping the finite sums by c_j, counit cancellation deletes unused slots, leaving W_{f^{-1}(j)}(c_j) in its original increasing order. This gives the asserted formula. For r=0 this is multiplicativity of epsilon, and for m=1 it is the word itself. This is the reusable combinatorial lemma, not the augmentation-basis theorem or a relabelled clause of it.

## Review by Q34

I read the item and new prerequisite against Milne 11.24--11.27, printed pp.216--218. I read the complete statements of both proof dependencies: lem-sfb-convolution-linear-map-algebra and the newly stated product rule. In step 1 the polynomial expansion in shifted algebra generators proves finite-dimensionality directly; the scalar/I splitting and the quotient dual basis give all of v_i's prescribed values, and expanding two factors proves exactly the counit Leibniz hypothesis. This needs neither Noetherianity as an unstated theorem nor Nakayama.

Step 2 takes only associativity and the counit unit from the existing convolution leaf. Its R=k, B=k specialization has all hypotheses: C is a k-module with the given coassociative coproduct and both counit identities, and k is an associative unital k-algebra. The cited statement explicitly includes these conclusions and explicitly needs no cocommutativity. Step 3 uses the new lemma with r=|a|, m=r+1, and factors in I. Its hypotheses follow from step 1 and the item's bialgebra axioms. The empty-fibre/pigeonhole argument makes every summand zero and proves annihilation of the full ideal power by linearity, with ring coefficients absorbed into an I factor. Step 4 uses the same cited formula with m=n>0; only bijections survive, and the Kronecker coordinate values give zero for unequal multiindices and exactly product(a_i!) for equal multiindices. No symmetry of Delta or commutation of the v_i is used. citations.json quotes these formulas verbatim.

Step 5 expands representatives of the quotient basis in each I factor to prove spanning in every degree; an I^2 remainder raises the total ideal degree by one. The linear relation is separated by the already established annihilating functionals and the calculated diagonal entries. The n! assumption implies each a_i! is nonzero since a_i<=n, so division is legitimate over a field. Step 6 separately checks n=0 via C/I=k, and d=0 via I=I^2. All proof steps are shorter than 2000 characters. The only substantial general calculation has been isolated into the new statement-only lemma rather than concealed in an elementary step.

I tested the new formula for r=0, m=1, r=1,m=2 and r=2,m=2 (four assignments, with the two mixed assignments in their inherited order). For the item I checked C=k (d=0), the additive group polynomial algebra, and G_m with nonprimitive coordinate t-1. In characteristic p, k[x]/(x^p) with additive coproduct satisfies the result for n<p, while degree p has a vanishing factorial and is correctly excluded from the basis claim. Annihilation does not require this factorial hypothesis. These checks also explain why the printed global derivative identity must not be used. I checked B--E: no elementary auxiliary nodes, no exact existing or Mathlib substitute, no new proof inside a statement-only node, no weakened hypotheses, no cycles through the parent, and precise statements for every citation. The source uses Milne, not any forbidden SGA route. No Lean file was written or compiled.

## What remains

The single new lemma remains unsplit as required for a one-level split. No part of the assigned item's proof is left unfinished. The required server dry run exited 0 with OK (not pushed), preflight passed, at 36fdea9abf6. It ran the maintainer preflight including check_dag and review_split. A subsequent dry run verifies the expanded convolution citation excerpt and this recorded result before pushing.
