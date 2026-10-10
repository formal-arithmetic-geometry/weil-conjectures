# lem-weil-pbc-cyclic-extension-cocycle

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-cyclic-extension-cocycle.json`: split the item into five explicit module calculations. No new nodes were needed.

## Attachments

None. A search of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` and `Comparator/` by item ID, Stacks labels 05ED and 05EE, and the extension/cocycle concepts found no declaration stating this item. Its audit state remains `none`.

## WANTED

None.

## Source and statement check

Read Stacks More on Algebra, Lemmas 05ED (`lemma-naive-Koszul-complex`, more-algebra.tex:24394) and 05EE (`lemma-explicit-ext`, more-algebra.tex:24413), and Homology, Section 010I (`section-extensions`, homology.tex:1260). The tags and labels were checked against `tags/tags`. The node makes the kernel of the map from the cycle group to `Hom(K,P)` explicit as extensions and gives the change-of-lift relation. No hypothesis or conclusion needed correction. The cited definition nodes state the free, quotient and direct-sum modules and short exact sequences used in the proof.

For the edge cases `t=1`, `J=0`, and `J=A`, the relation criterion and quotient formulas still give exact sequences; no regularity or injectivity of the generators is assumed. Steps 1-5 write out the coefficient relation, kernel/image, inverse, and boundary calculations. They use only the cited definitions and elementary module algebra, with no uncited external result.

## Verification and remaining work

`python3 tools/review_split.py lem-weil-pbc-cyclic-extension-cocycle`: PASS, zero new nodes. `python3 tools/check_dag.py`: zero cycles and zero self-loops; nonzero exit from seven unrelated reach flags and eleven unrelated unit-route edges involving `thm-constructible-serre`. No Lean was written or built. Nothing remains on this item for the worker.

## Review by C1

I read More on Algebra Lemma 05ED (`lemma-naive-Koszul-complex`) and Lemma 05EE (`lemma-explicit-ext`) in `more-algebra.tex`, and the extension interpretation in Homology Section 010I. The unchanged item makes the extension-class calculation of 05EE explicit for a chosen tuple of generators and a lift of `1`; it assumes only a commutative ring, a finite nonempty tuple, and an arbitrary module. I opened the four cited definition nodes for free modules, quotient modules, direct sums, and short exact sequences. They say precisely what the five steps use; the DAG and blueprint searches found no duplicate, and the read-only Lean source has no exact declaration for this item. There are no new nodes, so B1-B7 has no new-node instance.

For step 1, the relations `f_i e_j - f_j e_i` map to zero both under `e_i -> f_i` and under `e_i -> x_i` exactly when `x` is a Koszul cycle. A representative of a kernel element has coefficient relation `sum a_i f_i = 0`, giving the stated admissibility test. In step 2, adding the generators `(x_i,-f_i)` changes `(p,a)` to `(p+sum b_i x_i,0)` when `a` is in `J`; admissibility is exactly what makes the inclusion of `P` injective. In steps 3-4, exactness of the given extension supplies unique `x_i`, and a lift `e` of `1` gives an inverse map on the quotient: any `y` differs from `a e` by `j(p)`, while a kernel pair is a combination of the defining relations. These are the elementary calculations behind the injection of extension classes in 05EE, with no regular-sequence hypothesis.

I checked the sign in step 5: `h_m(p,a)=(p+am,a)` takes `(x_i,-f_i)` to `(x_i-f_i m,-f_i)` and `h_{-m}` is its inverse. For `t=1`, `J=0`, and `J=A`, the same quotient and exactness calculations work; no generator is assumed nonzero or a nonzerodivisor. All facts beyond those elementary calculations are cited through the definition nodes. I found no cycle or hidden hypothesis and sent no correction to the worker. The final item and report were checked against delivery-errors A-F.
