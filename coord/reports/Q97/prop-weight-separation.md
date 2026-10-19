# Q97 stage-1 report: prop-weight-separation

## Files written

- `dag/nodes/sec-zeta-weil/prop-weight-separation.json`: the item, marked `split`, with four proof steps.
- `dag/nodes/sec-zeta-weil/lem-zeta-coprime-no-common-root.json`: Mathlib leaf for `Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed`.
- `dag/nodes/sec-zeta-weil/lem-zeta-coprime-product.json`: Mathlib leaf for `IsCoprime.prod_left`.
- `citations.json`: verbatim node quotations for every cited node in every proof step.

## Attachments

None. I searched the project source for `prop-weight-separation` and for the root-separation declarations; no sorry-free declaration under `WeilConjectures/` states this item exactly. The existing `Polynomial.eq_of_isPureOfWeight_of_prod_mul_eq` theorem is a different complex-polynomial uniqueness theorem and is not an attachment.

## WANTED

None.

## Not duplicates

- `lem-zeta-coprime-no-common-root` vs `def-weil-coprime-polynomials`: the existing node defines coprimality by a Bézout identity; the new node is the algebraically closed root criterion for that predicate.
- `lem-zeta-coprime-product` vs `def-weil-coprime-polynomials`: the existing node defines coprimality; the new node states closure under a finite product of pairwise-coprime factors.
- `lem-zeta-coprime-no-common-root` vs `lem-weil-reciprocal-root-factorization`: the existing node factors one normalized polynomial and records reciprocal-root multiplicities; the new node characterizes coprimality of two polynomials by common evaluation zeros.

## What was checked and changed

The item statement was compared with `literature/blueprint/master/blueprint/sec-zeta-weil/sk-prop-separation/prop-weight-separation.md` (node order 2900) and with the corresponding `main-20261015` node. They agree, so I kept every hypothesis and conclusion. The imported `stmt_deps` omitted the explicit ordinary-root, parity-product, and point-count-zeta notions used in the statement and included `def-weil-punctual-weights`, which the statement does not use; I corrected that dependency list. The proof follows the unit route in `dag/units/sk-prop-separation.json` and the single paragraph in `prop-weight-separation.proof.md`.

The proof now has four steps. Step 1 fixes a possible common ordinary root, inverts it using the ordinary/reciprocal-root definition, and uses the assumed absolute-value condition plus `q=p^a>1` to force equal indices. It then applies the algebraically closed root criterion. Step 2 forms the odd and even products, applies finite-product coprimality (using the symmetry of the Bézout predicate when reversing factors), and obtains constant coefficient one from the smooth-proper family definition. Step 3 groups the assumed alternating trace-to-determinant product into `N_ell/D_ell`; the existing power-series unit lemma supplies the formal-series inverse because `D_ell(0)=1`. Step 4 uses the existing reciprocal-root factorization node twice: its factorization gives the multiset union for a product, and its uniqueness clause preserves multiplicities. The distinct absolute values then select precisely the weight- `i` submultiset in the matching parity product.

I ran the required Mathlib searches for each new node with `msearch.py`: LeanFinder, Loogle, grep, and LeanSearch. The root criterion was found at `Mathlib/FieldTheory/IsAlgClosed/Basic.lean:251`; the product theorem was found at `Mathlib/RingTheory/Coprime/Lemmas.lean:76`. Their search records and exact `mathlib_match` fields are in the node files.

## Review by Q97

I reread the item, both new nodes, the unit record, the chapter record, the master and current blueprint proof files, and every existing node cited by the four steps. The item’s finite-field, geometric, cohomological-family, root, parity-product, and zeta hypotheses match their cited definitions. The root criterion node says exactly that coprimality is equivalent to the absence of a common evaluation zero over an algebraically closed extension, and the product node says exactly that a finite product of factors coprime to one element remains coprime to it. The reciprocal-root factorization node explicitly supplies nonzero roots, linear factorization, and uniqueness up to reordering with algebraic multiplicity; those are the only facts used in the final multiset step. The power-series unit node explicitly supplies invertibility from constant coefficient one. Every citation quote in `citations.json` is a verbatim substring of its node’s statement.

I checked the hypotheses at each use: the root criterion is applied over `k = Q_l` and `K = Q_lbar`; the product lemma is applied to finite odd/even index sets; the smooth-proper family supplies `P_{i,l}(0)=1`; and the formal-series inverse is applied over the field `Q_l` with denominator constant term one. Edge cases tested were `d=0`, empty odd or even index sets, constant factors equal to one, and repeated roots within a single factor. No statement dispute, source error, route change, cycle, SGA citation, or unfinished proof remains.

## Unfinished

None. No Lean file was written and no compiler or build tool was run, as required for this stage-1 worker.
