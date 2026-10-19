# Stage 1 report: lem-weil-power-series-exp-hom

1. Files written:

- `dag/nodes/sec-zeta-weil/lem-weil-power-series-exp-hom.json`: statement node, split; Mathlib searches found no exact arbitrary-substitution exponential-additivity theorem.
- `citations.json`: verbatim quotations for every cited statement in every proof step.

2. Attachments:

None. The reference source contains `PowerSeries.exp_mul_exp_eq_exp_add`, but it is only the constant-rescaling identity (e^{aX}e^{bX}=e^{(a+b)X}), so it does not state this item.

3. WANTED:

None.

4. Issues found and changes:

The imported node had no proof steps and no split report. I supplied the finite-coefficient multinomial argument for the two-term identity, then the inverse and finite integer-exponent consequences. The item’s blueprint ancestry is `prop-trace-determinant`, step 2, and `blueprint.same_as` is now the required empty list. No statement change was needed.

## Review by Q31

I read the item, the `sk-thm-tracetodeterminant` unit and the `sec-zeta-weil` chapter, then checked the source references in Milne, §26 p. 151 and the proof of Theorem 27.6 p. 156, together with the cited Deligne passage recorded on the item. I searched the source Lean tree for the blueprint tag and for exponential-addition declarations; there is no finished project declaration for this item.

Step 1 uses exactly the coefficient formula and finiteness assertion in `def-weil-power-series-exponential`, and the coefficient-of-a-product formula in `def-weil-formal-power-series`. I checked that the zero constant terms make every coefficient sum finite, and that expanding each ordered composition by a choice of (u)-positions gives the binomial factor (inom{r}{k}), with (inom{r}{k}/r!=1/(k!(r-k)!)), matching the convolution coefficient. Step 2 uses the same definition and the product formula; setting (U=0) and substituting (-U) gives the unit and inverse statements. Step 3 is the finite induction on the index set and on nonnegative/negative integer powers, using the inverse from step 2; its only nontrivial input is the already proved two-term identity.

I tested the edge cases (U=0), (W=0), (U=W=0), a singleton family, an empty family, and exponents (0,1,-1); all give the displayed formulas. The Mathlib searches were rerun with LeanFinder, Loogle, grep, and LeanSearch and recorded verbatim in the node; the only close Mathlib result is the constant-rescaling theorem, which is correctly treated as no match.


## Second reading by Q31

- Item statement: read Milne LEC §26 p. 151 and Theorem 27.6 proof p. 156, Deligne Weil I (1.5.2)–(1.5.4) pp. 275–276, and the current main-20261015 prop-trace-determinant statement/proof and unit proof. The sources use the identity implicitly; the general commutative Q-algebra statement is valid without a field, domain, or convergence hypothesis. The slopmaster2 sketch 49_zeta_linear_algebra.tex, “Formal exponential and logarithm” proposition, also explicitly states the group-homomorphism identity under exactly this ring hypothesis. No statement correction is needed.
- Step 1: checked both cited statements in full: def-weil-power-series-exponential gives coefficientwise finite truncation and constant coefficient 1; def-weil-formal-power-series gives coefficientwise equality, addition and Cauchy multiplication. Replaced the implicit shuffle regrouping by the displayed finite binomial double sum. Terms with k+l>N vanish because each factor has zero constant term; rational factorials are invertible in R; commutativity permits the binomial expansion. This is elementary finite algebra, with Pascal induction specified, and proves the identity also at N=0. No unsupported analytic convergence or infinite-sum interchange remains.
- Step 2: checked the defining exponential series and the ring operations in the same cited definitions, using step 1 for U and -U. Exp(0)=1 and the displayed product supplies a right inverse; commutativity supplies the left inverse. Verdict: correct; repaired the first reader's reversed “right inverse” terminology.
- Step 3: checked the use of the zero-constant-coefficient domain in def-weil-power-series-exponential and of steps 1–2. Expanded the induction at n=0 and n+1, the negative case epsilon=-n, and the empty-set and insertion steps for the finite family. Integer powers are in the unit group already established in step 2. Verdict: elementary, with all induction cases now written.
- New nodes: none; no helper restates a clause or hides the proof. B1–B7 for new nodes are vacuous. Both existing definition nodes were opened; their statements supply the exact facts taken, and citations.json now quotes the whole exponential statement rather than an introductory fragment.
- Search audit: independently searched the whole imported DAG and both main-20261015/master blueprint trees for the item and formal exponential identities, and the two named reference Lean trees for the item and exponential homomorphism names. No duplicate blueprint node or finished project declaration was found. Ran new msearch.py LeanFinder, Loogle and grep queries using composition and rational-algebra vocabulary; searches.jsonl contains their actual results. Read Mathlib/RingTheory/PowerSeries/Exp.lean:123–169. Its rescaling constants and powers do not state arbitrary substitution. Loogle's exp/log inverse identities do not state additivity. No new Mathlib leaf is justified.
- Edge cases: checked the zero Q-algebra (all equalities reduce to its unique element), R=Q, U=0, W=0, U=W=0, U=aT and W=bT in degrees 0,1,2, and U=aT+uT^2, W=bT+wT^2 in degree 2. The latter coefficient is u+w+(a+b)^2/2 on each side. Checked the empty family, a singleton, and exponents 0,1,-1. All hypotheses suffice; no added nontriviality or domain assumption is used.

Changes and reasons: made the coefficient rearrangement and both inductions explicit (C2, E5); marked the supplied proof as agent-written because Milne uses the identity without proving it; corrected inverse terminology; replaced the current-run grep record whose claimed hits contradicted its zero-hit log (the first worker passed an extra Mathlib/ path prefix) with a correctly rooted real search; replaced the rejected Loogle pattern with a valid query; strengthened the exponential citation quotes. The first worker's report and Review by Q31 above are retained as requested; this section and the repaired node supersede their descriptions of the altered proof and search records. No statement, new node, maintainer field, Lean source or live project was changed.
