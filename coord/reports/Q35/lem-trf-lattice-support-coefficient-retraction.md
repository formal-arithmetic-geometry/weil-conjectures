# Stage-1 delivery: lem-trf-lattice-support-coefficient-retraction

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-lattice-support-coefficient-retraction.json`: statement, split; no exact Mathlib match. The statement and its single statement dependency are unchanged. Five elementary proof steps use the existing power-series definition and subgroup arithmetic. All other existing metadata is preserved.
- `citations.json`: one verbatim citation for each node used in each proof step.
- `searches.jsonl`: seven actual Q35 search calls, retained as logged by msearch.py. Earlier Q69 searches in the imported item are preserved, not represented as fresh calls.
- `report.md`: this report. `prepare.py` is an item-local preparation script, not a delivered node.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the exact blueprint tag and item id, `lattice`, `retraction`, exponent-support and subgroup/power-series phrases under the actual project `lean/WeilConjectures/`. No declaration states the item. Unrelated cohomological coefficient and lattice statements do not attach this commutative-algebra result.

## WANTED

None for this proof. The parent's unavailable Kato reference is not used: no completed-monoid comparison, Cohen structure theorem or log-geometry fact is needed here.

## What was wrong or incomplete

The item was statement-only. The original source already correctly warns that ILO supplies motivation rather than this independent algebra statement; I retained that distinction. Read ILO Expose VI 1.6(i)--(ii), printed p.70, PDF p.76: it gives completed monoid models, not this coefficient retraction. The proof is therefore explicitly agent algebra, not attributed to ILO as a theorem or copied proof. There is no statement dispute and no changed hypothesis or conclusion.

Read `dag/chapters/sec-trace-formula.json`, `dag/units/sk-i-curve-zero.json`, the main-20261015 unit statement/proof and `lem-trf-local-term-locality.proof.md`, together with the current parent `lem-trf-completed-monoid-support-projection`. This item is auxiliary algebra on that parent's fixed ancestry, not the unit's key statement; no unit realization fields are changed. Its result supplies exactly the parent's coefficient projection and retraction clause.

## Searches and candidate decisions

All fresh Mathlib searches used the required msearch command with group Q35 and this item id. Both semantic phrasings, Loogle, LeanSearch and three grep patterns are retained exactly in the node and search log. Read the hits and local candidate statements: `MvPowerSeries.coeff` at Basic.lean:137 is L-linear evaluation of a single coefficient; `toSubring` at Basic.lean:579 changes the coefficient ring, not exponent support; `weightedHomogeneousComponent` at Order.lean:592 has a natural-number weight and degree, not an arbitrary subgroup condition; `homogeneousComponent_mul_of_le_order` at Order.lean:734 has lower-order hypotheses and only a lowest-degree product conclusion; `truncFinset` at Trunc.lean:74 has a finite index set and polynomial target. Restricted.lean:31,98 concerns decay over normed rings. `MvPolynomial.restrictSupport` at Basic.lean:93 and `MvPolynomial.supported` at Algebra/MvPolynomial/Supported.lean:40 concern polynomials, with the latter selecting variables. None specializes in one line to the whole item for arbitrary L and subgroup M. In particular M=2Z already requires an infinite exponent filter unavailable from natural-number degree-zero selection.

Whole-DAG searches for subgroup-supported series and the lattice-support intersection returned this item, its completion-comparison parent and the toric normality/class-group applications. The latter statements were opened: they assert normality and boundary-class injectivity, not this lemma. Blueprint searches for `subgroup support` returned zero; `subgroup` and `power series` returned unrelated group-theoretic and univariate-series nodes. Thus `same_as` remains empty.

## Not duplicates

No new nodes are introduced. The parent is a completed-monoid comparison with topological hypotheses, while this item is its separate coefficient-filter tool for arbitrary L; no parent result is used in this proof.

## Review by Q35

I read delivery-errors B--E, including the merged duplicate of those sections, against the actual statement and all five steps. No new nodes need standalone hypotheses, sources, searches or duplicate comparisons. The existing Mathlib definition node was opened and its statement says exactly that a power series is a coefficient family, with coefficientwise addition, the finite Cauchy-product sum and constants r times the zero monomial. It therefore supplies all the facts taken from it, not merely a name for an unspecified ring. The citations file records that statement verbatim for steps 2--4.

Step 1 uses no cited lemma: closure of a subgroup under zero, addition and subtraction proves the precise equivalence needed. Nonnegativity is already given for both indices, so membership in M and membership in Q coincide for those vectors. No saturation or primitivity of M is assumed or used.

Step 2 uses the existing power-series definition for addition, negatives, constants and convolution. If an exponent outside Q is a sum of two indices in Q it contradicts subgroup closure; hence every coefficient term of a product outside Q is zero. This establishes the subalgebra directly, including the constants and additive inverses. No assertion about formal completion is imported.

Step 3 uses the same coefficient-family definition to construct the filtered series and prove its support, additivity and identity on A_Q, coefficient by coefficient. No existence theorem for an infinite sum is being hidden: the object is a family from the outset.

Step 4 uses precisely the finite convolution formula in that definition. After terms with u outside Q vanish, Step 1 replaces the indicator of e in Q with the indicator of v in Q for every pair u+v=e. Thus the displayed finite sums agree term by term and equality of families proves module compatibility. This is a few-line coefficient calculation, not an omitted theorem about graded rings or infinite decompositions. In particular no direct-sum grading of arbitrary formal series is assumed.

Step 5 gives the transport argument explicitly: the image equality gives existence of a preimage of pi(b), injectivity gives its uniqueness, and applying phi reduces additivity, scalar compatibility, the left-inverse identity and uniqueness of rho to the already established identities. The map phi is an L-algebra homomorphism and hence preserves addition and products; phi(t) is in A_Q by the image assumption, which is exactly the hypothesis of Step 4. The R-action is explicitly t dot b=phi(t)b. No comparison lemma or unstated isomorphism is invoked. These steps are elementary arguments from the definition and the given map axioms; each is under 2000 characters.

I tested r=0, where the single exponent is zero and pi is the identity; M={0}, where pi takes the constant term; M=Z^r, where it is the identity; and M=2Z inside Z, where the even-part projection is module-linear over even series. The zero coefficient ring also causes no difficulty, since the proof never cancels a ring element or assumes 0 differs from 1. The projection is not claimed to be multiplicative: for M=2Z and a=b=X over Z, pi(ab)=X^2 but pi(a)pi(b)=0. This checks that Step 4 uses a in A_Q essentially, rather than silently asserting a stronger false property. For M=Z(1,-1) in rank two, Q={0}, so the same constant-term argument applies without any finite-generation reasoning.

The only proof dependency is the existing Mathlib definition leaf; the statement dependency is unchanged. There is no edge to the parent or any descendant and hence no new cycle or off-unit statement tool use. I introduced no SGA citation, modified no repository or launcher file, ran no git command in the read repository, and wrote/compiled no Lean.

## Unfinished work

None in this stage-1 split. The first server dry run exited successfully at ca8e56e5747 with preflight passed. Corrected the report's homogeneous-product candidate line from 731 to 734 after checking the numbered source; the final dry run and push follow this report update.
