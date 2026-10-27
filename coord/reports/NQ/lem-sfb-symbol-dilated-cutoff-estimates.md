# Report: lem-sfb-symbol-dilated-cutoff-estimates

1. Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-symbol-dilated-cutoff-estimates.json`: unchanged statement, five-step proof, status split.
- `dag/nodes/sec-six-functors-basics/lem-sfb-symbol-cutoff-scaled-derivatives.json`: statement-only cutoff derivative bound and annular support; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-symbol-product-derivative-bound.json`: statement-only general mixed Leibniz formula for a scalar frequency multiplier and a smooth matrix function; no Mathlib match.
- `citations.json`: one verbatim statement quotation for each step/node citation.

2. Attachments: none. Searches of `lean/WeilConjectures` for the blueprint id and for pseudodifferential, dilated-cutoff and symbol-seminorm terminology gave no declaration for this item. No Lean was written or compiled.

3. WANTED: Demailly, *Differential and pseudodifferential operators on manifolds*, §3.6–3.7, printed pp.7–8, https://www-fourier.univ-grenoble-alpes.fr/~demailly/analytic_geometry_2019/pseudodiff.pdf, for this item and both new nodes. This is distinct from the missing local `literature/demailly-hodge-ams.pdf`. I read the online source, including its scaled derivative calculation and ensuing Leibniz sum. The quantitative reformulation is marked agent-written because the document is not present locally. Neither SGA nor Stacks is a source for this elementary real-analytic calculation; no Stacks tag was invented.

4. The item had no proof. Its statement is correct and was preserved verbatim. An initial draft incorrectly treated the Mathlib full iterated-derivative norm bound as sufficient for the mixed-partial allocation; that was corrected before delivery. The final new node states the exact mixed formula needed, with its own arbitrary dimensions and functions, rather than a clause of the item's symbol estimate. The source's original estimate gains one symbol order using a small inverse radius; the final argument tracks the annulus and proves the stated estimate for all integer t≥s without an order-dependent constant.

5. Unfinished work: both new nodes intentionally remain unsplit and contain only their complete statements. Their future proofs are described below for handoff, outside their statements.

## Searches and blueprint

I read GOAL.md, the three levels in SETUP.md, the chapter and unit records, and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` unit and direct-image proof. The inherited ancestor has `blueprint.from.node = null`; `blueprint_refs.py ancestor` confirms that value. I preserve the inherited via list and give the exact supporting analytic place. Searches of the whole DAG statements/titles and blueprint for Leibniz, cutoff, partial derivatives, symbol, linear precomposition and bounded continuous functions found no existing node stating either new lemma. The current blueprint's direct-image proof has no independent analytic cutoff lemma. No unit statement or route was changed.

All searches were actually run through msearch.py and their returned hits read. The search log preserves the original tool records. Queries initially run under the prospective child ids produced their logs in the corresponding tool-created directories; their records were appended verbatim to this delivery's log. Further product-formula searches include `iteratedDeriv_mul`, `iteratedDerivWithin_smul`, `norm_iteratedFDeriv_smul_le`, and the bounds for a bilinear map; I read `ContDiff/Bounds.lean:203–255`, `ContDiff/Basic.lean:461–467`, and the one-variable product declarations. A second wording of the mixed product question was searched. The full Fréchet norm estimates bound all directions together and do not give the separate x and frequency orders; the one-variable formula requires a genuine multivariable iteration. Consequently neither is an exact match or a one-line specialization of the final mixed formula. The cutoff searches found bump existence/support and derivative-support results; these do not give the bound for an arbitrary fixed theta at every dilation. I retained the old item's searches and added the actual new search results.

## Not duplicates

lem-sfb-symbol-cutoff-scaled-derivatives vs lem-sfb-euclidean-smooth-bump: the existing node constructs a bump with prescribed support; the new one bounds derivatives of every dilation of an arbitrary given high-frequency cutoff and specifies positive-derivative annular support.

lem-sfb-symbol-cutoff-scaled-derivatives vs lem-sfb-compact-continuous-norm-bound: the existing node bounds a continuous Euclidean function on a compact set; it does not give derivative scaling or the support of scaled derivatives. It is a possible input for the future cutoff proof.

lem-sfb-symbol-product-derivative-bound vs lem-sfb-lie-derivation-iterate-binomial: the existing Lie-module algebra statement concerns iterates of a single Lie derivation; the new node concerns smooth Euclidean functions, mixed coordinate partials, scalar multiplication of rectangular matrices, smoothness and the resulting matrix norm bound.

Neither child states a symbol-order estimate or introduces S^s, s, t or P_{s,n}. They are genuine generic calculus inputs, not restatements of any clause of the item. There are no shared Stacks tags.

## Review by NQ

For the item I read Demailly §3.6–3.7, printed pp.7–8, particularly the scaling identity for cutoff derivatives and the Leibniz sum immediately following it. For the cutoff child I checked the same displayed scaling identity, together with the source's assertion that positive derivatives vanish outside the radius-two ball; its precise statement also records vanishing in the radius-one ball. A future proof can bound the finitely many continuous derivatives on the closed annulus, use ∂^γ(theta(ξ/R))=R^{-|γ|}(∂^γ theta)(ξ/R), and use (1+R)/R≤2. The zeroth derivative is separately bounded since theta=1 outside a ball. Boundary values follow by continuity; no positivity or upper bound by one is assumed for theta. These facts are a generic calculus lemma, not the symbol estimate being split.

For the product child I read the Leibniz formulas in Demailly §3.6 and §3.7 and the Mathlib candidates above. Its future argument iterates the coordinate product rule, combining duplicate terms with Pascal's identity in each coordinate. It then takes the norm of the finite sum and uses |c|‖A‖ for a real scalar times a complex matrix. There is no symbol hypothesis in this lemma. All dimensions may be zero and the sum for beta=0 has one term. No proof text is left inside either unsplit child.

Step 1 only fixes n and d=t−s and observes that the index set for the maximum is finite. Step 2 cites the cutoff child: I checked its statement gives both the global A_n(1+R)^{-|γ|} bound and the separate k=0 and k>0 support clauses actually used later. Step 3 cites the product child: its statement gives smoothness, the exact mixed formula and the norm inequality, under the available smoothness hypotheses, after taking u=v=m and h=theta_R. It never uses an operator-norm bound as if it were a mixed formula.

Step 4 cites the cutoff child and the symbol definition, whose statement I opened. The item's own stronger uniform definition of P_{s,n}, rather than the definition node's merely locally uniform x bounds, supplies M. With k=|γ| and d≥0, the weighted term is A_n M (1+R)^{-k}(1+|ξ|)^{k-d}. For k=0, only the lower support bound |ξ|≥R is used. For k>0, R≤|ξ|≤2R gives separately the negative exponent −d and the positive exponent k. This avoids assuming the exponent k−d has one sign. The two inequalities give 2^n A_n M (1+R)^{-d}. The explicit binomial sum is ≤2^n, so C_n=4^n A_n works independently of both symbol orders and of matrix dimensions. Step 5 takes suprema and the finite maximum; smoothness was already supplied by step 3. Repeating for every n gives membership in S^t.

I tested n=0, R=1, t=s, arbitrarily large t−s, negative s and t, p=0 or q=0, vanishing symbols, and both radii |ξ|=R,2R. None requires an additional hypothesis. In particular theta need not take values in [0,1]. I corrected an initial unnecessary R^{-k} substitution in the assembly to use exactly the child's (1+R)^{-k} statement. All proof steps are below 2000 characters; the only non-elementary facts have their precise cited statements and verbatim quotations. Dependencies equal the union of uses. I checked B–E: complete standalone child statements, correct single TeX escaping, actual searches, no new-node proof sketches, no relabelled clauses, no circular use, exact citation content, and all hypotheses in force. No statement dispute remains.
