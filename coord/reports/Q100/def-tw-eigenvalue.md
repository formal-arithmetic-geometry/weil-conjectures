# Stage-1 report: def-tw-eigenvalue

## Files written

- `dag/nodes/sec-purity-real-sheaves/def-tw-eigenvalue.json`: definition; split using four existing statement dependencies; no complete Mathlib match.
- `citations.json`: empty list, because the item is a definition with no proof steps.
- `report.md`: this report. The mandatory search command generated `searches.jsonl`; its queries and results are retained verbatim by tool/query with truthful verdicts in the item.

New nodes: 0. Mathlib leaves: 0. No Lean files, compiler, Lake, live project writes, or direct git operations were used.

## Attachments

None for this item. Searching all project Lean under `WeilConjectures/` for the exact id and eigenvalue/weight terminology found no declaration stating the imported definition. `AlgebraicGeometry.WeilGroup.frobeniusWeight` at `WeilConjectures/EtaleCohomology/Purity/RealSheaves/Weights.lean:60` defines the numeric logarithmic weight relative to a chosen complex embedding; it does not supply every clause of this item. `FrobeniusModule.IsPureOfWeight` at `WeilConjectures/ZetaLinearAlgebra/FrobeniusModule.lean:88` quantifies over all eigenvalues of a finite-dimensional abstract Frobenius module, whereas this item defines the absolute-value notation and weight of a single global cohomological eigenvalue. Both support the corrected convention, but neither is an exact attachment. Their existing DAG notions are left intact.

## WANTED

None. Deligne's Weil II PDF is available locally and was read at (0.2), p. 144 and (1.2.1), (1.2.6), pp. 153–154. No prohibited SGA source is used.

## Source error — STATEMENT-DISPUTED

The master blueprint and the current main-20261015 copy both ask for the Q_l-adic valuation normalized by v(q)=1 with q=p^r and l different from p. This is impossible: q is an l-adic unit. For the explicit permitted data p=q=2, r=1, l=3, v_3(2)=0 and the usual 3-adic absolute value is |2|_3=1. Rescaling the additive valuation cannot change zero into one, and taking the reciprocal norm still gives 1, not 2. Thus this is not merely a reversed sign. In addition, reciprocal l-adic norms are not absolute values in the usual triangle-inequality sense: for l=3, the reciprocal norm of 1+2 is 3, while those of 1 and 2 are each 1.

I repaired the definition, as the dispatch explicitly requires for disputed statements, to use a fixed field isomorphism iota from Qbar_l to C and |beta|_iota=|iota(beta)|. This is exactly the complex convention in Deligne (1.2.6), the enclosing chapter's `sk-d-real-weights`, and the existing `def-weil-frobenius-module-weights`. I retain the imported integer w and formula q^(w/2), rather than add a real-weight generalization. I label the predicate iota-weight so it cannot be mistaken for purity for every complex embedding, which Deligne (1.2.1) treats separately. No algebraicity over Q or independence from iota is asserted.

The finite-extension norm rule and reciprocal-adic assertions are removed as part of the same correction, not silently accepted as complex norm identities. The title is corrected accordingly. This changes a definition used downstream: the maintainer should record the dispute and reopen any semantic target review that used the old norm. The unit's local characteristic-polynomial identity and conjugacy argument are unaffected; no unit or chapter route is changed.

## Not duplicates

No new node is created, so there are no new/existing duplicate pairs. Whole-DAG key-word searches and whole-blueprint searches for `q-adic absolute value`, `absolute value`, `weight`, and `q^{w/2}` found the related `sk-d-real-weights`, `def-weil-frobenius-module-weights`, and `def-weil-numbers`. The first concerns local stalks and includes reality and polynomials; the second purity/mixedness of entire modules; the third numbers algebraic over Q with all complex conjugates constrained. None is an exact duplicate of this definition's global single-eigenvalue and absolute-value notation. The existing scalar absolute-value and positive-real-power nodes are reused rather than recreated.

## Review by Q100

I read delivery-errors B–E in full and checked this definition against each applicable point. The authoritative correction is Deligne (0.2) and (1.2.6), not a guessed normalization; I also read both blueprint snapshots and the current chapter/unit records. There are no new unsplit statements, no hidden lemma nodes, no proof moved into a child, and no proof steps (hence no long non-elementary steps or proof-step quotation obligations).

I opened every statement dependency. `def-tw-conventions` specifies q=p^r, l different from p, the chosen algebraic closure and coefficient framework; the statement explicitly invokes those conventions. `def-tw-frobenius-action` supplies precisely the Qbar_l-linear cohomology automorphism Phi_X^* on H^i(X,Qbar_l) for a separated finite-type finite-field model and every integer i; I repeat those hypotheses and use that operator rather than a scheme map acting directly on scalars. `def-weil-complex-absolute-value` explicitly defines |z|=sqrt(x^2+y^2), including agreement with the real absolute value; it supplies the absolute value used after iota. `def-weil-real-power` defines x^y for positive real x, and q=p^r>1 checks its domain. Iota is stipulated as a field isomorphism without a continuity assumption; no existence theorem is hidden in that stipulation. Every notion added in the correction is either inline (eigenvector and field isomorphism) or an existing statement dependency. Proof and proof_deps remain empty, so no result is mis-cited as a proof step or used from a cited node's internal proof.

The elementary normalization |q|_iota=q follows because a field homomorphism fixes the integer q and the complex absolute value of the positive real q is q. I tested alpha=1 (weight 0), alpha=q (weight 2), and alpha=q^(-1) (weight -2); all agree with the chosen embedding. Roots of unity map to complex roots of unity, so the intended weight-zero convention is preserved. Zero cannot be an eigenvalue of the automorphism: F(v)=0 implies v=0 by injectivity. In degree with zero cohomology there are no eigenvalues and the definition makes no false existence claim. Iota-dependence is explicit; the definition asserts neither that every eigenvalue has an integer weight nor that a chosen weight is independent of iota.

The Mathlib searches were run only via the prescribed msearch.py command, with two semantic phrasings after the statement correction. I read the returned hits. `Complex.norm_def` is a scalar-norm partial match already covered by an existing node, while eigenvalue and infinite-place hits do not define this predicate. Ordinary padic hits were checked in `PadicNorm.lean:45` and `Complex.lean:92–98`, and confirm that they are unrelated to the corrected convention. Two early grep scopes erroneously repeated the Mathlib prefix and one early Loogle query was invalid; these are explicitly recorded as invalid, not absence evidence, and replaced with correctly scoped searches. No unrun search is recorded. There is no full Mathlib match, and no Mathlib leaf is claimed.

## Unfinished work

None within this stage-1 definition split. Downstream nodes remain unchanged and require the maintainer's normal independent semantic review of the reported source correction.
