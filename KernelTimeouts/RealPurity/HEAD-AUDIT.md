# RealPurity head audit

## Case and conversion

- Case ID: `RealPurity`; conversion ID: `RPU-hreal-exact-v1`.
- Declaration: `IsReal.exists_isPunctuallyPureOfWeight_cokernel_detWeight`, from `e2d8b540cba`; module `WeilSheaf/RealPurity`.
- Lean/Mathlib: 4.35.0; baseline `Before.lean` at dataset revision `7118b5fe0097`.
- Site: `exact h` in the local `hreal' : W.IsReal l P.obj.ρ ι` proof, after rewriting `hreal x n` through stalk polynomial equality and rewriting the target through `WeilGroup.localPolynomial`. Local context includes `W`, `P`, `G`, `x`, `n`, a stalk equivalence `f`, its Frobenius compatibility `hf`, and proof `h`.
- Original elaborated expressions preserved: **yes**. `probes/HeadAudit.lean` reads `inferType h` and the goal before normalization. Both pretty-print as the same `starRingEnd ℂ (ι (...coeff n)) = ι (...coeff n)` proposition.
- Normal Kernel checking enabled. Historical Before: deterministic timeout at 58.94 s wall and 5,590,352 KB RSS. Type-only: 4.70 s. `AfterHRealSorry.lean`, which keeps `exact h` and replaces later proof work, still times out at 58.94 s. `HRealFinalSorry.lean`, which keeps both rewrites and replaces `exact h`, completes in 7.30 s. Isolated heartbeat count and CPU time for the timeout were not retained.

## Head audit

| Side | Outer constructor/head | Arguments and metadata | First divergent path |
|---|---|---|---|
| Actual, `h` type | `Expr.app`, `Eq.{1}` | three arguments; type is syntactically identical `Complex`; inductive head | `Eq` side -> `DFunLike.coe` (three layers on left) -> `Polynomial.coeff` -> `Polynomial.reverse` -> `CommSemiring.toSemiring` -> `CommRing.toCommSemiring` -> `Field.toCommRing` |
| Expected, goal | same `Eq` head, universe, and arity | corresponding coercion/coefficient/reverse heads agree | corresponding leaf is `AlgebraicClosure.instCommRing` |

The leaf difference also occurs on the right equality side. `Field.toCommRing` is an abbrev definition at universe `[0]`, with two applied arguments and a lambda as immediate body shape. `AlgebraicClosure.instCommRing` is a regular definition at universe `[0]`, height 29, also with two applied arguments and a lambda as immediate body shape. The surrounding `Polynomial.reverse` coefficient structure is data, not a proof argument. There is no raw `Expr.proj`, `letE`, or recursor on the first divergent path.

The shared `Eq`/coercion/polynomial heads offer an argument-comparison route, but their concrete semiring inheritance paths differ. The installed hint policy favors exposing an abbrev over a regular definition when those heads must be reconciled; one-step expansion of `Field.toCommRing` exposes a lambda building the commutative-ring structure from a field. This is a metadata-based prediction, not an observed Kernel step. The subsequent cost might lie in that instance reconciliation or in the larger polynomial/coercion context it exposes.

## Hypothesis tests

| Hypothesis | Status | Experiment and result |
|---|---|---|
| H1: hint/order | **Plausible, unconfirmed.** | H1.3 records abbrev `Field.toCommRing` versus regular height-29 `AlgebraicClosure.instCommRing`. No valid same-body hint-kind control was obtained. |
| H2: same-head argument | **Observed structurally.** | The first differing argument is a ring-instance leaf beneath matching `Eq`, coercion, coefficient, and reverse heads. A one-leaf replacement preserving the exact proof was not achieved. |
| H3: projection | **Not supported at the first divergence.** | The raw path consists of applications, including structure-to-structure constants, without `Expr.proj`. |
| H4: dependent binder | **Not applicable.** | The hotspot is the final proof-term type versus goal conversion, not an application binder. |
| H5: instance paths | **Plausible, unconfirmed.** | H5.1 finds the exact stored inheritance paths. No valid local-instance control was found that changed only this leaf while preserving both elaborated equality sides. |
| H6: proof proposition types | **Tested; confirmed as the conversion site.** | H6.1 compares `h`'s proposition with the goal. Replacing only `exact h` gives a 7.30 s diagnostic prefix, while keeping it and removing subsequent work still times out. The first raw mismatch is in the propositions, not proof bodies. |
| H7: non-delta reduction | **Not established.** | Initial unequal heads are definitions. Earlier isolated diagnostics had small unfold counts; those counters do not identify the internal expensive step. |
| H8: context/order | **Unresolved.** | The old in-situ conversion is reproducibly slow. There is no same-expression isolated control proving a cache or order effect. |

`PolynomialTransport.lean` uses a checked equality of the two local polynomials, transports the coefficient equality, and finishes `hreal'` without `exact h`; the diagnostic file completes in 7.10 s (5.86 + 1.19 s CPU, 3,994,852 KB RSS). Its enclosing theorem ends with `sorry` only after that local proof, so this measurement checks the local proof but is not a proof of the full theorem. The current `Master.lean` fully checks in 6.10 s. These controls change the proof construction, not solely the ring-instance leaf; they establish a cheap alternate route without isolating H1 or H5.

## Causal record

- Initial pair: identical-looking equality propositions with a first raw mismatch at two concrete commutative-ring instance paths inside `Polynomial.reverse`.
- Potential cheap route: compare the common equality and polynomial heads argument by argument.
- Why it does not close syntactically: the stored `Field.toCommRing` and `AlgebraicClosure.instCommRing` applications differ.
- Predicted reduction: expose the abbrev-side ring structure, then reconcile the regular algebraic-closure instance inside the dependent polynomial operations. Exact Kernel order remains unobserved.
- Why potentially costly: this path repeats on both equality sides, within coercion and polynomial operations over `PadicAlgCl l`. The baseline reaches the heartbeat timeout, but no control isolates this leaf's share of the cost.
- Control: a direct polynomial-equality transport completes the same `hreal'` obligation cheaply. The source proof route changes, so it cannot establish that aligning only the instance would suffice.
- Verdict: **unresolved** between an unfavorable concrete-instance path and a more general expensive proof-proposition conversion. The original pair requires reconciliation of distinct instance representations; the reason that reconciliation becomes a timeout remains open.

## Evidence and confidence

Observed: exact preserved proposition pair, first instance leaf and hints, the `exact h` boundary, and a checked alternate local proof. Interpretation: H6 identifies the expensive conversion site; H1/H2/H5 are **plausible** explanations of its cost. Overall evidence level for the causal explanation: **plausible**; the site localization is confirmed. The historical `After.lean` also times out on this toolchain, so its changes are not credited with the current Master's speed.
