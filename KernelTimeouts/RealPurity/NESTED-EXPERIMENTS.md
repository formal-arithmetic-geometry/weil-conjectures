# RealPurity: nested representation audit

Source: `e2d8b540cba`, `WeilSheaf/RealPurity`,
`IsReal.exists_isPunctuallyPureOfWeight_cokernel_detWeight`;
Lean/Mathlib 4.35.0, 200,000 heartbeats. Measurements are reused from
`WORKPLAN-EXPERIMENTS.md`; unchanged fixture links are in `probes/nd/`.
Kernel-only time/heartbeats and separate synthesis time are unavailable.

## Original context and A records

The exact expensive site is `exact h` in `hreal'`, after two polynomial
rewrites. Both proposition sides print as the same complex-number equality,
but under `Polynomial.reverse` / `coeff` each equality side first differs
at `Field.toCommRing` in `h` versus
`AlgebraicClosure.instCommRing` in the goal. Both are concrete ring-instance
paths. After both leaves are aligned, each side next differs at
`Functor.obj` versus local `P` under `LinearMap.charpoly`.
Section-10 fields shared by the rows: instance depth and field count are
the unchanged original sheaf/representation structure; the equality uses
both polynomial sides. Source elaboration reruns in each variant. Explicit
instance terms, synthesis time, Kernel-only time/heartbeats, and same-term
Kernel replay are unavailable. Earlier isolated diagnostics had only small
local unfold counts, so no downstream reduction chain is attributed to
the ring leaf.

| Record | Changed factor | First remaining difference | Kernel result | Wall s | CPU user+sys s | RSS KB | Same site/proof construction | Confidence |
|---|---|---|---|---:|---:|---:|---|---|
| A-RP-0 | original `exact h` | ring path on both equality sides | deterministic timeout | 58.24 | 58.36+1.30 | 5,616,188 | yes | confirmed site |
| A-RP-L | align left ring leaf only | right ring leaf; left object path | deterministic timeout | 58.44 | 58.43+1.27 | 5,618,576 | yes | negative one-side control |
| A-RP-R | align right ring leaf only | left ring leaf; right object path | deterministic timeout | 58.44 | 58.39+1.33 | 5,616,352 | yes | negative one-side control |
| A-RP-B | align both ring leaves | `Functor.obj`/local `P` on both sides | deterministic timeout | 58.44 | 58.39+1.29 | 5,619,680 | yes | confirmed negative ring-path control |
| A-RP-T | transport polynomial equality before coefficient equality | changed proof construction | ok for local proof | 7.10 | 5.86+1.19 | 3,994,852 | no, alternate proof route | transport control only |

`AlignLeftRing`, `AlignRightRing`, and `AlignBothRing` use the same
`exact h`, and their head probes confirm the intended changed expression.
The two-side alignment keeps the theorem obligation and original local
context, but does not make the Kernel conversion cheap. `PolynomialTransport`
checks the local `hreal'` proof and discards later work with a diagnostic
`sorry`; it is not a same-cost-site A variant. `Master.lean` fully checks
in 6.10 s and is a within-case fast control with a different construction.
The historical `After.lean` also times out on this toolchain. No A/A,
B/B, A/B, B/A provider matrix or explicit-instance replay was obtained.

## D: representation provenance

| Role | `h` proposition | `hreal'` goal |
|---|---|---|
| Original declaration | local `hreal x n` rewritten through stalk equivalence | local `W.IsReal l P.obj.ρ ι` goal after local-polynomial rewrite |
| Data | `Polynomial.reverse`/`coeff`, coercions into `Complex` | same coefficient equality |
| Ring path | field inheritance `Field.toCommRing` | algebraic-closure `instCommRing` |
| Object path after ring alignment | functor-object construction | local `P` |
| Proof abstraction | not established at first divergence | not established at first divergence |

The first ring difference occurs on both sides of the equality; aligning
both exposes a later object representation and leaves the timeout. Thus
ring provenance is observed but its causal sufficiency is refuted. The
polynomial transport changes the proof route and cannot isolate the
object path. D confidence: confirmed for the visible sequence, unresolved
for the dominant Kernel cost.

**Evidence level:** below section-12 Level 1 for the ring-instance
hypothesis. The negative A controls are conclusive at the original site;
no B/C or project-level amplification result is available.
