# STRUCTURE EXPOSURE AUDIT

Case: `RealPurity`
Source snapshot: `e2d8b540cba`, `IsReal.exists_isPunctuallyPureOfWeight_cokernel_detWeight`
Lean/Mathlib: 4.35.0, one Lean thread, normal Kernel checking, 200,000 heartbeats

## R1. Exact Kernel cost site and initial mismatch

The exact site is `exact h` in the local `hreal' : W.IsReal l P.obj.ρ ι`
proof, after two polynomial rewrites. The compact printer shows the same
complex equality on both sides, but `pp.explicit` reveals, under
`Polynomial.reverse`/`Polynomial.coeff`,
`Field.toCommRing` in `h` versus `AlgebraicClosure.instCommRing` in the goal.
The mismatch occurs on both equality sides. The original site times out at
58.24--58.94 s (about 5.6 GB RSS); replacing only `exact h` with `sorry` is
7.30 s.

## R2. Candidate exposure boundary

The common outer head is `Eq`; the candidate boundary is the concrete
commutative-ring instance under coercion, coefficient, and reverse. The first
path contains applications only, not a projection or recursor. Both ring
definitions have lambda bodies; their reducibility metadata predicts a
possible unfold, but no same-body control isolates it.

## R3. Exposed data-bearing structure

```text
complex equality
|- starRingEnd / coercions / Polynomial.coeff / Polynomial.reverse
|  |- Field.toCommRing versus AlgebraicClosure.instCommRing
|  |- PadicAlgCl and finite-dimensional/stalk instances
|  `- P.obj.ρ, W.frobenius, and local polynomial data
`- repeated ring path on the right equality side
```

After both ring leaves are aligned, the first visible difference moves to
`Functor.obj` versus local `P` under `LinearMap.charpoly`. That movement is
directly checked; the large object tree below it is structurally inferred.

## R4. Cost distribution and reduction footprint

The constituent equivalence and later purity proof are cheap in isolation.
Keeping `exact h` while replacing later work still times out, while replacing
only `exact h` is cheap. Aligning the left ring leaf, right ring leaf, or both
leaves still times out at about 58.44 s. Local isolated unfold counters are
small (maximum 8), so no child counter is credited as the cause.

## R5. Causal control

`AlignLeftRing`, `AlignRightRing`, and `AlignBothRing` use the same `exact h`,
same goal, and normal Kernel checking; their head probes verify the selected
leaf changes. None removes the timeout. `PolynomialTransport` is a checked
alternate proof route (7.10 s for the local proof), but changes proof
construction and is not a one-factor alignment. The historical `After.lean`
also times out; current `Master.lean` is a later 6.10 s form.

## R6. Exposure-footprint comparison

Original: both equality sides carry distinct ring paths and the final proof
conversion times out.
Ring-aligned: both first differences move to `Functor.obj` versus `P`, but the
same cost remains.
Restored: the original ring leaves and timeout return. No causal exposure
reduction is established by ring alignment; the deeper object path remains
unmeasured.

## R7. Classification and confidence

Classification: **U** (P2/P4 candidates are not established).
Confidence: **Confirmed** for the exact conversion site and the negative
ring-leaf control; **Not supported** for ring-leaf sufficiency; **Plausible**
for a deeper object or proof-proposition mechanism.
Directly measured: exact pair, both-side movement, timings, and alternate
route. Structurally inferred: the polynomial/stalk tree. Unknown: the dominant
post-ring child and the Kernel reduction order.

## Most important result

The visible ring mismatch is real but not causal by itself. Aligning both
instances exposes a deeper `Functor.obj`/local-object mismatch without reducing
the conversion, so the case remains unclassified.
