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
## Round 2 and v2 addendum

DownstreamAfterRing aligns both ring paths at the same local exact h site and still reaches a deterministic timeout after 66.01 s (61.95 s user, 5.58 GB peak RSS). The first post-ring divergence is under LinearMap.charpoly at a Functor.obj/local P boundary. The child footprint includes Add.add 1,910, CategoryStruct.comp 663, AddMonoid.toAdd 574, and Functor.obj 55.

### STRUCTURE EXPOSURE AND AMPLIFICATION ADDENDUM

**A. MISMATCH SEMANTICS.** Field.toCommRing versus AlgebraicClosure.instCommRing is syntactic and independently alignable, but not causal. The next Functor.obj/local-object divergence under LinearMap.charpoly is unresolved; no supported trigger exists.

**B. EXPOSURE.** The boundary is the ring argument under Polynomial.reverse/coeff, then the first common polynomial representation under charpoly. The visible tree includes polynomial, Frobenius/stalk, functor-object, and algebraic-closure data. Only the post-ring object conversion is relevant to the unchanged timeout; no causal child attribution is measured.

**C. COST MECHANISM.** Ring-aligned proof is still reduction-heavy and times out. Small ring counters do not account for the conversion; larger object/proof path remains unknown. No repeated generated-field cost is shown.

**D. FIXED-TRIGGER ABLATION.** Invalid: the ring leaf is shown non-causal and the next candidate lies inside a dependent polynomial/object bundle.

**E. REDUCTION-PATH AUDIT.** Aligning either or both regular ring paths moves the first difference to Functor.obj versus local P under LinearMap.charpoly. Polynomial.reverse exposes a deeper representation without making the parent conversion cheap. Internal order is inferred.

**F. MISMATCH PROVENANCE.** Field and algebraic-closure instance providers create the ring split during elaboration. The downstream Functor.obj path is the concrete Frobenius/stalk producer versus local P. First provenance divergence is ring selection; first post-alignment conversion divergence is the object producer split.

**G. CONCLUSION.** U, evidence level 1; ring-leaf sufficiency is not supported. The unchanged 66.01 s timeout after both alignments is strongest contrary evidence. A typed Functor.obj/local-object alignment retaining the original polynomial proof is the next falsifier.
