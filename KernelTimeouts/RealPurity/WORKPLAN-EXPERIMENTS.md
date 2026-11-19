# RealPurity workplan experiments

Source snapshot: `IsReal.exists_isPunctuallyPureOfWeight_cokernel_detWeight`,
module `WeilSheaf/RealPurity`, commit `e2d8b540cba`; Lean and
Mathlib 4.35.0. The cost site is `exact h` inside the local
`hreal' : W.IsReal l P.obj.ρ ι` proof, after the original two
polynomial rewrites. `probes/HeadAudit.lean` retains the actual
`h` proposition, expected goal, and local context. Both are
equalities of complex numbers. The first raw difference on each
equality side is below `Polynomial.coeff` and
`Polynomial.reverse`: `Field.toCommRing` in `h` versus
`AlgebraicClosure.instCommRing` in the goal. The former is an
abbrev; the latter is a regular definition of height 29.

All timed probes used one Lean thread, `timeout 3600`,
`/usr/bin/time -v`, normal Kernel checking, and fixed
process concurrency of one. The heartbeat setting is the
source default 200,000. Kernel-only time and heartbeat
consumption are not separately available. Baseline
`probes/AfterHRealSorry.lean` keeps the two rewrites and
`exact h`, then discards later theorem work. It times out
deterministically in 58.24 s wall, 58.36 + 1.30 s CPU,
5,616,188 KB RSS. The later unknown-constant error is a
consequence of the timed-out private theorem.

## C4-L: Left equality-side ring path

EXPERIMENT: C4-L; group: G3-B. Hypothesis: aligning the first
`Polynomial.reverse` ring-instance leaf removes the
final conversion cost. BASELINE: the exact pair and timeout
above. CONTROL: `probes/wp/AlignLeftRing.lean` retains
the proof construction and inserts a Lean `change` immediately
before `exact h`. It changes only corresponding
`Field.toCommRing`/`AlgebraicClosure.instCommRing` leaves
in the goal's left equality side, using the actual `h` type
as the aligned source. The `change` accepts the
definitionally equal obligation; ordinary Kernel checking
remains enabled. `AlignLeftRingHead.lean` confirms a changed
elaborated left side. Its first difference moves to
`Functor.obj` versus local `P` below
`LinearMap.charpoly`; the right equality side still
first differs at the ring leaf. RESULT: deterministic
Kernel timeout, 58.44 s wall, 58.43 + 1.27 s CPU,
5,618,576 KB RSS. The same `exact h` cost remains.
The diagnostic head probe, with `exact h` replaced by
`sorry`, completes in 5.90 s wall, 6.24 + 0.91 s CPU,
4,242,280 KB
RSS, so the inserted `change` itself does not explain
the timeout. Supports: another nested object mismatch
exists on the aligned side. Weakens: left ring path alone
is sufficient. Classification: negative one-side control;
confidence: confirmed negative result.

## C4-R: Right equality-side ring path

EXPERIMENT: C4-R; group: G3-B. The same snapshot, pair,
context, and `exact h` site are used. CONTROL:
`probes/wp/AlignRightRing.lean` changes only the ring
leaf in the right equality side. The goal `change` is
accepted and the proof construction is otherwise unchanged.
`AlignRightRingHead.lean` verifies that the right
side's first difference moves past the ring leaf, while
the left side still first differs there. Kernel checking
enabled. RESULT: deterministic timeout, 58.44 s wall,
58.39 + 1.33 s CPU, 5,616,352 KB RSS. The head
diagnostic completes in 5.90 s wall, 6.23 + 0.96 s CPU,
4,244,168 KB
RSS. Supports: the original left-side mismatch remains.
Weakens: right ring path alone is sufficient. The
next nested right-side contribution is unresolved.
Classification: negative one-side control; confidence:
confirmed negative result.

## C4-B: Both equality-side ring paths

EXPERIMENT: C4-B; group: G3-B factorial two-side control.
The same `hreal'` proof, local context, theorem obligation,
and `exact h` are retained. CONTROL:
`probes/wp/AlignBothRing.lean` aligns the ring-instance
leaves in both equality sides, one path per side, using the
same goal-change mechanism as C4-L/R. Both actual
elaborated changes are logged, and
`AlignBothRingHead.lean` prints the resulting pair.
After alignment, the first data difference on **each**
side is `Functor.obj` versus local `P` under
`ObjectProperty.FullSubcategory.obj` and
`LinearMap.charpoly`. The previously first
`Field.toCommRing`/`AlgebraicClosure.instCommRing`
pair is absent at these paths. Kernel checking enabled.
RESULT: deterministic timeout, 58.44 s wall,
58.39 + 1.29 s CPU, 5,619,680 KB RSS.
The head-only diagnostic completes in 6.00 s wall,
6.30 + 0.96 s CPU,
4,242,880 KB RSS. Supports: a later concrete
functor-object representation remains after both ring
paths align. Weakens: the ring-instance leaves are a
sufficient cause of the timeout. The exact contribution
of the newly exposed object mismatch is unmeasured.
Classification: unfavorable nested path, unresolved
causal child. Confidence: confirmed negative result
for ring-leaf sufficiency, plausible for the deeper
object path.

## Interpretation

The ring-instance pair is a real first structural
difference, but each one-side control and the combined
control still time out at the original `exact h` site.
The next visible mismatch is a concrete
`Functor.obj` expression against the local `P`.
The existing `PolynomialTransport.lean` proof makes the
local `hreal'` obligation cheap by changing proof
construction; it is not counted as evidence that the ring
leaf alone causes the original timeout. The historical
`After.lean` also times out on this toolchain, so its
older change is not credited with the current Master's
speed.
