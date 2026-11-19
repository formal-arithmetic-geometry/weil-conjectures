# FiniteBaseChangeRestrictionMateTransport workplan experiments

Source snapshot: `finite_base_change_restriction_mate_transport`,
module `Algebra/Homology/OpenTensorNormalization/OpenTensorNormalizationData`,
commit `0676f555de6`; Lean and Mathlib 4.35.0. The costly site is
argument 49 (`hb`) of `transport_from_unit` after the preceding 48
actual category, functor, equivalence, and mate arguments have been
substituted. `probes/HeadAudit.lean` retains the original local context
and exact pair. Both propositions are `forall M : FiniteModules A X', Eq
...`. Their first raw difference is in the equality's `Quiver.Hom`
type, below `ProjectionRestriction.Mod`: supplied `Scheme.ProEt X`
versus expected `OpenTensorNormalization.Site .ordinary X`. The
same site difference recurs in the two equality sides.

All timed checks used one Lean thread, `timeout 3600`,
`/usr/bin/time -v`, normal Kernel checking, and a fixed process
concurrency of one for this work. Kernel-only time and heartbeat
consumption are not separately exposed. The reduced-budget diagnostic
uses 400,000 heartbeats; the original declaration used 4,000,000.

## B2-S: Immediate site representation

EXPERIMENT: B2-S; group: G2-A/G3-A. Hypothesis: the expected site's
ordinary-mode branch exposes the supplied Pro-etale site. BASELINE:
`probes/HeadAudit.lean` reconstructs the exact 49th binder; its
first mismatch is the `ProEt`/`Site` pair above. The original
reduced-budget application times out at 89.36 s wall,
89.06 + 1.05 s CPU, 5,743,096 KB RSS. CONTROL:
`probes/wp/SiteShape.lean` proves
`Site .ordinary X = X.ProEt` by `rfl` under ordinary Kernel checking.
The one-step `Site` source body is a mode match; selecting
`.ordinary` exposes `X.ProEt`. This checks the representational
equality but is **not** a same-cost-site timing control and does not
change either elaborated proposition in the expensive application.
RESULT: the checked shape probe succeeds in 2.10 s wall,
1.29 + 0.81 s CPU, 2,203,148 KB RSS. The site spelling is
definitionally reconcilable. `probes/wp/SiteUnfoldHead.lean`
reconstructs the original instantiated proposition pair,
replaces the eight expected `Site .ordinary` type
applications with corresponding `Scheme.ProEt` applications,
and prints the changed pair. The first difference moves from
the site type to its category-instance argument:
`Scheme.instCategoryProEt` versus
`OpenTensorNormalization.instCategorySite` under `Mod`.
This diagnostic takes 3.90 s wall, 3.98 + 0.67 s CPU,
2,530,612 KB RSS; it ends in `sorry` and is not a
same-cost-site Kernel control. Supports:
necessary mode-match exposure for this initial leaf. Weakens: none.
Classification: necessary representation reduction, with an
unresolved downstream path. Confidence: strongly supported for the
one-step equality and next instance mismatch, plausible for their
individual shares of the total cost.

An attempted source substitution at the explicit `Ab` category
argument was rejected before timing: `Site .ordinary X` has type
`Type (u+1)`, while `constantSheaf` there requires a
`GrothendieckTopology`. It was removed and is not counted as a
performance result or as an elaborated-pair change.

## B2-T: Exact expected proof proposition

EXPERIMENT: B2-T; group: G2-B/G2-C. Hypothesis: the cost is the
supplied proof's proposition conversion to the instantiated helper
domain. BASELINE: the original `hb := h` application at 400,000
heartbeats gives a deterministic Kernel timeout, 89.36 s wall,
89.06 + 1.05 s CPU, 5,743,096 KB RSS. The original 4,000,000-budget
application took 577.57 s in the head audit. CONTROL:
`probes/TransportHB.lean` replaces only argument 49 with
`fun M => by transport_exact h M`, leaving the other 48 arguments
and square obligation intact. `probes/TransportHead.lean` confirms
that the resulting argument has the exact instantiated expected
proposition; the original first site divergence is absent from the
argument-domain comparison. Kernel checking remains enabled. The
surrounding diagnostic example ends with `sorry` only after the
helper application; the complete `After.lean` checks the theorem.
RESULT: the application succeeds in 4.40 s wall,
4.26 + 0.94 s CPU, 2,335,020 KB RSS. The expensive argument-domain
conversion is removed. Supports: dependent proof-proposition alignment
is causal. Weakens: proof-body construction alone explains the cost.
Unresolved: whether aligning the site and category instance alone,
with every later dependent field unchanged, would suffice.
Classification: unfavorable
dependent-domain path avoided by the transported argument.
Confidence: confirmed for the exact-proposition control, plausible
for site spelling as a sole cause.

## Mechanism

The helper's expected proposition incorporates concrete data from the
first 48 arguments. Its site type is stored as `Site .ordinary X`,
whereas the supplied proof's proposition stores `X.ProEt`. The mode
match provides a route to equality, but an independent
mode-specific category-instance representation is the next
stored difference. The complete proposition also contains
nested functor and module data. The exact-proposition control
avoids the costly check; no experiment here attributes all
89 seconds to the mode match alone.
