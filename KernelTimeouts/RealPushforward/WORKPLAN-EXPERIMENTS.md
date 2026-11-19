# RealPushforward workplan reference

Source snapshot: `isReal_higherLowerShriek_one` example,
module `DeligneLaumon/AffineLine/RealPushforward`, commit
`ed3d39ddb5d`; Lean and Mathlib 4.35.0. The cost site
is the final inferred-type/declared-type conversion at
`exact this` after two polynomial rewrites.
`probes/HeadAudit.lean` preserves the local context and
exact pair. Both sides are `Eq` propositions with
matching `Polynomial.coeff` and coercion heads. The
first unequal polynomial argument is inferred
`LinearMap.charpolyRev ...` versus expected
`FrobeniusModule.localPolynomial ...`. These are
different regular definitions, heights 26 and 27.
One unfolding of `localPolynomial M` exposes
`M.frobeniusEnd.charpolyRev`.

WORKPLAN.md §5.4 designates this as the necessary-unfolding
reference and requires no new source experiment merely to
reconfirm the first unfold. The existing immutable
`probes/FinalExact.lean`, `probes/AlignedGoal.lean`,
and `probes/AlignedHead.lean` serve as the reference
probes; no renamed `wp` copies were made.

## RP-REF: Original versus aligned polynomial

EXPERIMENT: RP-REF; group: G3-A reference. Hypothesis:
the different regular polynomial heads require initial
definition reduction in the original representation,
whereas an aligned high-level polynomial expression
avoids that conversion. BASELINE: `probes/FinalExact.lean`
checks the original final proof at 200,000 heartbeats.
It gives a deterministic Kernel timeout in 54.73 s
wall, 53.57 + 1.14 s CPU, 4,720,124 KB RSS.
CONTROL: `probes/AlignedGoal.lean` changes the
declared polynomial representation to `charpolyRev`,
preserving the same proposition by definitional
equality and the rewritten proof term. Normal Kernel
checking is enabled. `probes/AlignedHead.lean`
confirms that the elaborated pair no longer first
diverges at the polynomial argument; a smaller
`Semifield.toCommSemiring` versus
`CommRing.toCommSemiring` instance difference remains.
RESULT: the full checked control succeeds in 3.00 s
wall, 2.00 + 1.04 s CPU, 3,161,488 KB RSS.
The same final conversion is no longer expensive.
Supports: polynomial-head alignment removes the
initial costly path, while the remaining instance
leaf alone is insufficient. Weakens: a generic
semiring-instance mismatch is by itself the timeout
cause. Unresolved: the exact downstream stalk/module
comparison after the original required unfolding.
Classification: necessary unfolding in the original
representation; confidence: confirmed for the
representation trigger, plausible for any particular
downstream amplifier.

All timings used one Lean thread, `timeout 3600`,
`/usr/bin/time -v`, and normal Kernel checking,
with fixed process concurrency of one. Kernel-only
time and heartbeat consumption are not separately
available. Neither the source inspection nor these
controls trace the Kernel's internal reduction order.
