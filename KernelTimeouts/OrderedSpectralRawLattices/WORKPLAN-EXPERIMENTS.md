# OrderedSpectralRawLattices workplan experiments

All paths here are relative to this case directory. Source snapshot: the
`small_spectral_raw_lattices` declaration in `Before.lean`, module
`AlgebraicGeometry/Coefficient/OrderedSpectralLattices`, commit
`f4946fdb6b6`. Lean and Mathlib: 4.35.0. The cost site is the final
inferred-type/declared-type conversion for
`CondensedRing.exists_stratified_lisse_integral_lattice`. The original
local context, three let bindings, and exact expression pair are retained in
`probes/HeadAudit.lean`. Every timed Kernel check used one Lean thread,
`timeout 3600`, and normal Kernel checking. The diagnostic `wp/*Head.lean`
files end in `sorry` after printing the pair and are not successful proofs.

The original pair has matching three-let syntax. In the first ring-object
value, both heads are `Profinite.continuousMapRingObj`; its topology
instance descends through `spectralNorm.nontriviallyNormedField` and
`IsLocalRing.toNontrivial` to `Semifield.toCommSemiring` on the inferred
side and `CommRing.toCommSemiring` on the declared side. The second
ring-object value has the same first unequal leaf. The third value is a
`Functor.map`; the body is a `forall` versus the named
`RawStratifiedLattices` predicate. The three competing source instance
paths are `IsRegularLocalRing.toIsLocalRing`,
`HenselianLocalRing.toIsLocalRing`, and `IsDomain.of_isSimpleRing`.

The following are separate G3-B/H5 one-factor or explicitly marked factorial
experiments. The baseline for the original seven-control timing session was
45.73 s wall and 3,283,804 KB RSS, deterministic Kernel timeout at 200,000
heartbeats. A fresh baseline in this workplan session was 40.23 s wall,
46.31 s user + 0.99 s system, 3,341,996 KB RSS, same timeout.
The current full three-path control was 10.11 s wall,
13.82 + 0.92 s CPU, 2,564,172 KB RSS, success. Kernel-only time and
heartbeat consumption are unavailable; the stated result is the ordinary
Kernel check at the configured heartbeat limit.

## C1-R: Regular-local-ring path

EXPERIMENT: C1-R; case: OrderedSpectralRawLattices; group: G3-B/H5.
Hypothesis: removing this path aligns the ring instance. Baseline pair and
site are above; baseline Kernel result is timeout. Control: disable only
`IsRegularLocalRing.toIsLocalRing` for the same declaration
(`probes/DisableRegular.lean`); theorem obligation and all proof terms
are preserved; Kernel checking enabled. The `wp/DisableRegularHead.lean`
elaborated pair still first diverges at
`Semifield.toCommSemiring` / `CommRing.toCommSemiring` in both ring values.
Result: timeout, 44.93 s wall, 44.15 + 0.78 s CPU, 3,284,440 KB RSS.
The same final conversion remains. Supports: competing paths persist.
Weakens: this path alone is sufficient. Unresolved: deeper changed terms
after the first mismatch. Classification: unfavorable concrete instance
path; confidence: not supported as a sufficient single control.

## C1-H: Henselian-local-ring path

EXPERIMENT: C1-H; same snapshot, module, pair, context, and group as C1-R.
Control: disable only `HenselianLocalRing.toIsLocalRing`; obligation
preserved, Kernel enabled. The diagnostic elaborated pair still first
diverges at the same semiring leaf in both ring values. The same final
conversion times out: 45.23 s wall, 44.37 + 0.85 s CPU,
3,285,356 KB RSS. Supports: remaining paths retain the mismatch.
Weakens: Henselian removal alone suffices. Deeper effects are unresolved.
Classification: unfavorable instance path; confidence: not supported as
a sufficient single control.

## C1-D: Domain path

EXPERIMENT: C1-D; same snapshot, module, pair, context, and group.
Control: disable only `IsDomain.of_isSimpleRing`; obligation preserved,
Kernel enabled. The diagnostic elaborated pair still first diverges at
the same semiring leaf in both ring values. The same final conversion
times out: 45.43 s wall, 44.56 + 0.86 s CPU, 3,284,008 KB RSS.
Supports: the semiring mismatch is upstream of this path in the current
expression. Weakens: domain removal alone suffices. Deeper effects are
unresolved. Classification: unfavorable instance path; confidence: not
supported as a sufficient single control.

## C1-RH: Regular and Henselian paths

EXPERIMENT: C1-RH; group: G3-B factorial two-path control, same snapshot,
module, obligation, pair, and final conversion. Disable both local-ring
paths, leaving the domain path enabled. The elaborated first leaf **moves**
from the semiring pair to `instIsDomain` versus
`IsDomain.of_isSimpleRing` beneath
`Algebra.IsSeparable.of_integral`; both ring values remain syntactically
unequal. Kernel checking still times out: 45.23 s wall,
44.30 + 0.88 s CPU, 3,284,080 KB RSS. Supports: the local-ring pair
removes the first mismatch, but domain search supplies a second one.
Weakens: semiring-leaf equality alone suffices. Classification:
unfavorable instance path; confidence: strongly supported for the
interaction, not a successful proof control.

## C1-RD: Regular and domain paths

EXPERIMENT: C1-RD; G3-B factorial two-path control, same snapshot,
module, obligation, pair, and final conversion. Disable the regular
local-ring and domain paths. The diagnostic pair still first diverges
at the original semiring leaf in both ring values. Kernel timeout:
45.23 s wall, 44.39 + 0.82 s CPU, 3,283,492 KB RSS. Supports: the
Henselian path can retain that leaf. Weakens: this pair suffices.
Further nested differences are unresolved. Classification: unfavorable
instance path; confidence: not supported as a sufficient pair.

## C1-HD: Henselian and domain paths

EXPERIMENT: C1-HD; G3-B factorial two-path control, same snapshot,
module, obligation, pair, and final conversion. Disable the Henselian
and domain paths. The pair still first diverges at the original
semiring leaf in both ring values. Kernel timeout: 45.53 s wall,
44.60 + 0.88 s CPU, 3,284,536 KB RSS. Supports: the regular path
can retain that leaf. Weakens: this pair suffices. Further nested
differences are unresolved. Classification: unfavorable instance path;
confidence: not supported as a sufficient pair.

## C1-RHD: All three paths

EXPERIMENT: C1-RHD; G3-B factorial three-path control, same snapshot,
module, obligation, pair, and final conversion. Disable all three
paths, as in `After.lean`. The diagnostic elaborated pair changes:
both first and second `continuousMapRingObj` let values are now
syntactically equal. The third `Functor.map` let value and the
folded final predicate still differ. Normal Kernel checking succeeds:
13.71 s wall, 12.90 + 0.81 s CPU, 2,496,640 KB RSS in the original
matrix; 10.11 s wall, 13.82 + 0.92 s CPU, 2,564,172 KB RSS in the
current baseline/After session. Supports: the combined concrete instance
alignment removes the expensive path; the remaining wrapper conversion
is cheap enough. Weakens: any single path is the whole cause.
Unresolved: exact internal Kernel order and contribution of the third
let value. Classification: unfavorable path avoided by alignment;
confidence: confirmed for the three-path control.

## Interpretation

The new structural probes distinguish two successive mismatches. Disabling
both local-ring paths moves the first mismatch to the domain-instance
leaf, yet the Kernel still times out. Only disabling all three aligns the
two ring-object values and makes the checked declaration succeed.
This supports an interaction among instance-search routes, not an
individual instance leaf as a sufficient cause. The source-level
availability edits also affect elaboration; they are not a same-body
reducibility-hint experiment. No claim is made about the exact C++ Kernel
reduction sequence.
