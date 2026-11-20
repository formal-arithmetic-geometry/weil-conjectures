# STRUCTURE EXPOSURE AUDIT

Case: `OrderedSpectralRawLattices`
Source snapshot: `f4946fdb6b6`, `small_spectral_raw_lattices`
Lean/Mathlib: 4.35.0, one Lean thread, normal Kernel checking, 200,000 heartbeats

## R1. Exact Kernel cost site and initial mismatch

The cost is the final conversion from the inferred type of
`CondensedRing.exists_stratified_lisse_integral_lattice ...` to the declared
`RawStratifiedLattices` goal. Both sides retain three lets. In the first two
`Profinite.continuousMapRingObj` values the first material mismatch is
`Semifield.toCommSemiring` versus `CommRing.toCommSemiring`, reached through
`spectralNorm.nontriviallyNormedField` and `IsLocalRing.toNontrivial`. The
bundle also contains a third `Functor.map` value and a named versus unfolded
lattice predicate. The initial trigger is therefore a three-path instance
bundle, repeated in two ring values.

The fresh baseline is 40.23 s wall and deterministic timeout (3.34 GB RSS);
the earlier session measured 45.73 s. Type-only and helper-only checks take
13.91 s.

## R2. Candidate exposure boundary

The outer shape is a matching `let` spine. The candidate boundary is the
topology-instance argument of each `continuousMapRingObj`; the final wrapper
`RawStratifiedLattices` is a second boundary whose body exposes a `forall`.
The first difference moves to `instIsDomain` versus
`IsDomain.of_isSimpleRing` when the regular and Henselian paths are both
disabled. This is measured expression movement, not an assertion about
Kernel reduction order.

## R3. Exposed data-bearing structure

```text
three let bindings
|- A : Profinite.continuousMapRingObj
|  `- topology / spectralNorm / local-ring / semiring instance path
|- B : Profinite.continuousMapRingObj
|  `- the analogous concrete instance path
|- a : Functor.map (sheafCompose ...)
|  `- category and coefficient-map instances
`- lattice predicate / RawStratifiedLattices
   |- locally-free modules over the ring objects
   |- condensed ring and stratum data
   `- dependent quantified fields
```

The first two value paths and the remaining third-value/predicate mismatch are
directly seen in `HeadAudit` and `AllDisabledHead`; field-level Kernel work
inside the predicate is inferred except for the recorded `Functor.obj` count.

## R4. Cost distribution and reduction footprint

Disabling only regular, Henselian, or domain paths leaves a timeout (44.93,
45.23, 45.43 s). Disabling either pair also leaves a timeout; the R+H pair
moves the first difference to the domain instance. The final `RHD` control is
10.11 s wall (13.82 + 0.92 s CPU, 2.56 GB RSS) and succeeds. The original
diagnostic reports 23,580 reducible `Functor.obj` reductions. No separate
cost was measured for the two repeated ring fields.

## R5. Causal control and §6 restoration

The complete three-path alignment disables
`IsRegularLocalRing.toIsLocalRing`, `HenselianLocalRing.toIsLocalRing`, and
`IsDomain.of_isSimpleRing`. It preserves the declaration and consumer; the
first two ring values become syntactically equal, verified by
`AllDisabledHead.lean`, and the final check succeeds. Single and pair controls
are negative. The §6 restoration re-enables all three paths in `Before.lean`:
the original pair returns and the check times out.

## R6. Exposure-footprint comparison

Original: two ring values expose competing instance routes, followed by the
third map/predicate differences and a large `Functor.obj` footprint.
Aligned: the two ring values are equal; the third value and folded predicate
still differ, but the remaining conversion is cheap.
Restored: all three routes reproduce the original semiring mismatch and
timeout. Exact internal unfold order and the third-let contribution remain
unknown.

## R7. Classification and confidence

Classification: **P2 (bundle-triggered exposure)** and **P3 (repeated ring
value path)**.
Confidence: **Confirmed** for the necessity of the complete three-path
alignment; **Strongly supported** for the bundle interpretation.
Directly measured: all seven partial/full controls, expression movement, and
timings. Structurally inferred: the lattice-field tree and downstream role of
the predicate. Unknown: the exact Kernel order and separate field costs.

## Most important result

No individual instance route explains the timeout. The complete three-route
alignment removes the first two data-valued mismatches and the large cost,
while leaving a smaller predicate conversion. This is the §6 restoration
experiment for the bundle case.
