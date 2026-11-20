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
## Round 2 and v2 addendum

The fresh full-alignment probe completed in 16.91 s wall (27.55 s user, 2.54 GB peak RSS). Four single-route restoration probes each reached a deterministic timeout in small_spectral_raw_lattices after 49.96--50.76 s and did not reach the final theorem check. The original all-route restoration remains the 40.23 s timeout.

### STRUCTURE EXPOSURE AND AMPLIFICATION ADDENDUM

**A. MISMATCH SEMANTICS.** The initial divergence is a bundle: two repeated continuousMapRingObj values select Semifield.toCommSemiring versus CommRing.toCommSemiring, with related third-map and lattice-predicate differences. No one route is independently causal; the complete three-path bundle is the trigger.

**B. EXPOSURE.** The boundary is the topology/instance argument of the two ring-object lets, followed by the RawStratifiedLattices dependent predicate. The tree contains spectral norm, local-ring/domain instances, continuous-map ring objects, a functor map, locally-free module fields, and quantified lattice data. The ring paths are comparison-relevant and full alignment connects them to the measured Functor.obj footprint; individual fields remain inferred.

**C. COST MECHANISM.** Original and single-route variants are reduction-heavy and repeated over two ring lets. Full alignment is 16.91 s; single-route probes time out; original is 40.23 s/timeout. The 23,580 Functor.obj count is a downstream footprint, not an execution trace.

**D. FIXED-TRIGGER ABLATION.** Invalid: the trigger is the complete dependent instance bundle. Abstracting one route changes the bundle or times out at the leaf. The full aligned/original pair is the valid restoration control.

**E. REDUCTION-PATH AUDIT.** Ring-object heads are shared but instance paths differ. Disabling one route moves the first difference to another route and still times out; disabling all three exposes the common fast representation. Internal order is inferred.

**F. MISMATCH PROVENANCE.** The same generic spectral construction is elaborated through distinct IsRegularLocalRing, HenselianLocalRing, and IsDomain providers. The third map and lattice predicate come from surrounding helpers. The first provenance divergence is instance selection.

**G. CONCLUSION.** P2 + P3, evidence level 2. Every one-factor restoration fails while complete alignment succeeds. Remaining predicate cost is unattributed. A typed whole-bundle ablation preserving all three lets is the next falsifier.
