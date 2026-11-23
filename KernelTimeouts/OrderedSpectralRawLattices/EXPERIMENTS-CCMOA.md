# CCMOA Batch 1: OrderedSpectralRawLattices

Case: `KernelTimeouts/OrderedSpectralRawLattices`  
Root: conversion from the instantiated type of
`CondensedRing.exists_stratified_lisse_integral_lattice ell K p k hpell S` to
the local `RawStratifiedLattices` goal in
`AlgebraicGeometry.ProEtale.small_spectral_raw_lattices`.

The measurements reuse the existing MOE, AD, and READY4.2 artifacts. No
finished experiment was rerun.

## A. S0-S6 stage audit

### S0: source

The source has three `let` values (`A_0`, `B_0`, `a_0`), two
`Profinite.continuousMapRingObj` constructions, one `sheafCompose.map`, and
the named `RawStratifiedLattices` predicate. The helper is applied directly.
The original local context makes the R/H/D routes available:
`IsRegularLocalRing.toIsLocalRing`, `HenselianLocalRing.toIsLocalRing`, and
`IsDomain.of_isSimpleRing`.

### S1: macro-expanded syntax

The saved syntax snapshots show no relevant macro or notation change. The
first mismatch is not source spelling or macro generated syntax.

### S2: elaborated expressions

After all preceding actual arguments are instantiated, the first unequal
data-bearing child is the semiring provider inside the topology argument of
`Profinite.continuousMapRingObj`:

```text
left  = Semifield.toCommSemiring
right = CommRing.toCommSemiring
```

The difference occurs in both the first and second `let` values. The stable
node path is `root/body/body/arg/fn/fn` in the bounded pair snapshots; in the
full root it is under the first `let` value, then the topology /
`spectralNorm.nontriviallyNormedField` /
`IsLocalRing.toNontrivial` argument. The third map and final predicate have
separate differences. The all-route source control re-elaborates the same
declaration and makes the first two ring-object values structurally equal.

### S3: declaration finalization

No generated proof field or proof abstraction is needed for the first
data-bearing mismatch. The imported helper is observable only after loading
its declaration; its pre-finalization term is unavailable. This is recorded
as `finalization-observable-only`, not as evidence of a finalization cause.

### S4: stored environment

Relevant stored hints are:

| Constant | Kind / hint |
| --- | --- |
| `Profinite.continuousMapRingObj` | `def`, `abbrev` |
| `Semifield.toCommSemiring` | `def`, `abbrev` |
| `CommRing.toCommSemiring` | `def`, `regular:1` |
| `RawStratifiedLattices` | regular definition |

The helper's imported provider arguments are environment-frozen. Current
local priorities cannot rewrite them.

### S5: Kernel root pair

The exact root pair is the helper's expanded `let A; let B; let a; forall L, ...`
type versus the local `let A_0; let B_0; let a_0; RawStratifiedLattices ...`
type. M0 begins at the repeated provider pair above. The original READY4.2
root used 18,944,709 calls, with M1 at 43.922% of calls / 64.684% of
comparison-exclusive time, M2 at 36.382% of time, and Matched at 0.698%.
The fresh original conversion was 40.23 s and deterministic-timeout scale.

### S6: Kernel exposure

After M0, descent enters the dependent lattice proposition through nested
`Exists`, `Quiver.Hom`, `Functor.obj`, and `Mod.X`. The earlier exact-site
diagnostic counted 23,580 reducible `Functor.obj` reductions. The descendants
are exposure of the S2 provider mismatch, not a Kernel-created first
representation difference.

**First-divergence conclusion:** earliest relevant stage S2; active at S5;
latent dependent descendants are exposed at S6. Evidence: **Strongly
supported** (exact snapshots and a successful route-availability control,
with a source-scope confound).

## B. One-factor representation and route controls

All controls retain the same declaration, consumer, dependent telescope, and
final root obligation. The control matrix disables one or two routes at a time
and then all three. The route names and the first provider result are recorded
in `ccmoa/B-instance-trace.snapshot` and `ccmoa/S2-provider-compare.txt`.

| Control | Expr change | Kernel result / counters |
| --- | --- | --- |
| Original | R/H/D available; `Semifield.toCommSemiring` vs `CommRing.toCommSemiring` in both ring values | 18,944,709 READY4.2 calls; 40.23 s fresh; deterministic timeout |
| One-route or two-route removal | Re-elaborated local provider terms change, but the first provider pair remains non-equal | Each saved control remains timeout-scale; no one-route alignment |
| All three routes removed | Both `continuousMapRingObj` values become structurally equal; third map and named predicate remain different | 10.11 s fresh (16.91 s in the separate alignment session); no comparable large root |
| Restore any one route after all-route control | The corresponding provider mismatch returns | Timeout-scale again; this is the saved E3 puncture |

This is a valid type-correct source availability matrix, but it is not a
one-factor frozen replay: disabling routes changes elaborator inputs and can
change more than one provider child. Therefore the workload reduction is
evidence for the route bundle, not proof that one instance leaf alone is the
sole cause. There is no metadata-only F2 control.

**B evidence:** **Strongly supported** for the route bundle; **Plausible** for
any individual provider leaf.

## C. Targeted elaborator provenance

The focused trace records ordinary implicit assignments (`Fact` prime facts,
fields, algebras, finite-dimensionality, characteristic, and scheme classes)
and the selected R/H/D declarations in the source matrix. No
`isDefEq.assign` record isolates a transparency-driven assignment for the
provider pair, and no candidate-list replay changes the final root expression
while preserving the same source and obligation. No relevant coercion is the
first divergent child.

The result is therefore:

- provider expressions are elaborator-selected at S2;
- source route availability is authored at S0;
- a causal Elaborator-only perturbation was not demonstrated;
- no transparency sweep or frozen F0/F1 replay is justified by the saved
  evidence.

**C evidence:** **Plausible** for an elaborator contribution; **Not observed**
for a separate transparency or coercion cause.

## D. Declaration finalization

The local proof has no generated proof declaration on the relevant path. The
imported helper's pre-finalization term is unavailable, so an exact S2/S3
comparison for that declaration is unobservable. Nothing in the saved S2,
S4, or route controls requires finalization to explain the mismatch.

**D evidence:** **Not observed** as a causal contribution; imported
pre-finalization identity is **Unknown**.

## E. Cheap-but-fragile boundary inventory

| Boundary | Current cheap behavior | Puncture | Status |
| --- | --- | --- | --- |
| `continuousMapRingObj` (`abbrev`) | Matching provider terms avoid topology descent | Re-enable a route, unfold the abbrev, or infer a fresh provider | **Fragile but effective** |
| `RawStratifiedLattices` regular wrapper | Wrapper exposure alone is cheap after ring-object alignment | Expand the predicate while independently reconstructing ring data | **Fragile; not primary** |
| Three-let spine | Shared `let` skeleton is not the first divergence | Inline or zeta-reduce the ring objects | **Untested as an independent cause** |
| Whole-side helper application | Naming/binding the helper is cheap; direct `exact h` enters the expensive conversion | Replace transport/alignment with direct handoff | **Fragile but effective** |

## Synthesis

| Case | Earliest divergence | Primary origin | Elaborator causal? | Finalization causal? | Kernel-exposed latent difference? | Effective boundary | Boundary fragility |
| --- | --- | --- | --- | --- | --- | --- | --- |
| OrderedSpectralRawLattices | S2 | Source-authored R/H/D availability selecting different provider terms (**Strongly supported**) | Plausible | Unknown | Strongly supported | All-route provider alignment (**Strongly supported**) | Strongly supported: route restoration reopens the expensive path |

Overall, the expensive root is a mixed source/API and elaborator-selected
provider mismatch. The dependent M1/M2 tree is Kernel-exposed, while the
available evidence does not justify assigning sole causality to one R/H/D
instance leaf or to declaration finalization.

## Audit note and Batch 2

The all-route control changes several available providers and therefore
cannot demonstrate the effect of one instance leaf. Each saved one-route
restoration punctures the alignment and reopens the timeout-scale path;
the remaining let-spine and predicate boundaries have no isolated puncture.
The exact imported pre-finalization term is unavailable, so finalization is
Unknown even though no generated-field cause was observed. No concrete
transparency constraint produced an alternate selected Expr.

