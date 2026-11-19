# FiniteBaseChangeRestrictionMateTransport: nested representation audit

Source: `0676f555de6`, `Algebra/Homology/OpenTensorNormalization/OpenTensorNormalizationData`,
`finite_base_change_restriction_mate_transport`; Lean/Mathlib 4.35.0.
Measurements are reused from `WORKPLAN-EXPERIMENTS.md`; unchanged fixtures
are linked from `probes/nd/`. The original has 4,000,000 heartbeats; the
localized controls below use 400,000. Kernel-only time/heartbeats and
separate instance-synthesis time were unavailable.

## Original context and A records

The checked site is `hb`, argument 49 of `transport_from_unit`, after 48
category, functor, equivalence, adjunction, and mate arguments instantiate
its dependent proposition. Both sides are a `forall M : FiniteModules A X'`
square. The first difference under `Eq` / `Quiver.Hom` /
`ProjectionRestriction.Mod` is supplied `Scheme.ProEt X` versus expected
`Site .ordinary X`; after exposing the mode match, the next category
instance is `Scheme.instCategoryProEt` versus `instCategorySite`.
Section-10 fields shared by the rows: instance depth and field count are
the original, unvaried category/functor hierarchy; the square uses both
equality sides. The selected site/category paths are in D. The source is
elaborated for each variant, but explicit instance terms, synthesis time,
Kernel-only time/heartbeats, and same-term Kernel replay are unavailable.
Prior diagnostics on the original application found 2,226 `Functor.obj`
and 1,168 `PresheafOfModules.obj` Kernel unfolds; these are downstream
activity, not an isolated cost for the site leaf.

| Record | Representation and changed factor | Elaborated pair | Kernel result | Wall s | CPU user+sys s | RSS KB | Same site and obligation | Confidence |
|---|---|---|---|---:|---:|---:|---|---|
| A-FB-0 | original `hb := h` | ProEt/Site at argument 49 | timeout | 89.36 | 89.06+1.05 | 5,743,096 | yes | confirmed site |
| A-FB-T | `hb := fun M => by transport_exact h M` | exact expected proposition | ok | 4.40 | 4.26+0.94 | 2,335,020 | same helper application and square | confirmed transport control |
| A-FB-S | unfold `Site .ordinary` in a diagnostic expected type | first difference moves to category instance | diagnostic only | 3.90 | 3.98+0.67 | 2,530,612 | no Kernel replay at argument 49 | inconclusive for cost |

The first two rows are from the same workplan session. Both source proofs
are elaborated normally; `TransportHB` fixes the proposition at the helper's
expected type but also changes the proof term. The enclosing diagnostic
example ends in `sorry` *after* the checked application, while `After.lean`
checks the full theorem. `Site .ordinary X = X.ProEt` is independently
checked by `rfl`, so the site pair is definitionally equal. This does not
make the transport row a one-leaf A/B symmetry control: the helper's
imported binder is not rebuilt through both site paths. A/A and B/A are
missing. The transport row is the matched within-case fast control, not an
independent nearby declaration.

## B status

No valid depth matrix was obtained. Adding wrapper classes around a separate
`Site` equality would remove the dependent `hb` binder and its 48 preceding
arguments; that would not test this Kernel cost. A future B control must
parameterize the site/category provider inside the same square and replay
the exact instantiated proposition with explicit instance terms. No
nesting-amplification conclusion follows from the retained timings.

## D: representation provenance

| Role | Supplied `hb` | Expected helper binder |
|---|---|---|
| Original declaration | local proof `h` | local `transport_from_unit` after 48 actual arguments |
| Data-bearing structure | `FiniteModules`, `Mod`, square morphisms, concrete equivalences | same square through abstract category and equivalence parameters |
| Site/instance path | concrete `Scheme.ProEt`, `Scheme.instCategoryProEt` | mode-indexed `Site .ordinary`, `instCategorySite` |
| Construction | concrete/local square | generic helper instantiated with concrete functors |
| Let/proof abstraction | neither identified as first producer | neither identified as first producer |

First divergence is the site type under `ProjectionRestriction.Mod`; after
one mode-match exposure it moves to a category instance. The generic helper
and concrete square are the two producers. The square repeats the difference
on both equality sides, but no per-side cost was isolated. D confidence:
strongly supported for provenance; no internal Kernel trace is claimed.

**Evidence level:** the exact expected-proposition transport is locally
causal, but it changes proof construction and does not satisfy strict A
symmetry or explicit Kernel replay. Below section-12 Level 1; no Level 2/3.

## Lead-note follow-up

Fresh matched control: probes/nd/TransportHB.lean checked in 4.38 s
(4.31 s user, 0.90 s system, 2,337,048 KB RSS). The helper's comparison
and mate arguments are explicit in the replay, but its category instances
remain inferred; this is partial A replay evidence.

The assigned B depth harness cannot add instance layers while retaining the
same instantiated dependent hb proposition: doing so either leaves the
stored helper term unchanged or rebuilds the quantified consumer. No valid
depth curve is reported.
