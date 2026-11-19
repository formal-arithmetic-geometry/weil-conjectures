# PR #1630 component classification

The old `pointFiberStageTransitionIso` value in [Before.lean](Before.lean)
compiles in 185.07 user CPU seconds versus 92.14 for [After.lean](After.lean),
with 2,624,356 versus 2,516,012 KB peak RSS. Its final `exact` alone takes
84.8 seconds. Kernel checking totals 8.88 versus 7.08 seconds. **Phase:
elaborator `exact`, not a Kernel A-F case.**

The old proof asks elaboration to identify the component of a composed
natural isomorphism with `β.hom.naturality f` below a bounded-derived-category
inclusion. The [historical PR diagnosis](https://github.com/formal-arithmetic-geometry/weil-conjectures/pull/1630)
prints the comparison of `((rationalStageTransition ⋙
pointFiberStageEquivalence...).map f ≫ isoMk.hom).hom` with
`(rationalStageTransition ⋙ HF).map f ≫ β.hom.app _`. The fixed term uses
`preimageIso` at the functor level, avoiding that component comparison. This
4.35.0 pair covers only the last of the PR's three source changes; the inner
Meta pair is historical evidence, while the time and phase are current replay.
