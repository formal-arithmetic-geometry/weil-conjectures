# PR #1627 classification

Case ID: `AlgebraicGeometry.ProEtaleWeilSheaf.powFunctor`, before/after target prefixes on Lean 4.35.0, master revision `1ef1fddac73e`.

## Phase and cost site

The old value constructs a concrete functor with `obj` and `map` fields; Lean generates/checks its functor-law proofs. With synchronous elaboration it takes 107.63 user CPU seconds and peaks at 7,781,816 KB RSS. Three Kernel checks after the old definition take 27.8, 55.3, and 14.6 seconds. The fixed value applies the generic `IsoAlgebra.liftOfStr` to the same Frobenius-power data and takes 9.38 CPU seconds, 1,837,544 KB RSS, with none of those checks above the 50 ms profiler threshold. Tactic execution is 2.48 versus 1.85 seconds, so the removed work is in Kernel checking, especially the generated field proofs.

## Mechanism

Primary label: **E, representation/interface mismatch**; contributing **A, expensive reduction**. The old functor fields force the Kernel to reconcile objects carried by `IsoAlgebra (frobeniusPowPullback k0 l Y r)` with objects of `ProEtaleWeilSheaf k0 l Y`. The [PR diagnosis](https://github.com/formal-arithmetic-geometry/weil-conjectures/pull/1627) identifies the inner comparison as `frobeniusPowPullback k0 l Y r` versus `WeilSheaf.frobeniusPullback k0 l Y`; the attempted comparison unfolds `adicLowerStar` before failing. This particular conversion pair and its approximately 3.6-second unfold were measured in the historical PR, not dumped afresh in our 4.35.0 run. Our controlled target replacement confirms that the same hand-built interface still produces three large Kernel checks.

The generic helper abstracts both endofunctors while proving the functor laws, so the problematic concrete comparison is absent from the target declaration. Confidence is high for phase and declaration, moderate for the precise inner mechanism on 4.35.0. These probes are diagnostic copies and do not change the library.
