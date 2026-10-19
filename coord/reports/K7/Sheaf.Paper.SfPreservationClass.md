## What changed

Completed the proof of `AlgebraicGeometry.Scheme.sf_preservation_class` without
changing its statement. The proof applies the existing affine-chart purity bounds,
proves that the restricted nonempty-chart maximum is bounded by the supplied chart
maximum, and widens the resulting interval endpoints by integer arithmetic. It then
assembles constructibility, finite-Tor interval preservation, and finite-Tor membership
uniformly for every coefficient stage `n`.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.Scheme.sf_preservation_class`
(node `thm-sf-preservation-class`). Added 0 holes and split off 0 statements. No
`sorry` remains in the delivered module.

## No longer needed

Removed the proof-only direct imports of
`Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals`,
`Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge`,
`Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`,
`Sheaf.Paper.ExceptionalAdjointAdmissibility`, `Sheaf.Paper.FiniteTorAmplitudeSites`,
`Sheaf.Paper.ProEtaleConstructibleOrigin`, and `Sheaf.Paper.PurityFiniteSetting`.
The public import `Sheaf.Paper.PurityAffineChartBounds` supplies the declarations used
by the statement and proof. No dependency node is globally claimed unreachable.

The proof does not need separate ambient-adjoint, origin-comparison, or coefficient
comparison arguments: those are already encapsulated by the imported affine-chart
purity theorem's interface. No unit route is bypassed.

The updated node retains only `cor-pur-general-admissibility-datum`,
`def-weil-constructible-intervals`, and `def-weil-finite-tor-amplitude` as direct
proof dependencies. The former direct proof dependencies
`def-weil-exceptional-inverse-image`, `lem-sf-proetale-constructible-origin`,
`cor-sf-ambient-adjoint-discharge`, `def-pur-conventions`,
`def-weil-pbc-proetale-site`, and `def-weil-exceptional-adjoint-admissibility`
are not separately applied. Removed the obsolete top-level tool approval for
`lem-sf-proetale-constructible-origin`; the needed finite-stage interpretation is
already part of the corollary's interface.

## Where the brief, the DAG or earlier work was wrong

The interrupted proof's first chart-maximum application supplied a pair whose dependent
index was not elaborated as an element of the original chart family. Introducing the
reindexed source index as a local term makes the pair type explicit; the module then
compiles successfully. No statement or definition was changed.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
