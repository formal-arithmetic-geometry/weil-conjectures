## What changed

Proved `AlgebraicGeometry.lfp_unique_infinitesimal_lifts_etale` in its existing module,
with the original signature and public imports. Two proved private helpers compute
the first-order thickening associated to a square-zero ring quotient and establish
surjectivity of a first-order thickening on points. For every affine chart, the main
proof transfers the given scheme lifting property to bijectivity of algebra lifts,
then applies Mathlib's `Algebra.FormallyEtale.iff_comp_bijective` and
`Algebra.Etale.mk`.

Updated the proof plans of both DAG nodes attached to the declaration:
`lem-sfb-lfp-unique-infinitesimal-lifts-etale` and
`lem-per-lfp-unique-infinitesimal-lifts-etale`. The affine restriction, ring lifting,
and finite-presentation argument is the existing Stacks 02HK/02HL/02HM route.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.lfp_unique_infinitesimal_lifts_etale`.
No holes added, no statements split off, and no `sorry` remains in the delivery.
Both private helper theorems are proved. Remote compilation of the proof completed
in 5.7 seconds. The named unused proof binder in the original statement is kept
verbatim, with the unused-variable linter disabled only for this theorem. The proof uses only Mathlib and the
existing concrete definition of `IsFirstOrderThickening`.

## No longer needed

No Lean imports removed; all three existing public imports are used by the
statement and its proof. No module is withdrawn.

For the older per-node plan, the standalone
`lem-weil-pbc-lfp-affine-opens-finite-presentation` is unnecessary: the field
`LocallyOfFinitePresentation.finitePresentation_appLE` supplies precisely that
fact. The dropped `lem-per-ring-square-zero-lifts-cotangent-zero` is unnecessary:
Mathlib's `Algebra.FormallyEtale.iff_comp_bijective` combines the existing
formally-unramified and formally-smooth ring criteria. `def-pc-scheme` is not a
separate proof step; its statement dependency remains unchanged. The current
sfb-node's declared mathematical dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

The original Lean docstring cited the older per twin and a dropped per ring
leaf. It now documents the current sfb route and names both nodes attached to
the same theorem. No mathematical statement was changed. Taking arbitrary
compatible affine opens uses Mathlib's affine-local class fields directly and
covers the empty-source case without any extra hypotheses.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
