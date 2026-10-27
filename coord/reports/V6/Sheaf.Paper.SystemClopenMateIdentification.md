## What changed

Filled `WeilConjectures.SystemClopenMate.direct_eq` in
`Sheaf.Paper.SystemClopenMateIdentification` by reusing the already proved private
`SystemTensorMate.direct_eq_varying`. A proof-only
`import all Sheaf.Paper.SystemTensorMateArrows` exposes that existing proof locally.
The coefficient rings and quotient maps of the two statements are definitionally equal.

Local irreducibility attributes and transparency-respecting elaboration keep large
exact-derived constructions folded in the two existing identification statements.
All declaration signatures, definition bodies, public imports and docstrings are unchanged.

## Proved and sorry left

Closed one of the original three holes:

- `WeilConjectures.SystemClopenMate.direct_eq`, proved from the existing
  `WeilConjectures.SystemTensorMate.direct_eq_varying`.

Two original holes remain unchanged, both attached to
`lem-pur-system-clopen-mate-identification`:

- `WeilConjectures.SystemClopenMate.systemClopenMateIdentification`.
- `WeilConjectures.IntegralSystemRealization.systemClopenRealizationMateIdentification`.

No holes were added or split off. No axiom or new public declaration is introduced.

## No longer needed

None. No imports, modules or DAG dependencies are withdrawn. Both identification
statements and their existing proof plans remain needed.

## Where the brief, the DAG or earlier work was wrong

The existing private `direct_eq_varying` already proves `direct_eq`, as the earlier
statement review observed. Lean's proof-only `import all` permits direct reuse without
changing that source module's visibility or repeating its sheafification argument.

The existing ambient localization theorem supplies the realization component formula.
A generic mate formula was proved and its concrete application closed the tactic goals,
but the resulting proof repeatedly exceeded the kernel-checking time budget. That
unverified realization proof is not delivered; the original named hole remains.
The ambient theorem uses `E : Type u`, whereas the strict-system statement uses
`E : Type (u + 1)` with schemes of universe `u`, preventing direct specialization to
the other remaining hole. No definition or mathematical statement was changed.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
