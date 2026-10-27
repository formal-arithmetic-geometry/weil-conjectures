## What changed

Added `Sheaf.WeilSheaf.SmoothDualizingVanishing`, splitting the geometric cohomology-vanishing
input into a named theorem, and proved `smooth_dualizing_concentration` from it using the
canonical `DerivedCategory.isGE_iff` and `isLE_iff` characterizations. The concentration module
imports the split theorem; both modules compile in import order.

## Proved and sorry left

Closed the original `smooth_dualizing_concentration` sorry. Added one strictly smaller sorry,
`smooth_dualizing_homology_vanishing`, whose node is
`lem-sf-weil-smooth-dualizing-homology-vanishing`; it is the geometric vanishing input and is
stated separately so the target proof itself is complete.

## No longer needed

The original plan's direct proof dependencies `lem-pod-separated-finite-type-base-change`,
`lem-sbc-smooth-relative-dimension-permanence`, `lem-sf-weil-native-exceptional-forgetful`,
`lem-sf-adic-qbar-constructible-realization`, and
`cor-pur-adic-and-rational-smooth-dualizing-complexes` are not imported by the concentration
proof directly. The first four are not needed by the completed t-structure conversion; the
latter three remain the declared proof dependencies of the split vanishing theorem.

## Where the brief, the DAG or earlier work was wrong

The DAG described the full native exceptional comparison and coefficient-stage purity inside
one proof step, but no available Lean declaration exposes that comparison at the required
object level. The proof is therefore decomposed at the strictly smaller homology-vanishing
statement; the target's statement is unchanged.

## New nodes

`lem-sf-weil-smooth-dualizing-homology-vanishing` records the new split theorem and its
remaining geometric proof obligation.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.WeilSheaf.SmoothDualizingConcentration": "dea912ddeedaa4cb111838b203862ae33247e573", "Sheaf.WeilSheaf.SmoothDualizingVanishing": "acbd52236fd26ba7cfcbadc19c1636b2e988375c"}, "results": {"WeilConjectures.WeilSheaf.VerdierDual": {"hash": "cbd782ced4a4ed0d3932076da1a163a61a8db8c5", "status": "OK"}}, "seconds": 42, "time": "2026-10-28T04:09:17+0800", "transitive": 0, "version": 1}
```

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
