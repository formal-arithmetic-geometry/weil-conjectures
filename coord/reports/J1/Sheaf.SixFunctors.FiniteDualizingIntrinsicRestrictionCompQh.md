## What changed

Proved `WeilConjectures.finiteDualizingIntrinsicRestriction_comp_Qh` without
changing its statement. Added a private proof import of
`Sheaf.CategoryTheory.DerivedExactSquareComposition` and fully proved private
helpers in the item module. Updated the item's DAG proof and proof dependencies.

The ordinary comparison is transported along `finiteDualizingRestriction_eq`.
The realization-unit map is surjective because its underlying sheafification
unit is invertible. Checking the two ordinary comparison paths on these sections
proves compatibility with successive restriction. Applying the existing exact
derived square composition theorem, identifying its compositors, and evaluating
at `DerivedCategory.Q.obj P` gives the required equation.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.finiteDualizingIntrinsicRestriction_comp_Qh`
(node `lem-coef-dualizing-intrinsic-restriction-comp-qh-x7`).
No holes added or split off. No `sorry` remains in the item module.

## No longer needed

None. Both original data dependencies remain necessary. No original imports,
nodes, or modules are pruned. The existing proved exact-square composition
lemma supplies the localization step without any new intermediate obligation.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The prior planned comparison pasting is now
implemented by section normalization followed by the proved general exact-square
composition theorem. Generic helpers keep Lean from unfolding the large concrete
coefficient-ring construction during the section calculations. The private
intrinsic compositor uses the canonical inverse composite directly, so its
derived identification does not normalize equality transports in the concrete
coefficient system. The complete proof compiled in 47.1 seconds before removal
of profiling options.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 INFRA.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.SixFunctors.FiniteDualizingIntrinsicRestrictionCompQh": "f54ca17a82cfcb53de745d11f363988500588dbd"}, "results": {"Sheaf.SixFunctors.FiniteDualizingIntrinsicRestrictionComp": {"hash": "e72f4afbad901c00b236fd145d777950ab0d7ff0", "status": "INFRA"}, "Sheaf.SixFunctors.FiniteDualizingIntrinsicRestrictionCompLhs": {"hash": "02b77342219833e0c17f0dedac21535e95f679ea", "status": "INFRA"}}, "seconds": 133, "time": "2026-10-28T11:21:20+0800", "transitive": 0, "version": 1}
```

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
