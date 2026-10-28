## What changed

Added a proof-only localization chain for the intrinsic finite-dualizing restriction
composition. The item theorem is now proved by applying the natural-transformation
witness to the requested component and using its explicit right-hand component
expansion. The Qh representative statement, the left pasted transformation, and
the localization extension are separate named declarations.

## Proved and sorry left

The item theorem `WeilConjectures.finiteDualizingIntrinsicRestriction_comp` is
proved. Two lower obligations remain as named declarations with `sorry`:

- `finiteDualizingIntrinsicRestriction_comp_Qh` in
  `Sheaf.SixFunctors.FiniteDualizingIntrinsicRestrictionCompQh`;
- `finiteDualizingIntrinsicRestrictionCompLhs` is a complete definition with no
  sorry;
- `finiteDualizingIntrinsicRestriction_comp_natTrans_exists` in
  `Sheaf.SixFunctors.FiniteDualizingIntrinsicRestrictionCompNatTrans`.

The natural-transformation witness includes the right-side component expansion
as part of its proposition. No definition contains `sorry`.

## No longer needed

No existing import or planned dependency was withdrawn. The proof uses only the
finite-dualizing data and normalized DVR tower APIs, plus the three new local
modules. No additional blueprint nodes are needed below the declared Qh and
localization steps.

## Where the brief, the DAG or earlier work was wrong

The original node treated the representative calculation and the extension across
localization as one step. The Lean proof requires these as distinct obligations:
the representative identity, the natural-transformation extension, and the final
component expansion. The target statement and all existing declarations remain
unchanged.

## New nodes

- `lem-coef-dualizing-intrinsic-restriction-comp-qh-x7`: representative-complex
  comparison after derived localization.
- `lem-coef-dualizing-intrinsic-restriction-comp-lhs-x7`: complete left pasted
  natural transformation.
- `lem-coef-dualizing-intrinsic-restriction-comp-nattrans-x7`: localization
  extension with a right-side component witness.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.FiniteDualizingIntrinsicRestrictionComp": "e72f4afbad901c00b236fd145d777950ab0d7ff0", "Sheaf.SixFunctors.FiniteDualizingIntrinsicRestrictionCompLhs": "02b77342219833e0c17f0dedac21535e95f679ea", "Sheaf.SixFunctors.FiniteDualizingIntrinsicRestrictionCompNatTrans": "06c44f0b93ad736dbbbb2f118f314aeb7c335fcd", "Sheaf.SixFunctors.FiniteDualizingIntrinsicRestrictionCompQh": "0418ae85a7468b1f20e85ac2c2538df0124c5213"}, "results": {}, "time": "2026-10-28T08:42:01+0800", "transitive": 0, "version": 1}
```

## Second reading by X7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
