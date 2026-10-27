## What changed

Filled `AlgebraicGeometry.Scheme.finiteModel_constantScalarExtension_derivedChangeBridge`.
The proof extracts the selected derived-change witness, obtains its derived adjunction from
`SheafOfModules.sheafRingDerivedCoefficientAdjunction`, compares that left adjoint with
`ConstantScalarRealization.derivedExtension` by left-adjoint uniqueness, and evaluates the
comparison on the finite constant model. The canonical `mapDerivedCategoryFactorsh`
isomorphism transports between the derived constant functor object and the explicit
localized finite constant complex. Removed the duplicate private import of
`Sheaf.Paper.ConstantRealizationDerivedScalarExtension`.

## Proved and sorry left

Proved `finiteModel_constantScalarExtension_derivedChangeBridge`; no `sorry`s remain in
the item module and no new `sorry`s were added.

## No longer needed

The proof does not use the previously planned specialized theorem
`ConstantScalarRealization.constantRealizationDerivedScalarExtension` or any finite-model
comparison theorem. No imported module beyond the two existing public imports was removed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan described direct identification of ordinary tensor functors and
left-derived uniqueness. The available generic theorem
`lem-pur-sheaf-ring-derived-coefficient-adjunction` already packages the needed ordinary
identification and supplies an adjunction for the selected witness, so no new tensor
identification lemma is needed.

## New nodes

None.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteModelConstantScalarExtensionDerivedChangeBridge": "a115f7ad48947b4a3b11f0af79f0a1654f683acf"}, "results": {}, "time": "2026-10-28T06:36:55+0800", "transitive": 0, "version": 1}
```

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
