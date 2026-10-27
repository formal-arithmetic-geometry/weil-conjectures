## What changed

Closed the `unitCounit_exact` proof up to one strictly smaller shift-compatibility statement. The proof obtains triangulated closure witnesses, transfers ambient commutative-shift and triangulated structures to the restricted direct-image and twisted-pullback functors with `rationalP1_restrictedFunctorExactness`, and combines them with `unitCounit_shift_compatibility`. Added the proved helper module and its DAG node, plus the split compatibility node.

## Proved and sorry left

- Proved `AlgebraicGeometry.ProEtale.RationalP1.unitCounit_exact` from the existing preservation and inversion declarations, the new restriction-exactness lemma, and the split shift-compatibility theorem.
- The only `sorry` left is `AlgebraicGeometry.ProEtale.RationalP1.unitCounit_shift_compatibility`; it is a named decomposition of the final shift calculation for the normalized diagonal unit and trace counit.

## No longer needed

The direct ambient exactness route through the old `LocalizingFunctorChecks.exactRestriction` conclusions is insufficient for the restricted functor witnesses, so the proof uses the new full-subcategory restriction lemma. No imported module was removed; all existing imports remain needed by the definitions and preceding proofs.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof treated exactness of the ambient functors as if it directly supplied `CommShift` and `IsTriangulated` instances for the restricted `push` and `exceptional` functors. The restriction step requires an explicit full-subcategory lift argument. The remaining shift calculation was also too large to safely inline, so it is recorded as a separate, strictly smaller theorem.

## New nodes

- `lem-sfb-rational-p1-restricted-functor-exactness` — proved in `Sheaf.Paper.RationalP1RestrictionExactness`.
- `lem-sfb-rational-p1-unit-counit-shift-compatibility` — split as `unitCounit_shift_compatibility` in the item module.

## Related modules compiled before delivery

3 related module(s) compiled against this delivery by deliver3.py: 3 OK.

```json
{"capped": false, "direct": 3, "left_out": 0, "own": {"Sheaf.Paper.RationalP1RestrictionExactness": "3429cef5a176fdde1badb8667d195c0efec2e9f7", "Sheaf.Paper.RationalP1UnitCounit": "13d3d41003c57405f11cc6b1e7b75a523e27da5c"}, "results": {"Sheaf.Paper.AffineLineAdjunctionAssembly": {"hash": "b184d314427bd2c03760347cc2996cebd55315cd", "status": "OK"}, "Sheaf.Paper.RationalP1KernelContractions": {"hash": "f7b75505a18f395645cc716a7d590b6c67ce8e2a", "status": "OK"}, "Sheaf.Paper.RationalP1Triangle": {"hash": "d1e2d798a7453c8ae09756e0efc410fa7b065150", "status": "OK"}}, "seconds": 49, "time": "2026-10-28T04:44:51+0800", "transitive": 0, "version": 1}
```

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
