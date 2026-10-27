# CategoryTheory.LocalizedSignedDual.dualProjection

## Reason

The original definition obtains the chosen Hom projection through
`RationalTermHom.ProjectionData`. Checking the differential required transporting
through its large equality of dependent families. A clean complete compile took
54.5 seconds, but delivery exceeded the 60-second limit. Refer directly to the
existing `homComplexπ` API instead. It is precisely the same chosen projection:
`ProjectionData.eq_chosen` fixes the original family to the choice defining
`homComplexπ`. The target transport and every declaration signature are unchanged.

## Old

```lean
def dualProjection (P : Complex R) (q : ℤ) :
    (dual R P).X q ⟶
      SheafOfModules.homObj (R := R) (P.X (-q)) (RationalTermHom.coefficients R) :=
  RationalTermHom.projection R P
    (RationalTermHom.single R (RationalTermHom.coefficients R)) q (-q) 0
      (neg_add_cancel q) ≫
    SheafOfModules.homObjMap.{u, u, u, u} (R := R) (𝟙 (P.X (-q)))
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (RationalTermHom.coefficients R)).hom
```

## New

```lean
def dualProjection (P : Complex R) (q : ℤ) :
    (dual R P).X q ⟶
      SheafOfModules.homObj (R := R) (P.X (-q)) (RationalTermHom.coefficients R) :=
  homComplexπ (R := R) P
    (RationalTermHom.single R (RationalTermHom.coefficients R)) q (-q) 0
      (neg_add_cancel q) ≫
    SheafOfModules.homObjMap.{u, u, u, u} (R := R) (𝟙 (P.X (-q)))
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (RationalTermHom.coefficients R)).hom
```

The source now publicly imports `HomComplexComponents` because the definition uses
its projection API. The proof establishes the surviving projection is invertible
and satisfies the specified signed differential. This is an implementation repair
of the identical mathematical projection; target meanings are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.LocalizedSignedDualPresentation | N3 | Use direct chosen projection API and its product and differential laws. |

Read-only `tools/downstream.py` reports zero downstream modules and only this
module as a textual user of the fully qualified declaration. No consumer needs an
adaptation. Parents whose proofs are unfinished retain the identical interface.

## Status

landed 20261023T151900-L-419067 2026-10-23 (merge of deliver/N3/Sheaf.Algebra.Homology.LocalizedSignedDualPresentation)
