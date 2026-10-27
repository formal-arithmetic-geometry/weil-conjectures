# WeilConjectures.PurityFiniteSetting.cartierRelativeCoefficientBoundary

## Reason

The original result annotation uses the selected-site category wrappers while the value is
`cartierReducedEtale` in the native module-sheaf category. Applying `Ext.hom` to the result
then compares the wrappers and their derived localizations with the native structures.
The complete proof elaborates but kernel checking exceeds the 60-second file limit.
Use the native Ext endpoints already used by the defining term. The two annotations are
definitionally equal; the value is unchanged. This removes a large instance conversion
without replacing the construction or changing the supported class.

## Old

```lean
def cartierRelativeCoefficientBoundary (P : PurityFiniteSetting.{u}) {D T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) :
    Ext.{u + 1} (P.functorialCupSource false i) (P.functorialCupTwist false T 1) 2 :=
  ProEtale.cartierReducedEtale P.Coefficient P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates i hI
    (P.diagonalExponent_isUnit a)
```

## New

```lean
def cartierRelativeCoefficientBoundary (P : PurityFiniteSetting.{u}) {D T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) :
    Ext.{u + 1}
      ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constantEtale D))
      (P.frameTwistEtale T 1) 2 :=
  ProEtale.cartierReducedEtale P.Coefficient P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates i hI
    (P.diagonalExponent_isUnit a)
```

## Users

`tools/downstream.py Sheaf.Paper.CartierRelativeBoundaryRealization --uses
cartierRelativeCoefficientBoundary` reports no downstream module and this one user.
A full source text search agrees.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CartierRelativeBoundaryRealization | H3 | Its scalar-adjunct and divisor realization proofs use the native result type. |

The item theorem's written statement is preserved. No target statement, target-used
definition, or other module needs adaptation. The annotation is definitionally equal to
its predecessor and introduces no hypothesis or changed mathematical object.

## Status

landed 20261025T123042-L-1827891 2026-10-25 (merge of deliver/H3/Sheaf.Paper.CartierRelativeBoundaryRealization)
