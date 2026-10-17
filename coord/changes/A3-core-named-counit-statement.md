# integralResidue_tensorPullCounit_core: name its existing counit data

## Reason

The original intermediate statement rebuilt the balanced tensor counit by
unfolding the named reduction/restriction functor. Repeating that large concrete
term cost roughly 30 seconds before the public proof calculation, and the full
file exceeded 60 seconds even though the generic diagram proof compiled.
Replace that let body's construction with `residueExchangeTensorCounit`, the
same explicit construction now named in its owning presentation module.

The old and new counits have already been compared by a compiling reflexivity
proof after unfolding the new name. Remove the unused SX and φX lets and the unused outer monoidal-instance let.
The named ordinary coefficient isomorphism already supplies its monoidal instance
internally. Let reduction removes all three from the old proposition. No hypothesis,
universe parameter, or mathematical conclusion changes. This is a presentation change to an intermediate
statement, not a weakening and not a change to a Challenge target.

## Old

```lean
theorem integralResidue_tensorPullCounit_core {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ)) :
    let F := (f)^*⟦integralCoeff ℓ E⟧
    let B := residueExchangeOrdinaryCoefficient ℓ E Y
    let B' := residueExchangeOrdinaryCoefficient ℓ E X
    let A := Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)
    let SX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientMap (integralReductionMap ℓ E) X)
    letI := residueOrdinaryUpperStarMonoidal A f
    let e : F.obj B ≅ B' :=
      residueOrdinaryRestrictedRegularPullIso (integralCoeff ℓ E) A
        (integralReductionMap ℓ E) f
    let eH : (F.mapHomotopyCategory (.up ℤ)).obj (Functor.tensorModelCoefficient B) ≅
      Functor.tensorModelCoefficient B' := (F.mapHomotopyCategoryFactors (.up ℤ)).app
        ((CochainComplex.singleFunctor _ 0).obj B) ≪≫
      (HomotopyCategory.quotient _ (.up ℤ)).mapIso
        ((F.mapCochainComplexSingleFunctor 0).app B ≪≫
          (HomologicalComplex.single _ (.up ℤ) 0).mapIso e)
    let φX := coefficientMap (integralReductionMap ℓ E) X
    let H := residueExchangeReduction ℓ E X ⋙ residueExchangeRestriction ℓ E X
    let εX : DerivedCategory.Qh ⋙ H ⟶
        (tensorLeft B').mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh := by
      unfold H B' residueExchangeOrdinaryCoefficient
        residueExchangeReduction integralReduction residueExchangeRestriction
      exact Mod.tensorPresentationDerivedCounit φX
    let M := DerivedCategory.Qh.obj P
    let a : (residueExchangeUpperStar (integralCoeff ℓ E) f).obj M ⟶
        DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj P) :=
      (residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app P
    let N :=
      ((curriedTensor (residueExchangeDerived (integralCoeff ℓ E) X)).flip.mapIso
        (residueExchangeCoefficientPullIso ℓ E f).symm).hom.app
          ((residueExchangeUpperStar (integralCoeff ℓ E) f).obj M) ≫
        residueExchangeTensorModelTarget ℓ E f P
    let R := H.map a ≫
      εX.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map
      ((homotopyTensorSingleIso B').inv.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
          eH.inv ▷ (F.mapHomotopyCategory (.up ℤ)).obj P)
    N = (residueExchangeTensorIso ℓ E X).inv.app
      ((residueExchangeUpperStar (integralCoeff ℓ E) f).obj M) ≫ R
```

## New

```lean
theorem integralResidue_tensorPullCounit_core {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ)) :
    let F := (f)^*⟦integralCoeff ℓ E⟧
    let B := residueExchangeOrdinaryCoefficient ℓ E Y
    let B' := residueExchangeOrdinaryCoefficient ℓ E X
    let A := Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)
    let e : F.obj B ≅ B' :=
      residueOrdinaryRestrictedRegularPullIso (integralCoeff ℓ E) A
        (integralReductionMap ℓ E) f
    let eH : (F.mapHomotopyCategory (.up ℤ)).obj (Functor.tensorModelCoefficient B) ≅
      Functor.tensorModelCoefficient B' := (F.mapHomotopyCategoryFactors (.up ℤ)).app
        ((CochainComplex.singleFunctor _ 0).obj B) ≪≫
      (HomotopyCategory.quotient _ (.up ℤ)).mapIso
        ((F.mapCochainComplexSingleFunctor 0).app B ≪≫
          (HomologicalComplex.single _ (.up ℤ) 0).mapIso e)
    let H := residueExchangeReduction ℓ E X ⋙ residueExchangeRestriction ℓ E X
    let εX : DerivedCategory.Qh ⋙ H ⟶
        (tensorLeft B').mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
      residueExchangeTensorCounit ℓ E X
    let M := DerivedCategory.Qh.obj P
    let a : (residueExchangeUpperStar (integralCoeff ℓ E) f).obj M ⟶
        DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj P) :=
      (residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app P
    let N :=
      ((curriedTensor (residueExchangeDerived (integralCoeff ℓ E) X)).flip.mapIso
        (residueExchangeCoefficientPullIso ℓ E f).symm).hom.app
          ((residueExchangeUpperStar (integralCoeff ℓ E) f).obj M) ≫
        residueExchangeTensorModelTarget ℓ E f P
    let R := H.map a ≫
      εX.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map
      ((homotopyTensorSingleIso B').inv.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
          eH.inv ▷ (F.mapHomotopyCategory (.up ℤ)).obj P)
    N = (residueExchangeTensorIso ℓ E X).inv.app
      ((residueExchangeUpperStar (integralCoeff ℓ E) f).obj M) ≫ R
```

The proof specializes the fully proved generic normalization using the category
parameters from the presentation constructor on X and Y. In the metaprogram,
the first four parameters are the base category, category instance, abelian
instance and Grothendieck instance; the first nine also include the monoidal,
closed, preadditive, braided and flat-resolution instances. The last four
constructor arguments are the coefficient, functor, counit and its left-derived
property. The resulting application is checked by Lean's kernel. Using these
actual constructor parameters avoids converting between large dictionaries
recovered independently from the ordinary pullback and the derived presentation.
The emitted module compiled in 48.1 seconds and a separate module imported it.

The parent's statement and visibility are unchanged. Its final proof line changes
from `simp only [Iso.hom_inv_id_app_assoc]` to
`simp only [Iso.hom_inv_id_app_assoc, residueExchangeTensorCounit, id_eq]`, unfolding the
new name to the identical old balanced-counit expression.

## Users

`tools/downstream.py --uses integralResidue_tensorPullCounit_core` identifies the
parent below. Its use is checked against the new signature; the replacement let
body is definitionally the old one. The named balanced counit's type and real
construction are recorded in `A3-residue-presentation-defining-equations.md`.
No target statement text changes. The affected target definition closure is
subject to independent statement review together with that construction repair.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralResidueTensorPullCounitCore | A3 | Same tensor factorization, with its original counit term named. |
| Sheaf.Paper.IntegralResidueTensorPullCounitModel | unclaimed | Same factorization used in the parent proof; compile compatibility checked. |

## Status

landed 20261017T213021-L-1678945 2026-10-17 (merge of deliver/A3/Sheaf.Paper.IntegralResidueTensorPullCounitCore)
