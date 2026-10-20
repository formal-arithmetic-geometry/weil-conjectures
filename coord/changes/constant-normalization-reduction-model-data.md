# AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.ReductionModel

## Reason

Repeated kernel checking of the concrete four-field model expanded the chosen constant
coefficient sheaves and derived-category instances. Abstracting the same four fields over
categories, a functor and a resolving predicate permits the proofs to compile within the
existing single-file limit. The model still consists of a functor, its universal counit,
the universal left-derived-functor property, and invertibility on exactly the original
K-flat complexes. No mathematical hypothesis or conclusion changes.

## Old

```lean
structure ReductionModel (X : Scheme.{u}) where
  functor : DerivedCategory (Modules A X) ⥤ Derived A X
  counit : DerivedCategory.Qh ⋙ functor ⟶ reductionHomotopy I X
  universal : functor.IsLeftDerivedFunctor counit
    (HomotopyCategory.quasiIso (Modules A X) (.up ℤ))
  computes : ∀ P : CochainComplex (Modules A X) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A X) P →
    IsIso (counit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
```

## New

```lean
structure DerivedReductionModelData
    {C : Type c} [Category.{vc} C] [Abelian C] [HasDerivedCategory.{wc} C]
    {D : Type d} [Category.{vd} D] [Abelian D] [HasDerivedCategory.{wd} D]
    (E : C ⥤ D) [E.Additive] (S : CochainComplex C ℤ → Prop) where
  functor : DerivedCategory C ⥤ DerivedCategory D
  counit : DerivedCategory.Qh ⋙ functor ⟶
    E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  universal : functor.IsLeftDerivedFunctor counit (HomotopyCategory.quasiIso C (.up ℤ))
  computes : ∀ P, S P →
    IsIso (counit.app ((HomotopyCategory.quotient C (.up ℤ)).obj P))

abbrev ReductionModel (X : Scheme.{u}) :=
  DerivedReductionModelData (reductionModule I X)
    (CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A X))
```

`ReductionModel` is now an abbreviation for the generic record. Its fields retain their
names and types under elaboration. The structure constructor and generated projection
names belong to `DerivedReductionModelData`; no external consumer uses the old constructor
or projections. The definition `reductionModel` and its selection from `reduction_exists`
are retained. The new generic existence helper is private and fully proved.

## Users

`python3 tools/downstream.py Sheaf.Paper.ConstantTowerDirectImageNormalization --uses
ReductionModel` found only the item itself (three references). A search for qualified
constructor and projection names found no external references. There are 41 transitive
module importers, whose public mathematical interfaces remain unchanged; no forced
adaptations are required. Definitions used by targets transitively include this record,
so the independent reader should review the representational equivalence above.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstantTowerDirectImageNormalization | D9 | Construct the same four-field model through the generic existence theorem. |

## Status

landed 20261020T221128-L-4147542 2026-10-20 (merge of deliver/D9/Sheaf.Paper.ConstantTowerDirectImageNormalization)
