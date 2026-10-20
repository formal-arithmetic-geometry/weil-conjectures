# AlgebraicGeometry.ProEtale.deltaRestrictionNativeTensor, DeltaRestrictionTensorComparison, IsNormalizedDeltaRestrictionTensor

## Reason

Move the three native API declarations verbatim from `Sheaf.Paper.DeltaRestriction` to
`Sheaf.AlgebraicGeometry.ProEtaleDerivedRestrictionClosed`, and publicly import the new
module from the old one. Comparing independently expanded tensor aliases in the
normalization argument exceeded the elaboration limit. Sharing the declarations fixes
the implementation boundary without changing their qualified names, signatures or
bodies. The new module has no dependency on the double-dual construction. No target
statement changes and no external consumer adaptation is required. The original node's
Lean attachment now omits these declarations; the new node's attachment lists them.

## Old

In `Sheaf.Paper.DeltaRestriction`:

```lean
/-- The existing native derived tensor, with its plain bifunctor signature exposed.
Source: blueprint order 2124, proof step 4 (blueprint: lem-weil-delta-restriction). -/
def deltaRestrictionNativeTensor
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (Y : Scheme.{u}) :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
        _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) :=
  MonoidalCategory.curriedTensor _

/-- The type of derived tensor comparisons for ordinary pro-etale inverse image.
Source: blueprint order 2124, proof step 4; Stacks 08JB
(blueprint: lem-weil-delta-restriction). -/
abbrev DeltaRestrictionTensorComparison
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {W Y : Scheme.{u}} (j : W ⟶ Y) :=
  Functor.curry.obj
      ((upperStar A j).mapDerivedCategory.prod
        (upperStar A j).mapDerivedCategory ⋙
          Functor.uncurry.obj (deltaRestrictionNativeTensor A W)) ≅
      Functor.curry.obj (Functor.uncurry.obj
        (deltaRestrictionNativeTensor A Y) ⋙
          (upperStar A j).mapDerivedCategory)

/-- The comparison square with the ordinary homotopy tensor map and localization.
It fixes the derived comparison on every K-flat model and hence everywhere.
Source: blueprint order 2124, proof step 4; Stacks 08JB
(blueprint: lem-weil-delta-restriction). -/
def IsNormalizedDeltaRestrictionTensor
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {W Y : Scheme.{u}} (j : W ⟶ Y)
    (e : DeltaRestrictionTensorComparison A j) : Prop :=
  ∀ P Q : HomotopyCategory
      (Sheaf (Scheme.ProEt.topology Y) A) (.up ℤ),
      (upperStar A j).mapDerivedCategory.map
          (Functor.LaxMonoidal.μ
            (DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology Y) A)) P Q) ≫
        (upperStar A j).mapDerivedCategoryFactorsh.hom.app (P ⊗ Q) ≫
        (DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology W) A)).map
          (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ)
            (upperStar A j)).app P).app Q) =
      (e.inv.app
        ((DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology Y)
          A)).obj P)).app
          ((DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology Y)
            A)).obj Q) ≫
        ((upperStar A j).mapDerivedCategoryFactorsh.hom.app P ⊗ₘ
          (upperStar A j).mapDerivedCategoryFactorsh.hom.app Q) ≫
        Functor.LaxMonoidal.μ
          (DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology W) A))
          (((upperStar A j).mapHomotopyCategory (.up ℤ)).obj P)
          (((upperStar A j).mapHomotopyCategory (.up ℤ)).obj Q)

```

## New

In `Sheaf.AlgebraicGeometry.ProEtaleDerivedRestrictionClosed`, publicly re-exported by
`Sheaf.Paper.DeltaRestriction`:

```lean
/-- The existing native derived tensor, with its plain bifunctor signature exposed.
Source: blueprint order 2124, proof step 4 (blueprint: lem-weil-delta-restriction). -/
def deltaRestrictionNativeTensor
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (Y : Scheme.{u}) :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
        _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) :=
  MonoidalCategory.curriedTensor _

/-- The type of derived tensor comparisons for ordinary pro-etale inverse image.
Source: blueprint order 2124, proof step 4; Stacks 08JB
(blueprint: lem-weil-delta-restriction). -/
abbrev DeltaRestrictionTensorComparison
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {W Y : Scheme.{u}} (j : W ⟶ Y) :=
  Functor.curry.obj
      ((upperStar A j).mapDerivedCategory.prod
        (upperStar A j).mapDerivedCategory ⋙
          Functor.uncurry.obj (deltaRestrictionNativeTensor A W)) ≅
      Functor.curry.obj (Functor.uncurry.obj
        (deltaRestrictionNativeTensor A Y) ⋙
          (upperStar A j).mapDerivedCategory)

/-- The comparison square with the ordinary homotopy tensor map and localization.
It fixes the derived comparison on every K-flat model and hence everywhere.
Source: blueprint order 2124, proof step 4; Stacks 08JB
(blueprint: lem-weil-delta-restriction). -/
def IsNormalizedDeltaRestrictionTensor
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {W Y : Scheme.{u}} (j : W ⟶ Y)
    (e : DeltaRestrictionTensorComparison A j) : Prop :=
  ∀ P Q : HomotopyCategory
      (Sheaf (Scheme.ProEt.topology Y) A) (.up ℤ),
      (upperStar A j).mapDerivedCategory.map
          (Functor.LaxMonoidal.μ
            (DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology Y) A)) P Q) ≫
        (upperStar A j).mapDerivedCategoryFactorsh.hom.app (P ⊗ Q) ≫
        (DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology W) A)).map
          (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ)
            (upperStar A j)).app P).app Q) =
      (e.inv.app
        ((DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology Y)
          A)).obj P)).app
          ((DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology Y)
            A)).obj Q) ≫
        ((upperStar A j).mapDerivedCategoryFactorsh.hom.app P ⊗ₘ
          (upperStar A j).mapDerivedCategoryFactorsh.hom.app Q) ≫
        Functor.LaxMonoidal.μ
          (DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology W) A))
          (((upperStar A j).mapHomotopyCategory (.up ℤ)).obj P)
          (((upperStar A j).mapHomotopyCategory (.up ℤ)).obj Q)

```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DeltaRestriction | B9 | Publicly imports the shared API; existing signatures use identical names. |
| Sheaf.AlgebraicGeometry.ProEtaleDerivedRestrictionClosed | new B9 module | Owns the unchanged native API and the separate closed comparison theorem. |

A repository-wide search for the three moved API names finds only the item module.
All downstream imports of the item continue to see the same public names. No source
library declaration changes. The native API definitions themselves retain their data.

## Status

landed 20261020T221056-L-4141280 2026-10-20 (merge of deliver/B9/Sheaf.Paper.DeltaRestriction)
