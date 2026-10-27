# proEtaleCartesianStratumSheafComparison

## Reason

The original explicit Eq.rec/composite presentation repeatedly exhausted kernel/file limits
when projected inside the theorem. The new comparison is chosen from a proved unique
factorization. The theorem proEtaleCartesianStratumSheafComparison_eq proves equality
with the original composite. No mathematical content changes. Both module comparison
signatures use definitionally equal functor-object notation to keep conversions small.
The target theorem signature is byte-identical; all six public imports are retained.

## Old

```lean
noncomputable def proEtaleConstantModuleUnderlyingComparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A]
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) :
    (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
        ((proEtaleConstantModuleToAbelianSheaf Y A).obj M) ⟶
      (proEtaleConstantModuleToAbelianSheaf X A).obj
        (proEtaleConstantModulePullback f A M) :=
  ((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _).symm
    ((proEtaleConstantModuleToAbelianSheaf Y A).map
      ((proEtaleConstantRingAdjunction A f).unit.app M))

noncomputable def proEtaleIteratedConstantModuleUnderlyingComparison
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (A : Type u) [CommRing A]
    (M : proEtaleRingModules V (proEtaleConstantRing V A)) :
    (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
        ((proEtaleSheafInverseImage k AddCommGrpCat.{u + 1}).obj
          ((proEtaleConstantModuleToAbelianSheaf V A).obj M)) ⟶
      (proEtaleConstantModuleToAbelianSheaf Z A).obj
        (proEtaleConstantModulePullback h A (proEtaleConstantModulePullback k A M)) :=
  (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).map
      (proEtaleConstantModuleUnderlyingComparison k A M) ≫
    proEtaleConstantModuleUnderlyingComparison h A (proEtaleConstantModulePullback k A M)

noncomputable def proEtaleCartesianStratumSheafComparison
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [∀ T : Scheme.{u}, HasWeakSheafify (ProEt.topology T) D]
    {S Y X : Scheme.{u}} (s : S ⟶ X) (g : Y ⟶ X) :
    proEtaleSheafInverseImage g D ⋙ proEtaleSheafInverseImage (pullback.snd s g) D ≅
      proEtaleSheafInverseImage s D ⋙ proEtaleSheafInverseImage (pullback.fst s g) D :=
  (ProEtale.supportSiteProEtaleComparisonComp D (pullback.snd s g) g).symm ≪≫
    eqToIso (congrArg (fun f ↦ proEtaleSheafInverseImage f D)
      (pullback.condition (f := s) (g := g)).symm) ≪≫
    ProEtale.supportSiteProEtaleComparisonComp D (pullback.fst s g) s

```

## New

```lean
noncomputable def proEtaleConstantModuleUnderlyingComparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A]
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) :
    (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
        ((proEtaleConstantModuleToAbelianSheaf Y A).obj M) ⟶
      (proEtaleConstantModuleToAbelianSheaf X A).obj
        ((proEtaleConstantRingPullback A f).obj M) :=
  ((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _).symm
    ((proEtaleConstantModuleToAbelianSheaf Y A).map
      ((proEtaleConstantRingAdjunction A f).unit.app M))

noncomputable def proEtaleIteratedConstantModuleUnderlyingComparison
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (A : Type u) [CommRing A]
    (M : proEtaleRingModules V (proEtaleConstantRing V A)) :
    (proEtaleSheafInverseImage k AddCommGrpCat.{u + 1} ⋙
      proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
        ((proEtaleConstantModuleToAbelianSheaf V A).obj M) ⟶
      (proEtaleConstantModuleToAbelianSheaf Z A).obj
        ((proEtaleConstantRingPullback A k ⋙ proEtaleConstantRingPullback A h).obj M) :=
  (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).map
      (proEtaleConstantModuleUnderlyingComparison k A M) ≫
    proEtaleConstantModuleUnderlyingComparison h A ((proEtaleConstantRingPullback A k).obj M)

noncomputable def proEtaleCartesianStratumSheafComparison
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [∀ T : Scheme.{u}, HasWeakSheafify (ProEt.topology T) D]
    {S Y X : Scheme.{u}} (s : S ⟶ X) (g : Y ⟶ X) :
    proEtaleSheafInverseImage g D ⋙ proEtaleSheafInverseImage (pullback.snd s g) D ≅
      proEtaleSheafInverseImage s D ⋙ proEtaleSheafInverseImage (pullback.fst s g) D :=
  Classical.choose (stratumSheafComparison_existsUnique D s g).exists

```

The two new data constructions are fixed uniquely by proved theorems: transport equals
eqToIso and the square comparison is fixed by cancelling an isomorphism. No theorem
used for either choice has sorry. The new equality theorem proves extensional equality
with the original definition, so downstream mathematical statements retain their meanings.
Any target review triggered by the implementation change can use this equality.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CartesianStratumModuleRestriction | T1 | Complete proof; defeq helper types and equal square comparison. |

All three tools/downstream.py --uses queries list only this module and zero downstream
modules. A whole-tree declaration search agrees. No other module requires adaptation.

## Status

landed 20261024T191141-L-260151 2026-10-24 (merge of deliver/T1/Sheaf.Paper.CartesianStratumModuleRestriction)
