# Native Weil comparison proof components

## Reason

Move comparison data to a shared module so the comparison theorem can import its proof
components without an import cycle. Preserve every existing name, signature, visibility
and mathematical body; the original module publicly imports the new data module.

## Old

The following definitions were in `Sheaf.Paper.NativeWeilDerivedInductionComparison`:

```lean
def exactForgetComparison (P : C ⥤ C) (Q : D ⥤ D) [P.Additive] [Q.Additive]
    [P.IsEquivalence] [Q.IsEquivalence] (L : C ⥤ D) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [HasDerivedCategory.{w} (IsoAlgebra P)] [HasDerivedCategory.{w} (IsoAlgebra Q)]
    (e : L ⋙ Q ≅ P ⋙ L) :
    (IsoAlgebra.mapOfNatIso e).mapDerivedCategory ⋙
        (IsoAlgebra.forget Q).mapDerivedCategory ≅
      (IsoAlgebra.forget P).mapDerivedCategory ⋙ L.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (IsoAlgebra.mapOfNatIsoCompForgetIso e) ≪≫
      Functor.mapDerivedCategoryCompIso _ _


def rightExchange (P : C ⥤ C) (Q : D ⥤ D) [P.Additive] [Q.Additive]
    [P.IsEquivalence] [Q.IsEquivalence] [Abelian.HasKInjectiveResolutions C]
    (L : C ⥤ D) [L.Additive] (e : L ⋙ Q ≅ P ⋙ L) :
    L.rightDerivedFunctor ⋙ Q.mapDerivedCategory ≅
      P.mapDerivedCategory ⋙ L.rightDerivedFunctor :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso L Q).symm ≪≫
    Functor.rightDerivedFunctorNatIso e ≪≫ Functor.rightDerivedFunctorCompIso P L ≪≫
      Functor.isoWhiskerRight P.rightDerivedFunctorIsoMapDerivedCategory L.rightDerivedFunctor


def exactForgetNormalization (P : C ⥤ C) (Q : D ⥤ D) [P.Additive] [Q.Additive]
    [P.IsEquivalence] [Q.IsEquivalence] (L : C ⥤ D) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [HasDerivedCategory.{w} (IsoAlgebra P)] [HasDerivedCategory.{w} (IsoAlgebra Q)]
    (e : L ⋙ Q ≅ P ⋙ L) : Prop :=
  ∀ K : CochainComplex (IsoAlgebra P) ℤ,
    (exactForgetComparison P Q L e).hom.app (_root_.DerivedCategory.Q.obj K) ≫
      L.mapDerivedCategory.map ((IsoAlgebra.forget P).mapDerivedCategoryFactors.hom.app K) ≫
      L.mapDerivedCategoryFactors.hom.app
        (((IsoAlgebra.forget P).mapHomologicalComplex (.up ℤ)).obj K) =
    (IsoAlgebra.forget Q).mapDerivedCategory.map
        ((IsoAlgebra.mapOfNatIso e).mapDerivedCategoryFactors.hom.app K) ≫
      (IsoAlgebra.forget Q).mapDerivedCategoryFactors.hom.app
        (((IsoAlgebra.mapOfNatIso e).mapHomologicalComplex (.up ℤ)).obj K)


abbrev frobenius (T : Scheme.{u}) [T.Over (Spec (.of k₀))] :=
  (WeilSheaf.frobeniusPullback k₀ l T).mapDerivedCategory


abbrev forget (T : Scheme.{u}) [T.Over (Spec (.of k₀))] :=
  (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T)).mapDerivedCategory


abbrev induction (T : Scheme.{u}) [T.Over (Spec (.of k₀))] :=
  (IsoAlgebra.Free.functor (WeilSheaf.frobeniusPullback k₀ l T)).mapDerivedCategory


def structureIso (T : Scheme.{u}) [T.Over (Spec (.of k₀))] :
    forget k₀ l T ⋙ frobenius k₀ l T ≅ forget k₀ l T :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (IsoAlgebra.strNatIso (WeilSheaf.frobeniusPullback k₀ l T))


def inclusion (T : Scheme.{u}) [T.Over (Spec (.of k₀))]
    (A : _root_.DerivedCategory
      (ProEtale.AdicSheaf l (T ↘ Spec (.of k₀)).geometricFiber)) (n : ℤ) :
    IsoAlgebra.Free.obj (frobenius k₀ l T) A n ⟶
      (forget k₀ l T).obj ((induction k₀ l T).obj A) :=
  IsoAlgebra.Free.hom
    (IsoAlgebra.mk _ ((structureIso k₀ l T).app ((induction k₀ l T).obj A)))
    ((IsoAlgebra.freeWeilDerivedAdjunction
      (WeilSheaf.frobeniusPullback k₀ l T)).unit.app A) n


abbrev ordinaryImage :=
  (ProEtale.adicOpenImmersionLowerShriek l
    (Scheme.Hom.geometricFiberMap c.i (comp_over c.i (Spec (.of k₀))))).mapDerivedCategory ⋙
  (ProEtale.adicLowerStar l
    (Scheme.Hom.geometricFiberMap c.g (comp_over c.g (Spec (.of k₀))))).rightDerivedFunctor


def properComparison :
    (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor ⋙ forget k₀ l Y ≅
      forget k₀ l c.Z ⋙ (ProEtale.adicLowerStar l
        (Scheme.Hom.geometricFiberMap c.g (comp_over c.g (Spec (.of k₀))))).rightDerivedFunctor :=
  letI := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (.of k₀)).geometricFiber) ℤ
  letI := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (.of k₀)).geometricFiber) ℤ
  IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso
    (WeilSheaf.frobeniusPullback k₀ l c.Z)
    (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l c.g (comp_over c.g (Spec (.of k₀))))


def openComparison :
    (ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategory ⋙ forget k₀ l c.Z ≅
      forget k₀ l X ⋙ (ProEtale.adicOpenImmersionLowerShriek l
        (Scheme.Hom.geometricFiberMap c.i (comp_over c.i (Spec (.of k₀))))).mapDerivedCategory :=
  exactForgetComparison _ _ _
    (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso
      l c.i (comp_over c.i (Spec (.of k₀))))


def comparison :
    ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c ⋙ forget k₀ l Y ≅
      forget k₀ l X ⋙ ordinaryImage k₀ l f c :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (properComparison k₀ l f c) ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (openComparison k₀ l f c) _ ≪≫
          Functor.associator _ _ _


def exchange :
    ordinaryImage k₀ l f c ⋙ frobenius k₀ l Y ≅
      frobenius k₀ l X ⋙ ordinaryImage k₀ l f c :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (rightExchange _ _ _
      (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso
        l c.g (comp_over c.g (Spec (.of k₀))))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso
            l c.i (comp_over c.i (Spec (.of k₀)))) ≪≫
        Functor.mapDerivedCategoryCompIso _ _) _ ≪≫
    Functor.associator _ _ _



def HeartProperties (T : Scheme.{u}) [T.Over (Spec (.of k₀))] : Prop :=
  IsGrothendieckAbelian.{u + 1}
      (ProEtale.AdicSheaf l (T ↘ Spec (.of k₀)).geometricFiber) ∧
    IsGrothendieckAbelian.{u + 1} (ProEtaleWeilSheaf k₀ l T) ∧
    PreservesFiniteLimits (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T)) ∧
    PreservesFiniteColimits (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T)) ∧
    (forget k₀ l T).IsTriangulated ∧ (forget k₀ l T).ReflectsIsomorphisms ∧
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T)).PreservesKInjectiveComplexes ∧
    (∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J) (forget k₀ l T)) ∧
    (∀ A, ProEtale.DerivedCategory.boundedAdicConstructible l
      (T ↘ Spec (.of k₀)).geometricFiber A →
      ProEtale.DerivedCategory.boundedAdicConstructible l
        (T ↘ Spec (.of k₀)).geometricFiber ((frobenius k₀ l T).obj A)) ∧
    (∀ A, ProEtale.nativeAdicConstructibleLocalizingHull l
      (T ↘ Spec (.of k₀)).geometricFiber A →
      ProEtale.nativeAdicConstructibleLocalizingHull l
        (T ↘ Spec (.of k₀)).geometricFiber ((frobenius k₀ l T).obj A)) ∧
    ∀ A : _root_.DerivedCategory
      (ProEtale.AdicSheaf l (T ↘ Spec (.of k₀)).geometricFiber),
      Nonempty (IsColimit (Cofan.mk
        ((forget k₀ l T).obj ((induction k₀ l T).obj A)) (inclusion k₀ l T A)))


def ProperNormalization : Prop :=
  ∀ J : CochainComplex (ProEtaleWeilSheaf k₀ l c.Z) ℤ, J.IsKInjective →
    (forget k₀ l Y).map
        ((ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj J)) ≫
      (properComparison k₀ l f c).hom.app (_root_.DerivedCategory.Q.obj J) ≫
      (ProEtale.adicLowerStar l
        (Scheme.Hom.geometricFiberMap c.g (comp_over c.g (Spec (.of k₀))))).rightDerivedFunctor.map
        ((IsoAlgebra.forget
          (WeilSheaf.frobeniusPullback k₀ l c.Z)).mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj J)) =
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y)).mapDerivedCategoryFactorsh.hom.app
        (((ProEtaleWeilSheaf.lowerStar k₀ l c.g).mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj J)) ≫
      (ProEtale.adicLowerStar l
        (Scheme.Hom.geometricFiberMap c.g
          (comp_over c.g (Spec (.of k₀))))).rightDerivedFunctorUnit.app
        (((IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l c.Z)).mapHomotopyCategory
          (.up ℤ)).obj ((HomotopyCategory.quotient _ (.up ℤ)).obj J))


def OpenNormalization : Prop :=
  exactForgetNormalization _ _ _
    (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso
      l c.i (comp_over c.i (Spec (.of k₀))))

```

## New

The same definitions, verbatim as above, are in
`Sheaf.Paper.NativeWeilInductionComparisonData`. The original module has:

```lean
public import Sheaf.Paper.NativeWeilInductionComparisonData
```

The data module also proves `exactForgetNormalization_proof`. Its proof uses the standard
localization factorization equations. Proof components prove heart properties and the proper
unit equation, and isolate the localized coproduct and integer induction summands.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NativeWeilDerivedInductionComparison | S1 | Public import preserves all data and the theorem signature. |
| Sheaf.Paper.NativeWeilHeartProperties | S1, new | Imports shared data and the coproduct theorem. |
| Sheaf.Paper.NativeWeilProperNormalization | S1, new | Imports shared data. |
| Sheaf.Paper.NativeWeilFreeCoproduct | S1, new | Imports shared data. |
| Sheaf.Paper.NativeWeilInductionSummands | S1, new | Imports shared data. |

`tools/downstream.py` reports no current downstream Lean modules. The parent DAG proof still
requires the comparison node. Prospective importers see identical data through the public
import; no module held by another group is adapted. Target statements and their data are
unchanged, so this relocation does not alter their meaning.

## Status

landed 20261025T013237-L-3944560 2026-10-25 (merge of deliver/S1/Sheaf.Paper.NativeWeilDerivedInductionComparison)
