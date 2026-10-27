# AlgebraicGeometry.Scheme.sfCbcTensorComparisonNormalized and sfCbcFiniteEvaluationIso

## Reason

Detailed profiling found expensive kernel conversions of standard derived
factorizations to the model's public endpoints. Five data APIs state those
same existing isomorphisms with those endpoints explicitly. The normalization
formula uses `HEq` between the same two composites. Their types are
definitionally equal (the original equation typechecked), so `heq_iff_eq`
identifies this condition with its old equality. This changes no condition
on the comparison isomorphism. Both affected
definitions use the APIs. Unfolding each API gives its old expression; the
normalization condition and every finite evaluation map are unchanged. The mapped
ordinary comparison also uses `Functor.mapHomologicalComplexCompIso` to state
its composite-functor endpoints explicitly; this is Mathlib's canonical
complex comparison, defined by `NatIso.mapHomologicalComplex`. The inverse
comparison for `Iso.refl` reassociates the target into the termwise functors.
Its components are identity maps, so this represents the same chain map.

The finite factorization also gives
the original-coefficient reduction endpoint explicitly, rather than forcing
conversion through the positive-integer index inside each composition.

All existing public signatures, including every theorem and target, remain
identical. The original quotient presentation, reduction and completion unit
are preserved. No consumer statement is weakened or strengthened. No additional
data is chosen, and no proof obligation is added.

## Old

```lean
def sfCbcTensorComparisonNormalized {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    (e : sfCbcModelDerivedExtension j A ⋙ (sfCbcQuotientPresentation X d).tower ≅
      (sfCbcQuotientPresentation U d).tower ⋙ sfCbcDerivedTowerExtension j A) : Prop := by
  letI := sfCbcTensorRightRoute_zero j d
  letI := sfCbcTensorRoute_zero j d
  exact ∀ P : ConstantCompletion.Cx (sfCbcModelRing U A), P.IsAcyclicTensorKFlat →
    (∀ i : ℤ, SheafOfModules.IsFlat (P.X i)) →
      e.hom.app ((ConstantCompletion.Q (sfCbcModelRing U A)).obj P) ≫
          (sfCbcDerivedTowerExtension j A).map
            ((sfCbcQuotientPresentation U d).comparison.app P) ≫
          (sfCbcTowerExtension j A).mapDerivedCategoryFactors.hom.app
            (ConstantCompletion.reductionComplex (proEtaleModelTopology U)
              (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false P) =
        (sfCbcQuotientPresentation X d).tower.map
            ((sfCbcModelExtension j A).mapDerivedCategoryFactors.hom.app P) ≫
          (sfCbcQuotientPresentation X d).comparison.app
            (((sfCbcModelExtension j A).mapHomologicalComplex (.up ℤ)).obj P) ≫
          (ConstantCompletion.TQ (sfCbcModelRing X A)).map
            ((NatIso.mapHomologicalComplex (sfCbcOrdinaryTensorComparison j d)
              (.up ℤ)).hom.app P)
```

```lean
def sfCbcFiniteEvaluationIso (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : CompleteCoefficientDatum A) {K : proEtaleDerivedCategory X A}
    (M : AdicKFlatModel X A K) (n : ℕ) :
    (sfCbcEvaluate X A n).obj ((sfCbcReduction X d).obj K) ≅
      (sfCbcModelDerived X A).functor.obj
        (adicReductionUnderlying X d M ⟨n + 1, Nat.succ_pos n⟩) :=
  (sfCbcEvaluate X A n).mapIso
    ((sfCbcQuotientPresentation X d).tower.mapIso
      ((sfCbcModelDerived X A).functor.mapIso M.realization.symm ≪≫
        (sfCbcModelModules X A).mapDerivedCategoryFactors.app M.complex) ≪≫
      @asIso _ _ _ _ ((sfCbcQuotientPresentation X d).comparison.app
        (((sfCbcModelModules X A).mapHomologicalComplex (.up ℤ)).obj M.complex))
        ((sfCbcQuotientPresentation X d).laws.2.1 _
          (sfCbcModelComplex_kflat X M).1 (sfCbcModelComplex_kflat X M).2)) ≪≫
    (sfCbcEvaluateModule X A n).mapDerivedCategoryFactors.app
      (ConstantCompletion.reductionComplex (proEtaleModelTopology X)
        (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false
          (((sfCbcModelModules X A).mapHomologicalComplex (.up ℤ)).obj M.complex)) ≪≫
    (ConstantCompletion.Q (sfCbcModelRing X A)).mapIso
      (sfCbcFiniteModelIso_existsUnique X d M n).exists.choose ≪≫
    ((sfCbcModelModules X A).mapDerivedCategoryFactors.app
      (adicReductionComplex X d M n)).symm
```

## New

```lean
def sfCbcModelDerivedFactors (X : Scheme.{t}) (A : Type t) [CommRing A] :
    adicLocalization X A ⋙ (sfCbcModelDerived X A).functor ≅
      (sfCbcModelModules X A).mapHomologicalComplex (.up ℤ) ⋙
        ConstantCompletion.Q (sfCbcModelRing X A) :=
  (sfCbcModelModules X A).mapDerivedCategoryFactors
```

```lean
def sfCbcModelExtensionFactors {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] :
    ConstantCompletion.Q (sfCbcModelRing U A) ⋙ sfCbcModelDerivedExtension j A ≅
      (sfCbcModelExtension j A).mapHomologicalComplex (.up ℤ) ⋙
        ConstantCompletion.Q (sfCbcModelRing X A) :=
  (sfCbcModelExtension j A).mapDerivedCategoryFactors
```

```lean
def sfCbcTowerExtensionFactors {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] :
    ConstantCompletion.TQ (sfCbcModelRing U A) ⋙ sfCbcDerivedTowerExtension j A ≅
      (sfCbcTowerExtension j A).mapHomologicalComplex (.up ℤ) ⋙
        ConstantCompletion.TQ (sfCbcModelRing X A) :=
  (sfCbcTowerExtension j A).mapDerivedCategoryFactors
```

```lean
def sfCbcEvaluateFactors (X : Scheme.{t}) (A : Type t) [CommRing A] (n : ℕ) :
    ConstantCompletion.TQ (sfCbcModelRing X A) ⋙ sfCbcEvaluate X A n ≅
      (sfCbcEvaluateModule X A n).mapHomologicalComplex (.up ℤ) ⋙
        ConstantCompletion.Q (sfCbcModelRing X A) :=
  (sfCbcEvaluateModule X A n).mapDerivedCategoryFactors

```

```lean
def sfCbcFiniteModelFactors (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : CompleteCoefficientDatum A) {K : proEtaleDerivedCategory X A}
    (M : AdicKFlatModel X A K) (n : ℕ) :
    (ConstantCompletion.Q (sfCbcModelRing X A)).obj
        (((sfCbcModelModules X A).mapHomologicalComplex (.up ℤ)).obj
          (adicReductionComplex X d M n)) ≅
      (sfCbcModelDerived X A).functor.obj
        (adicReductionUnderlying X d M ⟨n + 1, Nat.succ_pos n⟩) :=
  ((sfCbcModelDerivedFactors X A).app (adicReductionComplex X d M n)).symm

```

```lean
def sfCbcTensorComparisonNormalized {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    (e : sfCbcModelDerivedExtension j A ⋙ (sfCbcQuotientPresentation X d).tower ≅
      (sfCbcQuotientPresentation U d).tower ⋙ sfCbcDerivedTowerExtension j A) : Prop := by
  letI := ConstantCompletion.reductionTower_additive (proEtaleModelTopology X)
    (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false
  letI := ConstantCompletion.reductionTower_additive (proEtaleModelTopology U)
    (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false
  let c := Functor.mapHomologicalComplexCompIso
    (sfCbcOrdinaryTensorComparison j d) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (F := ConstantCompletion.reductionTower (proEtaleModelTopology U)
          (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false)
        (G := sfCbcTowerExtension j A) (Iso.refl _) (.up ℤ)).symm
  exact ∀ P : ConstantCompletion.Cx (sfCbcModelRing U A), P.IsAcyclicTensorKFlat →
    (∀ i : ℤ, SheafOfModules.IsFlat (P.X i)) →
      HEq (e.hom.app ((ConstantCompletion.Q (sfCbcModelRing U A)).obj P) ≫
          (sfCbcDerivedTowerExtension j A).map
            ((sfCbcQuotientPresentation U d).comparison.app P) ≫
          (sfCbcTowerExtensionFactors j A).hom.app
            (ConstantCompletion.reductionComplex (proEtaleModelTopology U)
              (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false P))
        ((sfCbcQuotientPresentation X d).tower.map
            ((sfCbcModelExtensionFactors j A).hom.app P) ≫
          (sfCbcQuotientPresentation X d).comparison.app
            (((sfCbcModelExtension j A).mapHomologicalComplex (.up ℤ)).obj P) ≫
          (ConstantCompletion.TQ (sfCbcModelRing X A)).map
            (c.hom.app P))
```

```lean
def sfCbcFiniteEvaluationIso (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : CompleteCoefficientDatum A) {K : proEtaleDerivedCategory X A}
    (M : AdicKFlatModel X A K) (n : ℕ) :
    (sfCbcEvaluate X A n).obj ((sfCbcReduction X d).obj K) ≅
      (sfCbcModelDerived X A).functor.obj
        (adicReductionUnderlying X d M ⟨n + 1, Nat.succ_pos n⟩) :=
  (sfCbcEvaluate X A n).mapIso
    ((sfCbcQuotientPresentation X d).tower.mapIso
      ((sfCbcModelDerived X A).functor.mapIso M.realization.symm ≪≫
        (sfCbcModelDerivedFactors X A).app M.complex) ≪≫
      @asIso _ _ _ _ ((sfCbcQuotientPresentation X d).comparison.app
        (((sfCbcModelModules X A).mapHomologicalComplex (.up ℤ)).obj M.complex))
        ((sfCbcQuotientPresentation X d).laws.2.1 _
          (sfCbcModelComplex_kflat X M).1 (sfCbcModelComplex_kflat X M).2)) ≪≫
    (sfCbcEvaluateFactors X A n).app
      (ConstantCompletion.reductionComplex (proEtaleModelTopology X)
        (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false
          (((sfCbcModelModules X A).mapHomologicalComplex (.up ℤ)).obj M.complex)) ≪≫
    (ConstantCompletion.Q (sfCbcModelRing X A)).mapIso
      (sfCbcFiniteModelIso_existsUnique X d M n).exists.choose ≪≫
    sfCbcFiniteModelFactors X d M n
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SfCbcExtensionZeroCompletion | K5 | The only direct user of either changed definition. API unfolding gives the old values; no external adaptation is needed. |

The prescribed `tools/downstream.py --uses` searches list only this module as
using either affected definition. The 24 transitive importing modules keep all
existing signatures and public imports and use the same canonical maps. There
are no external adaptations. The equivalent normalization condition retains its two composites,
including all quotient units, scalar actions, complexes and isomorphisms.
The same conclusion holds for identity or empty opens and zero or unbounded
complexes: unfolding the API is the old term without any new hypothesis.

The five APIs are attached to `lem-sf-cbc-extension-zero-completion`, whose
statement is unchanged. They are actual constructions copied from the existing
factorization functors, with no sorry and no existence choice. Their use and the normalization representation in
public definition bodies reopen the target definition-use check and are
submitted for the independent meaning review;
the APIs unfold to the original factors, and the complex-composition
isomorphism represents the same map by the identity and composition laws.
Thus the intended target meaning is unchanged.

## Status

landed 20261026T001932-L-42784 2026-10-26 (merge of deliver/K5/Sheaf.Paper.SfCbcExtensionZeroCompletion)
