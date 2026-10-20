# fourArrowFiniteExchange and typed exchange interfaces

## Reason

The abstract mate calculation needs the geometric comparisons and exchange natural
transformations over the same explicitly typed four-corner functors. Add four
ordinary definitions for the existing integral/finite pullback comparisons and exchange
transformations. Their values are the original ambient ringed comparisons, with
exactly the same coefficient-commutation proofs. Give fourArrowFiniteExchange an
explicit morphism type and use its typed natural-transformation alias. Use the typed
adjunction aliases in fourArrowProjection and the integral exchange alias in the
four-arrow tuple. The existing data and all choices are definitionally unchanged;
the tuple signature is verbatim unchanged. Local preferences select the shared
Abelian data and standard geometric derived-category instance. No global instance
priority, normalization, hypothesis, or target meaning is changed. These interfaces
keep the kernel from comparing expanded instances through unrelated choices.
The independent definition review applies to all changed data interfaces.

## Old

```lean
def fourArrowProjection {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A)
    (H : fourCornerDerived U (adicDatumRing U d)) (n : ℕ) :
    (adicDatumReduction V d n).obj ((fourCornerPushforward f d).obj H) ⟶
      (fourCornerFinitePushforward f d n).obj ((adicDatumReduction U d n).obj H) :=
  (proEtaleRingDerivedAdjunction f ((adicLisseRingSystem V d.ideal).obj (op n))
    ((adicLisseRingSystem U d.ideal).obj (op n)) (fourCornerFiniteIso f d n)).homEquiv _ _
      ((fourArrowReductionPullback f d n).hom.app ((fourCornerPushforward f d).obj H) ≫
        (adicDatumReduction U d n).map
          ((proEtaleRingDerivedAdjunction f (adicDatumRing V d) (adicDatumRing U d)
            (fourCornerCoefficientIso f d)).counit.app H))
```

```lean
def fourArrowFiniteExchange (sq : ChosenCartesianSquare g' f' f g)
    (d : ProEtaleAdicCoefficientDatum A)
    (K : fourCornerDerived X (adicDatumRing X d)) (n : ℕ) :=
  (proEtaleAmbientRingedExchange sq
    ((adicLisseRingSystem X d.ideal).obj (op n))
    ((adicLisseRingSystem Y d.ideal).obj (op n))
    ((adicLisseRingSystem X' d.ideal).obj (op n))
    ((adicLisseRingSystem Y' d.ideal).obj (op n))
    (fourCornerFiniteIso f d n) (fourCornerFiniteIso g d n)
    (fourCornerFiniteIso g' d n) (fourCornerFiniteIso f' d n)
    (fourArrowFiniteCoefficients_comm sq d n)).app ((adicDatumReduction X d n).obj K)
```

```lean
def properBaseChangeFourArrows
    (sq : ChosenCartesianSquare g' f' f g) [IsProper f]
    (d : ProEtaleAdicCoefficientDatum A) (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal)
    (K : fourCornerDerived X (adicDatumRing X d))
    (C : CochainComplex (proEtaleRingModules X (adicDatumRing X d)) ℤ)
    (eC : DerivedCategory.Q.obj C ≅ K)
    (hK : IsCompletedIntrinsicallyDerivedComplete X d r a ha C eC)
    (W : ∀ n : ℕ, ProEtale.FiniteCoefficientDerivedCategoryPlus X (fourArrowQuotient d n))
    (w : ∀ n : ℕ, ProEtale.EtaleOriginWitness X (fourArrowQuotient d n) (W n))
    (e : ∀ n : ℕ, (fourArrowOriginTransport X d n).obj (W n).obj ≅
      (adicDatumReduction X d n).obj K) (n : ℕ) :
    ((properBaseChangeFourCorners g' f' f g sq d r a ha K C eC hK n).1 ≅
      (properBaseChangeFourCorners g' f' f g sq d r a ha K C eC hK n).2.1) ×
    ((properBaseChangeFourCorners g' f' f g sq d r a ha K C eC hK n).2.2.1 ≅
      (properBaseChangeFourCorners g' f' f g sq d r a ha K C eC hK n).2.2.2) ×
    ((properBaseChangeFourCorners g' f' f g sq d r a ha K C eC hK n).1 ⟶
      (properBaseChangeFourCorners g' f' f g sq d r a ha K C eC hK n).2.2.1) ×
    ((properBaseChangeFourCorners g' f' f g sq d r a ha K C eC hK n).2.1 ≅
      (properBaseChangeFourCorners g' f' f g sq d r a ha K C eC hK n).2.2.2) :=
  ((fourCornerFinitePullback g d n).mapIso (fourArrowProjectionIso f d K n),
    fourArrowProjectionIso f' d ((fourCornerPullback g' d).obj K) n ≪≫
      (fourCornerFinitePushforward f' d n).mapIso (fourCornerEReductionIso g' d K n),
    (fourArrowReductionPullback g d n).hom.app ((fourCornerPushforward f d).obj K) ≫
      (adicDatumReduction Y' d n).map
        ((proEtaleAmbientRingedExchange sq (adicDatumRing X d) (adicDatumRing Y d)
          (adicDatumRing X' d) (adicDatumRing Y' d)
          (fourCornerCoefficientIso f d) (fourCornerCoefficientIso g d)
          (fourCornerCoefficientIso g' d) (fourCornerCoefficientIso f' d)
          (fourArrowIntegralCoefficients_comm sq d)).app K),
    @asIso _ _ _ _ (fourArrowFiniteExchange sq d K n)
      (fourArrowFiniteExchange_isIso sq d K n (W n) (w n) (e n)))
```

## New

```lean
def fourArrowProjection {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A)
    (H : fourCornerDerived U (adicDatumRing U d)) (n : ℕ) :
    (adicDatumReduction V d n).obj ((fourCornerPushforward f d).obj H) ⟶
      (fourCornerFinitePushforward f d n).obj ((adicDatumReduction U d n).obj H) :=
  (fourCornerFiniteDerivedAdjunction f d n).homEquiv _ _
      ((fourArrowReductionPullback f d n).hom.app ((fourCornerPushforward f d).obj H) ≫
        (adicDatumReduction U d n).map
          ((fourCornerDerivedAdjunction f d).counit.app H))
```

```lean
def fourArrowIntegralPullbackComparison (sq : ChosenCartesianSquare g' f' f g)
    (d : ProEtaleAdicCoefficientDatum A) :
    fourCornerPullback g d ⋙ fourCornerPullback f' d ≅
      fourCornerPullback f d ⋙ fourCornerPullback g' d :=
  proEtaleAmbientRingedPullbackComparison sq
    (adicDatumRing X d)
    (adicDatumRing Y d)
    (adicDatumRing X' d)
    (adicDatumRing Y' d)
    (fourCornerCoefficientIso f d) (fourCornerCoefficientIso g d)
    (fourCornerCoefficientIso g' d) (fourCornerCoefficientIso f' d)
    (fourArrowIntegralCoefficients_comm sq d)
```

```lean
def fourArrowFinitePullbackComparison (sq : ChosenCartesianSquare g' f' f g)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :
    fourCornerFinitePullback g d n ⋙ fourCornerFinitePullback f' d n ≅
      fourCornerFinitePullback f d n ⋙ fourCornerFinitePullback g' d n :=
  proEtaleAmbientRingedPullbackComparison sq
    ((adicLisseRingSystem X d.ideal).obj (op n))
    ((adicLisseRingSystem Y d.ideal).obj (op n))
    ((adicLisseRingSystem X' d.ideal).obj (op n))
    ((adicLisseRingSystem Y' d.ideal).obj (op n))
    (fourCornerFiniteIso f d n) (fourCornerFiniteIso g d n)
    (fourCornerFiniteIso g' d n) (fourCornerFiniteIso f' d n)
    (fourArrowFiniteCoefficients_comm sq d n)
```

```lean
def fourArrowIntegralExchangeNat (sq : ChosenCartesianSquare g' f' f g)
    (d : ProEtaleAdicCoefficientDatum A) :
    fourCornerPushforward f d ⋙ fourCornerPullback g d ⟶
      fourCornerPullback g' d ⋙ fourCornerPushforward f' d :=
  proEtaleAmbientRingedExchange sq
    (adicDatumRing X d)
    (adicDatumRing Y d)
    (adicDatumRing X' d)
    (adicDatumRing Y' d)
    (fourCornerCoefficientIso f d) (fourCornerCoefficientIso g d)
    (fourCornerCoefficientIso g' d) (fourCornerCoefficientIso f' d)
    (fourArrowIntegralCoefficients_comm sq d)
```

```lean
def fourArrowFiniteExchangeNat (sq : ChosenCartesianSquare g' f' f g)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :
    fourCornerFinitePushforward f d n ⋙ fourCornerFinitePullback g d n ⟶
      fourCornerFinitePullback g' d n ⋙ fourCornerFinitePushforward f' d n :=
  proEtaleAmbientRingedExchange sq
    ((adicLisseRingSystem X d.ideal).obj (op n))
    ((adicLisseRingSystem Y d.ideal).obj (op n))
    ((adicLisseRingSystem X' d.ideal).obj (op n))
    ((adicLisseRingSystem Y' d.ideal).obj (op n))
    (fourCornerFiniteIso f d n) (fourCornerFiniteIso g d n)
    (fourCornerFiniteIso g' d n) (fourCornerFiniteIso f' d n)
    (fourArrowFiniteCoefficients_comm sq d n)
```

```lean
def fourArrowFiniteExchange (sq : ChosenCartesianSquare g' f' f g)
    (d : ProEtaleAdicCoefficientDatum A)
    (K : fourCornerDerived X (adicDatumRing X d)) (n : ℕ) :
    (fourCornerFinitePullback g d n).obj
        ((fourCornerFinitePushforward f d n).obj
            ((adicDatumReduction X d n).obj K)) ⟶
      (fourCornerFinitePushforward f' d n).obj
          ((fourCornerFinitePullback g' d n).obj
              ((adicDatumReduction X d n).obj K)) :=
  (fourArrowFiniteExchangeNat sq d n).app ((adicDatumReduction X d n).obj K)
```

```lean
def properBaseChangeFourArrows
    (sq : ChosenCartesianSquare g' f' f g) [IsProper f]
    (d : ProEtaleAdicCoefficientDatum A) (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal)
    (K : fourCornerDerived X (adicDatumRing X d))
    (C : CochainComplex (proEtaleRingModules X (adicDatumRing X d)) ℤ)
    (eC : DerivedCategory.Q.obj C ≅ K)
    (hK : IsCompletedIntrinsicallyDerivedComplete X d r a ha C eC)
    (W : ∀ n : ℕ, ProEtale.FiniteCoefficientDerivedCategoryPlus X (fourArrowQuotient d n))
    (w : ∀ n : ℕ, ProEtale.EtaleOriginWitness X (fourArrowQuotient d n) (W n))
    (e : ∀ n : ℕ, (fourArrowOriginTransport X d n).obj (W n).obj ≅
      (adicDatumReduction X d n).obj K) (n : ℕ) :
    ((properBaseChangeFourCorners g' f' f g sq d r a ha K C eC hK n).1 ≅
      (properBaseChangeFourCorners g' f' f g sq d r a ha K C eC hK n).2.1) ×
    ((properBaseChangeFourCorners g' f' f g sq d r a ha K C eC hK n).2.2.1 ≅
      (properBaseChangeFourCorners g' f' f g sq d r a ha K C eC hK n).2.2.2) ×
    ((properBaseChangeFourCorners g' f' f g sq d r a ha K C eC hK n).1 ⟶
      (properBaseChangeFourCorners g' f' f g sq d r a ha K C eC hK n).2.2.1) ×
    ((properBaseChangeFourCorners g' f' f g sq d r a ha K C eC hK n).2.1 ≅
      (properBaseChangeFourCorners g' f' f g sq d r a ha K C eC hK n).2.2.2) :=
  ((fourCornerFinitePullback g d n).mapIso (fourArrowProjectionIso f d K n),
    fourArrowProjectionIso f' d ((fourCornerPullback g' d).obj K) n ≪≫
      (fourCornerFinitePushforward f' d n).mapIso (fourCornerEReductionIso g' d K n),
    (fourArrowReductionPullback g d n).hom.app ((fourCornerPushforward f d).obj K) ≫
      (adicDatumReduction Y' d n).map
        ((fourArrowIntegralExchangeNat sq d).app K),
    @asIso _ _ _ _ (fourArrowFiniteExchange sq d K n)
      (fourArrowFiniteExchange_isIso sq d K n (W n) (w n) (e n)))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProperBaseChangeFourArrows | unclaimed | Typed aliases, same canonical maps and tuple data. |
| Sheaf.Paper.FiniteLevelRectangle | Q4 | Uses the maps and typed mate equations. |
| Sheaf.Paper.FiniteReductionPullbackCoherence | new, Q4 | Uses the two pullback comparison aliases. |

The downstream.py --uses scan for fourArrowFiniteExchange lists only
ProperBaseChangeFourArrows among existing repository modules. No module held by
another group is adapted. The two coefficient-commutation proofs are covered by
Q4-finite-rectangle-coefficient-proofs.md.

## Status

landed 20261020T233213-L-905022 2026-10-20 (merge of deliver/Q4/Sheaf.Paper.FiniteLevelRectangle)
