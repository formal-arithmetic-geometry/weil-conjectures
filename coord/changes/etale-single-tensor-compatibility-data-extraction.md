# AlgebraicGeometry.Etale.EtaleFlatSingleTensorCompatibility

## Reason

The original item with its complete combination proof exceeded the 60-second limit.
Profiling isolated substantial kernel cost in the explicit pairing definitions and
compatibility structure, and in the proof. These existing declarations are moved
verbatim to `Sheaf.AlgebraicGeometry.EtaleFlatSingleTensorCompatibilityData`, which
the item publicly imports. The original three public imports remain. This changes
module ownership only; names, signatures, bodies, attributes, data and equations
are identical. No target meaning changes.

## Old

In `Sheaf.AlgebraicGeometry.EtaleSingleFunctorMonoidalCompatibility`:

```lean
/-- The canonical degree-zero derived pairing computed on a flat left factor.
Source: Stacks Tag 06YQ; (blueprint: lem-pur-etale-single-functor-monoidal-compatibility).
This explicit result type uses the same derived tensor bifunctor as its consumers. -/
@[irreducible]
noncomputable def singleFunctorFlatPairing
    (L M N : Sheaf X.smallEtaleTopology B) (hL : ObjectProperty.flat L)
    (f : L ⊗ M ⟶ N) :
    ((derivedTensor B X).obj ((DerivedCategory.singleFunctor _ 0).obj L)).obj
      ((DerivedCategory.singleFunctor _ 0).obj M) ⟶
        (DerivedCategory.singleFunctor _ 0).obj N :=
  (singleFunctorObjTensorIso (A := B) (X := X) L M hL).hom ≫
    (DerivedCategory.singleFunctor _ 0).map f

/-- Map a pair of arrows with the specified derived tensor bifunctor.
Source: Stacks Tag 06YU;
(blueprint: lem-pur-etale-single-functor-monoidal-compatibility).
The coefficient category stays abstract when this composite is checked. -/
noncomputable def derivedTensorPairMap (X : AlgebraicGeometry.Scheme.{u})
    {K K' L L' : DerivedCategory (Sheaf X.smallEtaleTopology B)}
    (f : K ⟶ K') (g : L ⟶ L') :
    ((derivedTensor B X).obj K).obj L ⟶ ((derivedTensor B X).obj K').obj L' :=
  ((derivedTensor B X).map f).app L ≫ ((derivedTensor B X).obj K').map g

/-- Apply an ordinary pullback arrow after the canonical single/pullback comparison.
Source: Stacks Tag 06YQ;
(blueprint: lem-pur-etale-single-functor-monoidal-compatibility).
No resolution or inverse-image comparison is chosen here. -/
noncomputable def singleFunctorPullbackMap (v : X' ⟶ X)
    {L : Sheaf X.smallEtaleTopology B} {L' : Sheaf X'.smallEtaleTopology B}
    (f : (upperStar B v).obj L ⟶ L') :
    (upperStar B v).leftDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj L) ⟶
      (DerivedCategory.singleFunctor _ 0).obj L' :=
  (singleFunctorCompLeftDerivedUpperStarIso B v).hom.app L ≫
    (DerivedCategory.singleFunctor _ 0).map f

/-- The equations expressing the tensor compatibility of flat degree-zero models.
Source: Stacks Tags 06YQ and 06YU;
(blueprint: lem-pur-etale-single-functor-monoidal-compatibility).
The support sheaves and all ordinary multiplication or support maps are arbitrary inputs. -/
structure EtaleFlatSingleTensorCompatibility (v : X' ⟶ X)
    [(upperStar B v).PreservesFlat] : Prop where
  associativity {L M N P Q R T : Sheaf X.smallEtaleTopology B}
      (hL : ObjectProperty.flat L) (hM : ObjectProperty.flat M)
      (hP : ObjectProperty.flat P)
      (f : L ⊗ M ⟶ P) (g : P ⊗ N ⟶ R) (h : M ⊗ N ⟶ Q)
      (k : L ⊗ Q ⟶ T) (a : R ⟶ T)
      (w : f ▷ N ≫ g ≫ a = (α_ L M N).hom ≫ L ◁ h ≫ k) :
      ((derivedTensor B X).map (singleFunctorFlatPairing L M P hL f)).app
          ((DerivedCategory.singleFunctor _ 0).obj N) ≫
        singleFunctorFlatPairing P N R hP g ≫ (DerivedCategory.singleFunctor _ 0).map a =
      (derivedTensorAssociator B X _ _ _).hom ≫
        ((derivedTensor B X).obj ((DerivedCategory.singleFunctor _ 0).obj L)).map
          (singleFunctorFlatPairing M N Q hM h) ≫ singleFunctorFlatPairing L Q T hL k
  symmetry {L M P Q : Sheaf X.smallEtaleTopology B}
      (hL : ObjectProperty.flat L) (hM : ObjectProperty.flat M)
      (f : L ⊗ M ⟶ P) (g : M ⊗ L ⟶ Q) (a : Q ⟶ P)
      (w : (β_ L M).hom ≫ g ≫ a = f) :
      (((derivedTensorSymmetry B X).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj L)).app
          ((DerivedCategory.singleFunctor _ 0).obj M)) ≫
        singleFunctorFlatPairing M L Q hM g ≫ (DerivedCategory.singleFunctor _ 0).map a =
          singleFunctorFlatPairing L M P hL f
  pullback {L M N : Sheaf X.smallEtaleTopology B}
      {L' M' N' : Sheaf X'.smallEtaleTopology B}
      (hL : ObjectProperty.flat L) (hL' : ObjectProperty.flat L')
      (f : L ⊗ M ⟶ N) (g : L' ⊗ M' ⟶ N')
      (b : (upperStar B v).obj L ⟶ L') (c : (upperStar B v).obj M ⟶ M')
      (d : (upperStar B v).obj N ⟶ N')
      (w : (upperStar B v).map f ≫ d =
        Functor.OplaxMonoidal.δ (upperStar B v) L M ≫ (b ⊗ₘ c) ≫ g) :
      (upperStar B v).leftDerivedFunctor.map (singleFunctorFlatPairing L M N hL f) ≫
          (singleFunctorCompLeftDerivedUpperStarIso B v).hom.app N ≫
            (DerivedCategory.singleFunctor _ 0).map d =
        ((leftDerivedUpperStarTensorComparison B v).app
            ((DerivedCategory.singleFunctor _ 0).obj L)).app
            ((DerivedCategory.singleFunctor _ 0).obj M) ≫
          ((derivedTensor B X').map
            ((singleFunctorCompLeftDerivedUpperStarIso B v).hom.app L ≫
              (DerivedCategory.singleFunctor _ 0).map b)).app _ ≫
          ((derivedTensor B X').obj _).map
            ((singleFunctorCompLeftDerivedUpperStarIso B v).hom.app M ≫
              (DerivedCategory.singleFunctor _ 0).map c) ≫
          singleFunctorFlatPairing L' M' N' hL' g
```

## New

In the new public data module, re-exported by the original item:

```lean
/-- The canonical degree-zero derived pairing computed on a flat left factor.
Source: Stacks Tag 06YQ; (blueprint: lem-pur-etale-single-functor-monoidal-compatibility).
This explicit result type uses the same derived tensor bifunctor as its consumers. -/
@[irreducible]
noncomputable def singleFunctorFlatPairing
    (L M N : Sheaf X.smallEtaleTopology B) (hL : ObjectProperty.flat L)
    (f : L ⊗ M ⟶ N) :
    ((derivedTensor B X).obj ((DerivedCategory.singleFunctor _ 0).obj L)).obj
      ((DerivedCategory.singleFunctor _ 0).obj M) ⟶
        (DerivedCategory.singleFunctor _ 0).obj N :=
  (singleFunctorObjTensorIso (A := B) (X := X) L M hL).hom ≫
    (DerivedCategory.singleFunctor _ 0).map f

/-- Map a pair of arrows with the specified derived tensor bifunctor.
Source: Stacks Tag 06YU;
(blueprint: lem-pur-etale-single-functor-monoidal-compatibility).
The coefficient category stays abstract when this composite is checked. -/
noncomputable def derivedTensorPairMap (X : AlgebraicGeometry.Scheme.{u})
    {K K' L L' : DerivedCategory (Sheaf X.smallEtaleTopology B)}
    (f : K ⟶ K') (g : L ⟶ L') :
    ((derivedTensor B X).obj K).obj L ⟶ ((derivedTensor B X).obj K').obj L' :=
  ((derivedTensor B X).map f).app L ≫ ((derivedTensor B X).obj K').map g

/-- Apply an ordinary pullback arrow after the canonical single/pullback comparison.
Source: Stacks Tag 06YQ;
(blueprint: lem-pur-etale-single-functor-monoidal-compatibility).
No resolution or inverse-image comparison is chosen here. -/
noncomputable def singleFunctorPullbackMap (v : X' ⟶ X)
    {L : Sheaf X.smallEtaleTopology B} {L' : Sheaf X'.smallEtaleTopology B}
    (f : (upperStar B v).obj L ⟶ L') :
    (upperStar B v).leftDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj L) ⟶
      (DerivedCategory.singleFunctor _ 0).obj L' :=
  (singleFunctorCompLeftDerivedUpperStarIso B v).hom.app L ≫
    (DerivedCategory.singleFunctor _ 0).map f

/-- The equations expressing the tensor compatibility of flat degree-zero models.
Source: Stacks Tags 06YQ and 06YU;
(blueprint: lem-pur-etale-single-functor-monoidal-compatibility).
The support sheaves and all ordinary multiplication or support maps are arbitrary inputs. -/
structure EtaleFlatSingleTensorCompatibility (v : X' ⟶ X)
    [(upperStar B v).PreservesFlat] : Prop where
  associativity {L M N P Q R T : Sheaf X.smallEtaleTopology B}
      (hL : ObjectProperty.flat L) (hM : ObjectProperty.flat M)
      (hP : ObjectProperty.flat P)
      (f : L ⊗ M ⟶ P) (g : P ⊗ N ⟶ R) (h : M ⊗ N ⟶ Q)
      (k : L ⊗ Q ⟶ T) (a : R ⟶ T)
      (w : f ▷ N ≫ g ≫ a = (α_ L M N).hom ≫ L ◁ h ≫ k) :
      ((derivedTensor B X).map (singleFunctorFlatPairing L M P hL f)).app
          ((DerivedCategory.singleFunctor _ 0).obj N) ≫
        singleFunctorFlatPairing P N R hP g ≫ (DerivedCategory.singleFunctor _ 0).map a =
      (derivedTensorAssociator B X _ _ _).hom ≫
        ((derivedTensor B X).obj ((DerivedCategory.singleFunctor _ 0).obj L)).map
          (singleFunctorFlatPairing M N Q hM h) ≫ singleFunctorFlatPairing L Q T hL k
  symmetry {L M P Q : Sheaf X.smallEtaleTopology B}
      (hL : ObjectProperty.flat L) (hM : ObjectProperty.flat M)
      (f : L ⊗ M ⟶ P) (g : M ⊗ L ⟶ Q) (a : Q ⟶ P)
      (w : (β_ L M).hom ≫ g ≫ a = f) :
      (((derivedTensorSymmetry B X).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj L)).app
          ((DerivedCategory.singleFunctor _ 0).obj M)) ≫
        singleFunctorFlatPairing M L Q hM g ≫ (DerivedCategory.singleFunctor _ 0).map a =
          singleFunctorFlatPairing L M P hL f
  pullback {L M N : Sheaf X.smallEtaleTopology B}
      {L' M' N' : Sheaf X'.smallEtaleTopology B}
      (hL : ObjectProperty.flat L) (hL' : ObjectProperty.flat L')
      (f : L ⊗ M ⟶ N) (g : L' ⊗ M' ⟶ N')
      (b : (upperStar B v).obj L ⟶ L') (c : (upperStar B v).obj M ⟶ M')
      (d : (upperStar B v).obj N ⟶ N')
      (w : (upperStar B v).map f ≫ d =
        Functor.OplaxMonoidal.δ (upperStar B v) L M ≫ (b ⊗ₘ c) ≫ g) :
      (upperStar B v).leftDerivedFunctor.map (singleFunctorFlatPairing L M N hL f) ≫
          (singleFunctorCompLeftDerivedUpperStarIso B v).hom.app N ≫
            (DerivedCategory.singleFunctor _ 0).map d =
        ((leftDerivedUpperStarTensorComparison B v).app
            ((DerivedCategory.singleFunctor _ 0).obj L)).app
            ((DerivedCategory.singleFunctor _ 0).obj M) ≫
          ((derivedTensor B X').map
            ((singleFunctorCompLeftDerivedUpperStarIso B v).hom.app L ≫
              (DerivedCategory.singleFunctor _ 0).map b)).app _ ≫
          ((derivedTensor B X').obj _).map
            ((singleFunctorCompLeftDerivedUpperStarIso B v).hom.app M ≫
              (DerivedCategory.singleFunctor _ 0).map c) ≫
          singleFunctorFlatPairing L' M' N' hL' g
```

## Users

`tools/downstream.py --uses` was run for all four moved names. The table lists
every module mentioning them. All seven direct importers were checked against this packet; unchanged copies
are removed afterwards. The report records the two pre-existing timeout baselines,
the profiling-only accepted closed-constant consumer, and the private helper
adaptation needed for the shifted-pairing consumer.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleSingleFunctorMonoidalCompatibility | F2 | Same declarations through public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteTwistDegreeZeroEvaluationPairing | unclaimed in local record | Same declarations through public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteTwistDegreeZeroEvaluationPullback | unclaimed in local record | Same declarations through public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteTwistDerivedEvaluationPullback | unclaimed in local record | Same declarations through public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteTwistFlatEvaluationPullback | unclaimed in local record | Same declarations through public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteTwistShiftedFactorComparisons | unclaimed in local record | Same declarations through public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteTwistShiftedPairingPullback | unclaimed in local record | Private helper uses recorded aliases; public interface unchanged. |
| Sheaf.AlgebraicGeometry.FlatSinglePairingSymmetricPullback | unclaimed in local record | Same declarations through public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor | unclaimed in local record | Same declarations through public re-export; no adaptation. |

## Status

landed 20261026T222639-L-677900 2026-10-26 (merge of deliver/F2/Sheaf.AlgebraicGeometry.EtaleSingleFunctorMonoidalCompatibility)
