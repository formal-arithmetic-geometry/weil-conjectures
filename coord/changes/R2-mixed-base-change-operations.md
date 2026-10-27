# Mixed base-change operations: declaration-preserving extraction

## Reason

The open-factor and constructible-input steps refer to the specified exchange.
Extract its five existing constructions into a public operations module to avoid an
import cycle with the theorem. Every declaration name, signature, attribute and
construction body is preserved. The item publicly imports the operations module,
so existing importers retain the same operations. No source-library module changes.
There is no change to target meanings. The parent node now lists the operations
node as a statement dependency, reflecting the declarations’ new attachment. Private categorical cancellation in the item supports the proof without changing
any construction.

## Old

In `Sheaf.SecSmoothPurity.MixedBaseChange`, these imports were public:

```lean
public import Sheaf.SecSmoothPurity.ReductionExceptional
public import Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange
```

The five constructions were:

```lean
/-- Change derived realization coordinates for an exact fixed-scalar functor.
Source: blueprint mixed-base-change proof, Step 1 (blueprint: det-sp-mixed-base-change). -/
def mixedDerivedTransport (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}}
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⥤
      Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    ((sfIntrinsicModuleEquivalence X A).inverse ⋙ F ⋙
        (sfIntrinsicModuleEquivalence Y A).functor).mapDerivedCategory ≅
      (sfIntrinsicDerivedEquivalence X A).inverse ⋙ F.mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence Y A).functor :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _)

/-- Transport the actual ordinary open base-change isomorphism to intrinsic coefficients.
The realization units cancel at the middle schemes; the outside comparisons are fixed
by their sectionwise units. No inverse is chosen from bare existence.
Source: blueprint mixed-base-change proof, Steps 1 and 3
(blueprint: det-sp-mixed-base-change). -/
def mixedOpenBaseChangeIso (A : Type u) [CommRing A] [Finite A]
    {U' U Z' Z : Scheme.{u}} (h : U' ⟶ U) (j' : U' ⟶ Z')
    (j : U ⟶ Z) (g : Z' ⟶ Z) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback h j' j g) :
    (sfIntrinsicExtensionByZero j A).mapDerivedCategory ⋙
        proEtaleConstantRingDerivedPullback A g ≅
      proEtaleConstantRingDerivedPullback A h ⋙
        (sfIntrinsicExtensionByZero j' A).mapDerivedCategory := by
  let Λ := ULift.{u + 1, u} A
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory
  let J' := (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j').mapDerivedCategory
  let V := (upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategory
  let H := (upperStar (ModuleCat.{u + 1} Λ) h).mapDerivedCategory
  let EU := sfIntrinsicDerivedEquivalence U A
  let EZ := sfIntrinsicDerivedEquivalence Z A
  let EU' := sfIntrinsicDerivedEquivalence U' A
  let EZ' := sfIntrinsicDerivedEquivalence Z' A
  exact Functor.isoWhiskerLeft _ (openSquareDerivedPullbackModel A g) ≪≫
    Functor.isoWhiskerRight (mixedDerivedTransport A _) _ ≪≫
    Functor.isoWhiskerLeft _ (mixedDerivedTransport A _) ≪≫
    Functor.isoWhiskerLeft (EU.inverse ⋙ J) (EZ.funInvIdAssoc (V ⋙ EZ'.functor)) ≪≫
    Functor.isoWhiskerLeft EU.inverse
      (Functor.isoWhiskerRight (ordinaryOpenExtensionBaseChangeIso Λ h j' j g sq)
        EZ'.functor) ≪≫
    Functor.isoWhiskerLeft (EU.inverse ⋙ H) (EU'.funInvIdAssoc (J' ⋙ EZ'.functor)).symm ≪≫
    Functor.isoWhiskerLeft (EU.inverse ⋙ H ⋙ EU'.functor)
      (mixedDerivedTransport A
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j')).symm ≪≫
    Functor.isoWhiskerRight
      (mixedDerivedTransport A (upperStar (ModuleCat.{u + 1} Λ) h)).symm _ ≪≫
    Functor.isoWhiskerRight (openSquareDerivedPullbackModel A h).symm _

/-- The coefficient-independent pullback compactification.
Source: blueprint mixed-base-change Step 1 (blueprint: det-sp-mixed-base-change). -/
abbrev mixedPullbackCompactification
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare h f' f g)
    (c : Compactification f) : Compactification f' :=
  c.ofIsPullback
    (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)

/-- The canonical compact-support exchange, in the same intrinsic constant-ring
coordinates as b. Its proper factor is the normalized counit mate, and its open
factor is the existing ordinary base-change isomorphism transported above.
Source: blueprint mixed-base-change proof Step 4
(blueprint: det-sp-mixed-base-change). -/
def mixedCompactSupportExchange (A : Type u) [CommRing A] [Finite A]
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare h f' f g)
    (c : Compactification f) :
    reductionCompactSupport A c.i c.g ⋙ proEtaleConstantRingDerivedPullback A g ⟶
      proEtaleConstantRingDerivedPullback A h ⋙
        reductionCompactSupport A (mixedPullbackCompactification sq c).i
          (mixedPullbackCompactification sq c).g := by
  let hp := IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  let cp := mixedPullbackCompactification sq c
  let psq : ChosenCartesianSquare (pullback.fst c.g g) (pullback.snd c.g g) c.g g :=
    { w := pullback.condition
      isoPullback := Iso.refl _
      hom_fst := Category.id_comp _
      hom_snd := Category.id_comp _ }
  exact Functor.whiskerLeft (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory
      (directImageConstantExchange A psq) ≫
    Functor.whiskerRight
      (mixedOpenBaseChangeIso A h cp.i c.i (pullback.fst c.g g)
        (c.isPullback_i_ofIsPullback hp)).hom (directImageConstantPush A cp.g)

/-- Pullback on the full intrinsic Dctf categories; the certificate affects only membership.
Source: blueprint mixed-base-change proof Steps 4 and 6
(blueprint: det-sp-mixed-base-change). -/
def mixedCtfPullback (A : Type u) [CommRing A] [Finite A]
    {U V : Scheme.{u}} (g : U ⟶ V)
    (hg : ∀ K : spFiniteConstructibleTorCategory V A,
      spFiniteConstructibleTor U A ((proEtaleConstantRingDerivedPullback A g).obj K.obj)) :=
  (spFiniteConstructibleTor U A).lift
    ((spFiniteConstructibleTor V A).ι ⋙ proEtaleConstantRingDerivedPullback A g) hg
```

## New

The item replaces those two public imports with:

```lean
public import Sheaf.SecSmoothPurity.MixedBaseChangeOperations
public import Sheaf.SecSmoothPurity.ReductionExceptionalObjects
```

The following declarations occur verbatim in
`Sheaf.SecSmoothPurity.MixedBaseChangeOperations`, publicly imported by the item:

```lean
/-- Change derived realization coordinates for an exact fixed-scalar functor.
Source: blueprint mixed-base-change proof, Step 1 (blueprint: det-sp-mixed-base-change). -/
def mixedDerivedTransport (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}}
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⥤
      Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    ((sfIntrinsicModuleEquivalence X A).inverse ⋙ F ⋙
        (sfIntrinsicModuleEquivalence Y A).functor).mapDerivedCategory ≅
      (sfIntrinsicDerivedEquivalence X A).inverse ⋙ F.mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence Y A).functor :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _)

/-- Transport the actual ordinary open base-change isomorphism to intrinsic coefficients.
The realization units cancel at the middle schemes; the outside comparisons are fixed
by their sectionwise units. No inverse is chosen from bare existence.
Source: blueprint mixed-base-change proof, Steps 1 and 3
(blueprint: det-sp-mixed-base-change). -/
def mixedOpenBaseChangeIso (A : Type u) [CommRing A] [Finite A]
    {U' U Z' Z : Scheme.{u}} (h : U' ⟶ U) (j' : U' ⟶ Z')
    (j : U ⟶ Z) (g : Z' ⟶ Z) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback h j' j g) :
    (sfIntrinsicExtensionByZero j A).mapDerivedCategory ⋙
        proEtaleConstantRingDerivedPullback A g ≅
      proEtaleConstantRingDerivedPullback A h ⋙
        (sfIntrinsicExtensionByZero j' A).mapDerivedCategory := by
  let Λ := ULift.{u + 1, u} A
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory
  let J' := (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j').mapDerivedCategory
  let V := (upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategory
  let H := (upperStar (ModuleCat.{u + 1} Λ) h).mapDerivedCategory
  let EU := sfIntrinsicDerivedEquivalence U A
  let EZ := sfIntrinsicDerivedEquivalence Z A
  let EU' := sfIntrinsicDerivedEquivalence U' A
  let EZ' := sfIntrinsicDerivedEquivalence Z' A
  exact Functor.isoWhiskerLeft _ (openSquareDerivedPullbackModel A g) ≪≫
    Functor.isoWhiskerRight (mixedDerivedTransport A _) _ ≪≫
    Functor.isoWhiskerLeft _ (mixedDerivedTransport A _) ≪≫
    Functor.isoWhiskerLeft (EU.inverse ⋙ J) (EZ.funInvIdAssoc (V ⋙ EZ'.functor)) ≪≫
    Functor.isoWhiskerLeft EU.inverse
      (Functor.isoWhiskerRight (ordinaryOpenExtensionBaseChangeIso Λ h j' j g sq)
        EZ'.functor) ≪≫
    Functor.isoWhiskerLeft (EU.inverse ⋙ H) (EU'.funInvIdAssoc (J' ⋙ EZ'.functor)).symm ≪≫
    Functor.isoWhiskerLeft (EU.inverse ⋙ H ⋙ EU'.functor)
      (mixedDerivedTransport A
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j')).symm ≪≫
    Functor.isoWhiskerRight
      (mixedDerivedTransport A (upperStar (ModuleCat.{u + 1} Λ) h)).symm _ ≪≫
    Functor.isoWhiskerRight (openSquareDerivedPullbackModel A h).symm _

/-- The coefficient-independent pullback compactification.
Source: blueprint mixed-base-change Step 1 (blueprint: det-sp-mixed-base-change). -/
abbrev mixedPullbackCompactification
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare h f' f g)
    (c : Compactification f) : Compactification f' :=
  c.ofIsPullback
    (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)

/-- The canonical compact-support exchange, in the same intrinsic constant-ring
coordinates as b. Its proper factor is the normalized counit mate, and its open
factor is the existing ordinary base-change isomorphism transported above.
Source: blueprint mixed-base-change proof Step 4
(blueprint: det-sp-mixed-base-change). -/
def mixedCompactSupportExchange (A : Type u) [CommRing A] [Finite A]
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare h f' f g)
    (c : Compactification f) :
    reductionCompactSupport A c.i c.g ⋙ proEtaleConstantRingDerivedPullback A g ⟶
      proEtaleConstantRingDerivedPullback A h ⋙
        reductionCompactSupport A (mixedPullbackCompactification sq c).i
          (mixedPullbackCompactification sq c).g := by
  let hp := IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  let cp := mixedPullbackCompactification sq c
  let psq : ChosenCartesianSquare (pullback.fst c.g g) (pullback.snd c.g g) c.g g :=
    { w := pullback.condition
      isoPullback := Iso.refl _
      hom_fst := Category.id_comp _
      hom_snd := Category.id_comp _ }
  exact Functor.whiskerLeft (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory
      (directImageConstantExchange A psq) ≫
    Functor.whiskerRight
      (mixedOpenBaseChangeIso A h cp.i c.i (pullback.fst c.g g)
        (c.isPullback_i_ofIsPullback hp)).hom (directImageConstantPush A cp.g)

/-- Pullback on the full intrinsic Dctf categories; the certificate affects only membership.
Source: blueprint mixed-base-change proof Steps 4 and 6
(blueprint: det-sp-mixed-base-change). -/
def mixedCtfPullback (A : Type u) [CommRing A] [Finite A]
    {U V : Scheme.{u}} (g : U ⟶ V)
    (hg : ∀ K : spFiniteConstructibleTorCategory V A,
      spFiniteConstructibleTor U A ((proEtaleConstantRingDerivedPullback A g).obj K.obj)) :=
  (spFiniteConstructibleTor U A).lift
    ((spFiniteConstructibleTor V A).ι ⋙ proEtaleConstantRingDerivedPullback A g) hg
```

The canonical finite-level compact-support module is unused by the new proof.
The sole direct consumer already imports `ReductionExceptional` explicitly and
is checked unchanged against this packet.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SecSmoothPurity.MixedBaseChangeOperations | R2, new | Holds the five preserved operations. |
| Sheaf.SecSmoothPurity.MixedBaseChange | R2 | Publicly imports the extracted operations; theorem type unchanged. |
| Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction | unclaimed in the shared claim records | Uses mixedCtfPullback and mixedCompactSupportExchange through the same public import; no adaptation. |
| Sheaf.SecSmoothPurity.MixedCompactSupportScalar | R2, new | Uses the specified exchange. |
| Sheaf.SecSmoothPurity.MixedBaseChangeInput | R2, new | Uses the actual compact-support comparison. |

## Status

landed 20261026T222750-L-693083 2026-10-26 (merge of deliver/R2/Sheaf.SecSmoothPurity.MixedBaseChange)
