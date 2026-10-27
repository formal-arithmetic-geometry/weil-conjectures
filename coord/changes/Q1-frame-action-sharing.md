# Frame-action definition sharing

## Reason

The concrete action proof originally spent about 30 seconds in kernel checking because
its repeated Tate coefficient and compact-support expressions unfolded during endpoint
conversion. The two fully constructed generic definitions `frameActionEtaleComposite`
and `frameActionProComposite` retain each original composition in its original order.
The specialized definitions share their coefficient, bounded input, Cartesian square,
canonical coefficient map, and compactification change. `frameActionCoefficient` uses
only the proved defining equality of the bounded input. Neither action is defined by
conjugating the other. The complete module compiles cleanly in 52.7 seconds.
All new definitions are real constructions, with no postponed proof or chosen data.

## Old

```lean
def frameActionEtale (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (l : Γₛ(T, ⊤)))
    (c : Compactification (affineTraceProjection T d))
    (G : Matrix.GeneralLinearGroup (Fin d) Γₛ(T, ⊤)) :=
  (Etale.affineLinearPullbackId (Scheme.finiteTateCoefficient l E n) T).inv.app
      ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) c).obj
          (frameActionInput l E n r hA d T hT).obj) ≫
    (Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (affineTraceLinearMap_isPullback T d G) c).app _ ≫
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (c.ofIsPullback (affineTraceLinearMap_isPullback T d G))).map
        (Etale.affineLinearCoefficientPullback _ (l ^ (r + 1)) hA
          (Etale.projectiveLineTraceTransport _ (pow_pos (Fact.out : l.Prime).pos _) _ hA)
          T (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) d
          (affineTraceLinearMap T d G) (affineTraceLinearMap_over T d G)).hom ≫
    (Etale.rightDerivedLowerShriekOfCompactificationPlusιIso _
      (c.ofIsPullback (affineTraceLinearMap_isPullback T d G)) c).hom.app
        (frameActionInput l E n r hA d T hT)

def frameActionPro (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (l : Γₛ(T, ⊤)))
    (c : Compactification (affineTraceProjection T d))
    (G : Matrix.GeneralLinearGroup (Fin d) Γₛ(T, ⊤)) :=
  (frameActionIdentity l E n T).inv.app
      ((rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) c).obj
          ((comparison (Scheme.finiteTateCoefficient l E n) _).obj
            (frameActionInput l E n r hA d T hT).obj)) ≫
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (affineTraceLinearMap_isPullback T d G) c).app _ ≫
    (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (c.ofIsPullback (affineTraceLinearMap_isPullback T d G))).map
        ((pullback (Scheme.finiteTateCoefficient l E n) (affineTraceLinearMap T d G)).inv.app
            (frameActionInput l E n r hA d T hT).obj ≫
          (comparison (Scheme.finiteTateCoefficient l E n) _).map
            (Etale.affineLinearCoefficientPullback _ (l ^ (r + 1)) hA
              (Etale.projectiveLineTraceTransport _
                (pow_pos (Fact.out : l.Prime).pos _) _ hA)
              T (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) d
              (affineTraceLinearMap T d G) (affineTraceLinearMap_over T d G)).hom) ≫
    (compactSupportSiteComparison _
      (c.ofIsPullback (affineTraceLinearMap_isPullback T d G))).hom.app
        (frameActionInput l E n r hA d T hT) ≫
    (comparison (Scheme.finiteTateCoefficient l E n) T).map
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusιIso _
        (c.ofIsPullback (affineTraceLinearMap_isPullback T d G)) c).hom.app
          (frameActionInput l E n r hA d T hT)) ≫
    (compactSupportSiteComparison _ c).inv.app
      (frameActionInput l E n r hA d T hT)
```

## New

```lean
def frameActionEtaleComposite (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T : Scheme.{u}} [IsNoetherian X] [IsNoetherian T]
    {f : X ⟶ T} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {a : X ⟶ X} (sq : IsPullback a f f (𝟙 T)) (c : Compactification f)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (q : (Etale.ordinaryFinitePullback A a).obj K.obj ⟶ K.obj)
    (z : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).obj K.obj ⟶
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K.obj) :=
  (Etale.affineLinearPullbackId A T).inv.app
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K.obj) ≫
    (Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} A) sq c).app K.obj ≫
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).map q ≫ z

def frameActionProComposite (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T : Scheme.{u}} [IsNoetherian X] [IsNoetherian T]
    {f : X ⟶ T} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {a : X ⟶ X} (sq : IsPullback a f f (𝟙 T)) (c : Compactification f)
    (I : (upperStar (ModuleCat.{u + 1} A) (𝟙 T)).leftDerivedFunctor ≅ 𝟭 _)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (q : (Etale.ordinaryFinitePullback A a).obj K.obj ⟶ K.obj)
    (z : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).obj K.obj ⟶
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K.obj) :=
  I.inv.app ((rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) c).obj ((comparison A X).obj K.obj)) ≫
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} A) sq c).app ((comparison A X).obj K.obj) ≫
    (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).map
        ((pullback A a).inv.app K.obj ≫ (comparison A X).map q) ≫
    (compactSupportSiteComparison A (c.ofIsPullback sq)).hom.app K ≫
    (comparison A T).map z ≫ (compactSupportSiteComparison A c).inv.app K

def frameActionEtale (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (l : Γₛ(T, ⊤)))
    (c : Compactification (affineTraceProjection T d))
    (G : Matrix.GeneralLinearGroup (Fin d) Γₛ(T, ⊤)) :=
  let A := Scheme.finiteTateCoefficient l E n
  let K := frameActionInput l E n r hA d T hT
  let sq := affineTraceLinearMap_isPullback T d G
  let q := frameActionCoefficient l E n r hA d T hT G
  let : IsNoetherian (affineTraceTower T d) := affineTraceNoetherian T d
  frameActionEtaleComposite A sq c K q.hom
    ((Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A
      (c.ofIsPullback sq) c).hom.app K)

def frameActionPro (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (l : Γₛ(T, ⊤)))
    (c : Compactification (affineTraceProjection T d))
    (G : Matrix.GeneralLinearGroup (Fin d) Γₛ(T, ⊤)) :=
  let A := Scheme.finiteTateCoefficient l E n
  let K := frameActionInput l E n r hA d T hT
  let sq := affineTraceLinearMap_isPullback T d G
  let q := frameActionCoefficient l E n r hA d T hT G
  let : IsNoetherian (affineTraceTower T d) := affineTraceNoetherian T d
  frameActionProComposite A sq c (frameActionIdentity l E n T) K q.hom
    ((Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A
      (c.ofIsPullback sq) c).hom.app K)
```

Both generic composites have the displayed original formulas, with arbitrary finite
coefficient ring and bounded input. The specialization uses the actual frame square
and actual canonical Tate pullback; the final compactification comparison is unchanged.

A separate compiled test proves that both final action definitions equal their old
literal formulas, by unfolding and simplifying defining equality transports and
functor/category identity laws (12.4 seconds, no warnings).

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.VectorFrameIntegrationSiteDescent | Q1 | Definition implementation factored; all existing signatures unchanged. |
| Sheaf.Paper.IntegrationExponentTransposeTransport | V7 | Only downstream module; no changed name is used; no adaptation. |

A whole-library source scan finds the changed action names and input name only in this
item. No source-library declaration is changed. Target meanings are preserved by the
same canonical objects and maps; only their definition presentation changes.

## Status

landed 20261025T204819-L-3014229 2026-10-25 (merge of deliver/Q1/Sheaf.Paper.VectorFrameIntegrationSiteDescent)
