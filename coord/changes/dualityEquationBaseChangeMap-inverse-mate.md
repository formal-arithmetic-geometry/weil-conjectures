# AlgebraicGeometry.dualityEquationBaseChangeMap

## Reason

The assigned item is a class-2 definition repair, not a theorem with a direct sorry.
The first worker copied it unchanged and missed coord/hollow-definitions.md.
Construct the map directly as the mate of the inverse ordinary base-change square.
This removes the two auxiliary pullback adjunctions and their fresh counit choices.
The generic secondMate_formula already proved in QCohInverseBaseChangeMate identifies
this construction with the old body for *any* auxiliary adjunctions; a scratch copy
rechecks that identity independently. Thus the resulting morphism is unchanged.
No hypotheses, universes, conclusion or existing signature change.

Replace public Adjunction.Restrict by proof-only Adjunction.Mates, as requested
in return A9. The statement does not need mateEquiv. The removed Restrict import was only needed for the
eliminated auxiliary constructions. No new public declaration or new hole is introduced.

## Old

```lean
noncomputable def dualityEquationBaseChangeMap
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Y' : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (f : X ⟶ Y) (g : Y' ⟶ Y)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (a' : schemeDerivedQCohCategory Y' ⥤ schemeDerivedQCohCategory (pullback f g))
    (adjf : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y f).fst
        E.obj E.property) ⊣ a)
    (adjf' : (schemeDerivedQCohProperty Y').lift
      ((schemeDerivedQCohProperty (pullback f g)).ι ⋙
        schemeDerivedDirectImage (pullback.snd f g))
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
        (pullback.snd f g) _ _).fst E.obj E.property) ⊣ a')
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition E.obj))
    (K : schemeDerivedQCohCategory Y) :
    ((schemeDerivedQCohProperty (pullback f g)).lift
        ((schemeDerivedQCohProperty X).ι ⋙ derivedPullback (pullback.fst f g))
        (fun E ↦ (derivedPullback_tensor_preserve_QCoh (pullback.fst f g)).1
          E.obj E.property)).obj (a.obj K) ⟶
      a'.obj (((schemeDerivedQCohProperty Y').lift
        ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback g)
        (fun E ↦ (derivedPullback_tensor_preserve_QCoh g).1 E.obj E.property)).obj K) :=
  let PX := schemeDerivedQCohProperty X
  let PY := schemeDerivedQCohProperty Y
  let PY' := schemeDerivedQCohProperty Y'
  let PX' := schemeDerivedQCohProperty (pullback f g)
  let Lg := PY'.lift (PY.ι ⋙ derivedPullback g)
    (fun E ↦ (derivedPullback_tensor_preserve_QCoh g).1 E.obj E.property)
  let LgX := PX'.lift (PX.ι ⋙ derivedPullback (pullback.fst f g))
    (fun E ↦ (derivedPullback_tensor_preserve_QCoh (pullback.fst f g)).1 E.obj E.property)
  let Rg := PY.lift (PY'.ι ⋙ schemeDerivedDirectImage g)
    (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint Y' Y g).fst E.obj E.property)
  let RgX := PX.lift (PX'.ι ⋙ schemeDerivedDirectImage (pullback.fst f g))
    (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
      (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
      (pullback.fst f g) _ _).fst E.obj E.property)
  let Rf := PY.lift (PX.ι ⋙ schemeDerivedDirectImage f)
    (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y f).fst E.obj E.property)
  let Rf' := PY'.lift (PX'.ι ⋙ schemeDerivedDirectImage (pullback.snd f g))
    (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
      (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
      (pullback.snd f g) _ _).fst E.obj E.property)
  let adjg : Lg ⊣ Rg := Adjunction.restrictFullyFaithful
    (Classical.choose (exists_schemeDerivedAdjunction g
      (hAdd := (Classical.choose exists_derivedPullbackComposition) g)
      ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition))
        g)
      ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) g)))
    PY.fullyFaithfulι PY'.fullyFaithfulι
    (PY'.liftCompιIso _ _).symm (PY.liftCompιIso _ _).symm
  let adjgX : LgX ⊣ RgX := Adjunction.restrictFullyFaithful
    (Classical.choose (exists_schemeDerivedAdjunction (pullback.fst f g)
      (hAdd := (Classical.choose exists_derivedPullbackComposition) (pullback.fst f g))
      ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition))
        (pullback.fst f g))
      ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) (pullback.fst f g))))
    PX.fullyFaithfulι PX'.fullyFaithfulι
    (PX'.liftCompιIso _ _).symm (PX.liftCompιIso _ _).symm
  let β : Rf ⋙ Lg ⟶ LgX ⋙ Rf' :=
    { app := fun E ↦ ObjectProperty.homMk
        (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
          pullback.condition E.obj)
      naturality := fun E F φ ↦ by
        ext
        have gen : ∀ (adj' : derivedPullback (pullback.snd f g) ⊣
              schemeDerivedDirectImage (pullback.snd f g))
            (adjF : derivedPullback f ⊣ schemeDerivedDirectImage f)
            (c1 : derivedPullback g ⋙ derivedPullback (pullback.snd f g) ≅
              derivedPullback (pullback.snd f g ≫ g))
            (c2 : derivedPullback f ⋙ derivedPullback (pullback.fst f g) ≅
              derivedPullback (pullback.fst f g ≫ f)),
            (derivedPullback g).map ((schemeDerivedDirectImage f).map φ.hom) ≫
              adj'.homEquiv _ _ (c1.hom.app ((schemeDerivedDirectImage f).obj F.obj) ≫
                eqToHom (congrArg (fun k => (derivedPullback k).obj
                  ((schemeDerivedDirectImage f).obj F.obj)) pullback.condition.symm) ≫
                c2.inv.app ((schemeDerivedDirectImage f).obj F.obj) ≫
                (derivedPullback (pullback.fst f g)).map (adjF.counit.app F.obj)) =
            adj'.homEquiv _ _ (c1.hom.app ((schemeDerivedDirectImage f).obj E.obj) ≫
                eqToHom (congrArg (fun k => (derivedPullback k).obj
                  ((schemeDerivedDirectImage f).obj E.obj)) pullback.condition.symm) ≫
                c2.inv.app ((schemeDerivedDirectImage f).obj E.obj) ≫
                (derivedPullback (pullback.fst f g)).map (adjF.counit.app E.obj)) ≫
              (schemeDerivedDirectImage (pullback.snd f g)).map
                ((derivedPullback (pullback.fst f g)).map φ.hom) := by
          intro adj' adjF c1 c2
          have key : ∀ (k k' : pullback f g ⟶ Y) (e : k = k')
              {A B : schemeDerivedCategory Y} (u : A ⟶ B)
              {Z : schemeDerivedCategory (pullback f g)}
              (r : (derivedPullback k').obj B ⟶ Z),
              (derivedPullback k).map u ≫
                  eqToHom (congrArg (fun k => (derivedPullback k).obj B) e) ≫ r =
                eqToHom (congrArg (fun k => (derivedPullback k).obj A) e) ≫
                  (derivedPullback k').map u ≫ r := by
            rintro k _ rfl A B u Z r; simp
          rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
          congr 1
          simp only [Category.assoc, ← Functor.map_comp]
          rw [Functor.map_comp, ← Functor.comp_map, NatTrans.naturality_assoc,
            key _ _ pullback.condition.symm, c2.inv.naturality_assoc, Functor.comp_map,
            ← Functor.map_comp, ← Functor.map_comp]
          erw [adjF.counit.naturality]
          rfl
        exact gen _ _ _ _ }
  have : ∀ E, IsIso (β.app E) := fun E ↦
    @Functor.FullyFaithful.isIso_of_isIso_map _ _ _ _ _ PY'.fullyFaithfulι _ _ (β.app E) (hβ E)
  have : IsIso β := NatIso.isIso_of_isIso_app β
  LgX.map (a.map (adjg.unit.app K)) ≫
    LgX.map (inv ((conjugateEquiv (adjgX.comp adjf') (adjf.comp adjg) β).app (Lg.obj K))) ≫
      adjgX.counit.app (a'.obj (Lg.obj K))

end AlgebraicGeometry
```

## New

```lean
noncomputable def dualityEquationBaseChangeMap
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Y' : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (f : X ⟶ Y) (g : Y' ⟶ Y)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (a' : schemeDerivedQCohCategory Y' ⥤ schemeDerivedQCohCategory (pullback f g))
    (adjf : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y f).fst
        E.obj E.property) ⊣ a)
    (adjf' : (schemeDerivedQCohProperty Y').lift
      ((schemeDerivedQCohProperty (pullback f g)).ι ⋙
        schemeDerivedDirectImage (pullback.snd f g))
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
        (pullback.snd f g) _ _).fst E.obj E.property) ⊣ a')
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition E.obj))
    (K : schemeDerivedQCohCategory Y) :
    ((schemeDerivedQCohProperty (pullback f g)).lift
        ((schemeDerivedQCohProperty X).ι ⋙ derivedPullback (pullback.fst f g))
        (fun E ↦ (derivedPullback_tensor_preserve_QCoh (pullback.fst f g)).1
          E.obj E.property)).obj (a.obj K) ⟶
      a'.obj (((schemeDerivedQCohProperty Y').lift
        ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback g)
        (fun E ↦ (derivedPullback_tensor_preserve_QCoh g).1 E.obj E.property)).obj K) :=
  let PX := schemeDerivedQCohProperty X
  let PY := schemeDerivedQCohProperty Y
  let PY' := schemeDerivedQCohProperty Y'
  let PX' := schemeDerivedQCohProperty (pullback f g)
  let Lg := PY'.lift (PY.ι ⋙ derivedPullback g)
    (fun E ↦ (derivedPullback_tensor_preserve_QCoh g).1 E.obj E.property)
  let LgX := PX'.lift (PX.ι ⋙ derivedPullback (pullback.fst f g))
    (fun E ↦ (derivedPullback_tensor_preserve_QCoh (pullback.fst f g)).1 E.obj E.property)
  let Rf := PY.lift (PX.ι ⋙ schemeDerivedDirectImage f)
    (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y f).fst E.obj E.property)
  let Rf' := PY'.lift (PX'.ι ⋙ schemeDerivedDirectImage (pullback.snd f g))
    (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
      (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
      (pullback.snd f g) _ _).fst E.obj E.property)
  let β : Rf ⋙ Lg ⟶ LgX ⋙ Rf' :=
    { app := fun E ↦ ObjectProperty.homMk
        (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
          pullback.condition E.obj)
      naturality := fun E F φ ↦ by
        ext
        have gen : ∀ (adj' : derivedPullback (pullback.snd f g) ⊣
              schemeDerivedDirectImage (pullback.snd f g))
            (adjF : derivedPullback f ⊣ schemeDerivedDirectImage f)
            (c1 : derivedPullback g ⋙ derivedPullback (pullback.snd f g) ≅
              derivedPullback (pullback.snd f g ≫ g))
            (c2 : derivedPullback f ⋙ derivedPullback (pullback.fst f g) ≅
              derivedPullback (pullback.fst f g ≫ f)),
            (derivedPullback g).map ((schemeDerivedDirectImage f).map φ.hom) ≫
              adj'.homEquiv _ _ (c1.hom.app ((schemeDerivedDirectImage f).obj F.obj) ≫
                eqToHom (congrArg (fun k => (derivedPullback k).obj
                  ((schemeDerivedDirectImage f).obj F.obj)) pullback.condition.symm) ≫
                c2.inv.app ((schemeDerivedDirectImage f).obj F.obj) ≫
                (derivedPullback (pullback.fst f g)).map (adjF.counit.app F.obj)) =
            adj'.homEquiv _ _ (c1.hom.app ((schemeDerivedDirectImage f).obj E.obj) ≫
                eqToHom (congrArg (fun k => (derivedPullback k).obj
                  ((schemeDerivedDirectImage f).obj E.obj)) pullback.condition.symm) ≫
                c2.inv.app ((schemeDerivedDirectImage f).obj E.obj) ≫
                (derivedPullback (pullback.fst f g)).map (adjF.counit.app E.obj)) ≫
              (schemeDerivedDirectImage (pullback.snd f g)).map
                ((derivedPullback (pullback.fst f g)).map φ.hom) := by
          intro adj' adjF c1 c2
          have key : ∀ (k k' : pullback f g ⟶ Y) (e : k = k')
              {A B : schemeDerivedCategory Y} (u : A ⟶ B)
              {Z : schemeDerivedCategory (pullback f g)}
              (r : (derivedPullback k').obj B ⟶ Z),
              (derivedPullback k).map u ≫
                  eqToHom (congrArg (fun k => (derivedPullback k).obj B) e) ≫ r =
                eqToHom (congrArg (fun k => (derivedPullback k).obj A) e) ≫
                  (derivedPullback k').map u ≫ r := by
            rintro k _ rfl A B u Z r; simp
          rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
          congr 1
          simp only [Category.assoc, ← Functor.map_comp]
          rw [Functor.map_comp, ← Functor.comp_map, NatTrans.naturality_assoc,
            key _ _ pullback.condition.symm, c2.inv.naturality_assoc, Functor.comp_map,
            ← Functor.map_comp, ← Functor.map_comp]
          erw [adjF.counit.naturality]
          rfl
        exact gen _ _ _ _ }
  have : ∀ E, IsIso (β.app E) := fun E ↦
    @Functor.FullyFaithful.isIso_of_isIso_map _ _ _ _ _ PY'.fullyFaithfulι _ _ (β.app E) (hβ E)
  have : IsIso β := NatIso.isIso_of_isIso_app β
  (mateEquiv adjf adjf' (inv β)).app K

end AlgebraicGeometry
```

## Users

The table lists every transitive importer returned by tools/downstream.py. The 24
external modules mentioning the declaration all refer to the same morphism, since
secondMate_formula proves equality with the old construction without geometric
hypotheses. In particular, this changes no target's mathematical meaning. This is
a definition used in the target import closure, so the target statement review is
reopened and should record this equality-preserving construction change. Existing
Challenge.lean and all declaration signatures are unchanged.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | Y3 | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | N2 | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.FlatPrecomposePus | unclaimed | Forced proof adaptation: use mateEquiv_counit for the inverse square and cancel β; signatures unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.HorizontalDualityMateCommutativity | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.HorizontalDualityMateComparisons | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.HorizontalDualityMatePasting | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.HorizontalInverseSquareFixedPasting | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.HorizontalOrdinaryForwardFixedPasting | E3 | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.HorizontalOrdinaryInverseFixedPasting | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.HorizontalRectangleInverseMateFixedTransport | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.NewBaseOpenMateFactorization | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso | unclaimed | Forced proof adaptation: use mateEquiv_counit for the inverse square and cancel β; signatures unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso | unclaimed | Forced proof adaptation: construct proof-local open adjunctions and recover the factorization by iterated mates; signatures unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.QCohInverseBaseChangeMate | unclaimed | Forced proof adaptation: final secondMate_formula application replaced with rfl; signature unchanged. |
| Sheaf.AlgebraicGeometry.RectangleInverseBaseChangeMateTransport | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.RectangleOrdinaryGeometricComparisons | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.RectangleOrdinaryGeometricDirect | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.RectangleOrdinaryGeometricPullback | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.RectangleOrdinaryPastingComparisons | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.RectangleQCohComparisonLifts | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.RectangleQCohOrdinaryCompatibility | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.RightAdjointMateAffineOpenIsIso | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.RightAdjointMateNewBaseOpen | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpen | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpenFactorization | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.RightAdjointMateSchemeIsoTransport | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.RightAdjointMateSchemeIsoTransportBase | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.RightAdjointMateSchemeIsoTransportMate | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.RightAdjointMateSuccessiveBaseChange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.SchemeIsoInverseBaseChangeTransport | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.SchemeIsoLiftedComparisonCounit | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.SchemeIsoSecondMateNormalizedSquare | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| TargetsCheck | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Statements unchanged: equal arrow by the generic iterated-mates identity. |


Return A10 additionally forces the following proof-only changes (all three modules
are unclaimed in this checkout's claim records):

- FlatPrecomposePus: original lines 168–169 extract deleted lets and fail with
  `Unknown identifier adjgX`, `Unknown identifier β` and a type mismatch for adjg.
  Replace the extraction with the current nine lets, apply `mateEquiv_counit`
  to `inv β`, precompose by β and cancel its inverse. Add a proof-only Mates import.
  Its private mate_counit helper and every public signature stay unchanged.
- ProperFlatGlobalHomCompositeIso: original lines 176–178 fail analogously at
  composite_mate_counit. Make the same counit-square repair, with LLg in place of Lg,
  and add a proof-only Mates import. All other proof steps stay unchanged.
- ProperFlatOpenSquareMateIso: original line 161 extracts deleted lets, so Rg
  gets the wrong functor type and adjg becomes an IsIso proof; later references
  fail with `Invalid field unit`, type mismatches and an unsolved inverse-mate goal.
  Extract only the current lets. Construct the two open direct-image lifts and
  their restricted adjunctions locally as proof tools. The existing private
  secondMate_formula from QCohInverseBaseChangeMate, accessed using a proof-only
  import all, rewrites the public inverse mate to its three-factor formula. The original
  geometric restriction/unit proof then applies without changing its hypotheses
  or conclusion. Add proof-only import all QCohInverseBaseChangeMate and Restrict imports. No fresh choice enters
  the public definition: the identity holds for any auxiliary adjunctions.

The proof records of the three forced modules are updated to describe these
calculations. No statement, visibility or definition in the adapted modules changes.
The originals were compiled individually against the changed dependency overlay;
the failures are recorded in report.md. The adapted delivery is compiled as a set.

Return X-503ae: remove the duplicate private open_secondMate_formula and reuse
QCohInverseBaseChangeMate.secondMate_formula through import all. No existing
signature or visibility changes. The direct open-square Mates import is redundant
and removed. The delivery tool fetches and rebases on sheaf-dag for the dry run.

## Status

landed 20261014T034912-L-815572 2026-10-14 (merge of deliver/S3/Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap)
