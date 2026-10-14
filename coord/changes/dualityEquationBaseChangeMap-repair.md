# AlgebraicGeometry.dualityEquationBaseChangeMap

## Reason

Repair of landing 20261014T054723-L-2187800 at broken tip
7203881ce5a89cf381f49c8904a21439f3d8871f.

The redundant final `show _ from` elaborates through a local alias. In
`ProperFlatOpenSquareMateIso`, unfolding the definition and extracting the eleven
named lets leaves that additional alias in the goal. The subsequent rewrite by
`secondMate_formula` fails to find the mate expression. The build reports
`IsIso this✝¹` and a transparency-related type-correctness diagnostic.

Remove only `show _ from`, restoring the direct inverse-mate term. This preserves
the morphism definitionally, all signatures, visibility, imports and docstrings.
The consumer and the mathematical construction are unchanged. The inverse of beta
is still uniquely determined by its isomorphism instance. No axiom or hole is added.
The node's proof route remains accurate and is unchanged.

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
  -- The only inverse data used here is the inverse of the fixed base-change
  -- transformation; no fresh pullback adjunction or counit is selected.
  show _ from (mateEquiv adjf adjf' (inv β)).app K
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
  -- The only inverse data used here is the inverse of the fixed base-change
  -- transformation; no fresh pullback adjunction or counit is selected.
  (mateEquiv adjf adjf' (inv β)).app K
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FlatPrecomposePus | not adapted; current claim unchanged | redundant wrapper removed; signatures and meanings unchanged |
| Sheaf.AlgebraicGeometry.HorizontalDualityMateCommutativity | not adapted; current claim unchanged | redundant wrapper removed; signatures and meanings unchanged |
| Sheaf.AlgebraicGeometry.HorizontalDualityMatePasting | not adapted; current claim unchanged | redundant wrapper removed; signatures and meanings unchanged |
| Sheaf.AlgebraicGeometry.HorizontalRectangleInverseMateFixedTransport | not adapted; current claim unchanged | redundant wrapper removed; signatures and meanings unchanged |
| Sheaf.AlgebraicGeometry.NewBaseOpenMateFactorization | not adapted; current claim unchanged | redundant wrapper removed; signatures and meanings unchanged |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | not adapted; current claim unchanged | redundant wrapper removed; signatures and meanings unchanged |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso | not adapted; current claim unchanged | redundant wrapper removed; signatures and meanings unchanged |
| Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso | not adapted; current claim unchanged | consumer source unchanged; restores its expected inverse-mate expression |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | not adapted; current claim unchanged | redundant wrapper removed; signatures and meanings unchanged |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | not adapted; current claim unchanged | redundant wrapper removed; signatures and meanings unchanged |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart | not adapted; current claim unchanged | redundant wrapper removed; signatures and meanings unchanged |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | not adapted; current claim unchanged | redundant wrapper removed; signatures and meanings unchanged |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison | not adapted; current claim unchanged | redundant wrapper removed; signatures and meanings unchanged |
| Sheaf.AlgebraicGeometry.QCohInverseBaseChangeMate | not adapted; current claim unchanged | redundant wrapper removed; signatures and meanings unchanged |
| Sheaf.AlgebraicGeometry.RectangleInverseBaseChangeMateTransport | not adapted; current claim unchanged | redundant wrapper removed; signatures and meanings unchanged |
| Sheaf.AlgebraicGeometry.RightAdjointMateAffineOpenIsIso | not adapted; current claim unchanged | redundant wrapper removed; signatures and meanings unchanged |
| Sheaf.AlgebraicGeometry.RightAdjointMateNewBaseOpen | not adapted; current claim unchanged | redundant wrapper removed; signatures and meanings unchanged |
| Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpen | not adapted; current claim unchanged | redundant wrapper removed; signatures and meanings unchanged |
| Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpenFactorization | not adapted; current claim unchanged | redundant wrapper removed; signatures and meanings unchanged |
| Sheaf.AlgebraicGeometry.RightAdjointMateSchemeIsoTransport | not adapted; current claim unchanged | redundant wrapper removed; signatures and meanings unchanged |
| Sheaf.AlgebraicGeometry.RightAdjointMateSchemeIsoTransportMate | not adapted; current claim unchanged | redundant wrapper removed; signatures and meanings unchanged |
| Sheaf.AlgebraicGeometry.RightAdjointMateSuccessiveBaseChange | not adapted; current claim unchanged | redundant wrapper removed; signatures and meanings unchanged |
| Sheaf.AlgebraicGeometry.SchemeIsoSecondMateNormalizedSquare | not adapted; current claim unchanged | redundant wrapper removed; signatures and meanings unchanged |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | not adapted; current claim unchanged | redundant wrapper removed; signatures and meanings unchanged |

## Status

landed 20261014T063813-L-2812284 2026-10-14 (merge of deliver/XRbb9b20b2b4a981ff/Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap)
