# horizontal_ordinary_inverse_fixed_pasting

## Reason

Kernel checking repeatedly unfolds the duplicate horizontal and QCoh functors and the
large inline fixed transfer construction; complete direct proofs exceed the file limit.
Encapsulate exactly the existing upper comparison, base comparison and transfer data as
explicit definitions. The upper and base comparisons display qcPullback and qcDirectImage, which are
definitionally equal to their horizontal names. No hypothesis or conclusion changes, and
no Challenge target is edited. The natural-language DAG statement remains unchanged.

## Old

```lean
theorem horizontal_ordinary_inverse_fixed_pasting
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Y' Z : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (g : Y' ⟶ Y) (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition E.obj))
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (h : Z ⟶ Y')
    (hβh : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f (h ≫ g)) (h ≫ g)
        (pullback.fst f (h ≫ g)) pullback.condition E.obj))
    (hβ₂ : ∀ E : schemeDerivedQCohCategory (pullback f g),
      IsIso (schemeDerivedBaseChangeMap (pullback.snd f g)
        (pullback.snd (pullback.snd f g) h) h
        (pullback.fst (pullback.snd f g) h) pullback.condition E.obj)) :
    letI : QuasiSeparatedSpace (pullback f (h ≫ g) : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))
    letI : QuasiSeparatedSpace (pullback (pullback.snd f g) h : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h)
    let s := horizontalMateComp (pullback.fst (pullback.snd f g) h) (pullback.fst f g) ≪≫
      eqToIso (congrArg horizontalMatePullback
        (pullbackLeftPullbackSndIso_hom_fst f g h).symm) ≪≫
      (horizontalMateComp (pullbackLeftPullbackSndIso f g h).hom
        (pullback.fst f (h ≫ g))).symm
    let e := pullbackLeftPullbackSndIso f g h
    let ev := horizontalMateEquivalence e
    let q := pullback.snd f (h ≫ g)
    let p := pullback.snd (pullback.snd f g) h
    let ri := (horizontalMateAdjunction e.hom).rightAdjointUniq ev.toAdjunction
    let li := eqToIso (congrArg qcDirectImage
        (pullbackLeftPullbackSndIso_hom_snd f g h).symm) ≪≫
      horizontalMatePushComp e.hom q ≪≫
      Functor.isoWhiskerRight ri (horizontalMatePushforward q)
    let k : TwoSquare (horizontalMatePullback e.hom)
        (horizontalMatePushforward q) (horizontalMatePushforward p)
        (𝟭 (schemeDerivedQCohCategory Z)) :=
      .mk _ _ _ _ <|
        (Functor.isoWhiskerLeft (horizontalMatePullback e.hom) li).hom ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight ev.unitIso.inv (horizontalMatePushforward q) ≫
          (Functor.leftUnitor (horizontalMatePushforward q)).hom ≫
          (Functor.rightUnitor (horizontalMatePushforward q)).inv
    let τ := qcInverseBaseChange f (h ≫ g) hβh
    let σ := qcInverseBaseChange f g hβ ≫ₕ
      @qcInverseBaseChange _ (pullback f g) Y' Z _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
        (pullback.snd f g) _ _ h hβ₂
    ∀ E : schemeDerivedQCohCategory X,
      (horizontalMatePushforward (pullback.snd (pullback.snd f g) h)).map
          (s.hom.app E) ≫ (τ ≫ₕ k).app E =
        σ.app E ≫ (horizontalMateComp h g).hom.app
          ((horizontalMatePushforward f).obj E)
```

## New

```lean
theorem horizontal_ordinary_inverse_fixed_pasting
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Y' Z : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (g : Y' ⟶ Y) (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition E.obj))
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (h : Z ⟶ Y')
    (hβh : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f (h ≫ g)) (h ≫ g)
        (pullback.fst f (h ≫ g)) pullback.condition E.obj))
    (hβ₂ : ∀ E : schemeDerivedQCohCategory (pullback f g),
      IsIso (schemeDerivedBaseChangeMap (pullback.snd f g)
        (pullback.snd (pullback.snd f g) h) h
        (pullback.fst (pullback.snd f g) h) pullback.condition E.obj)) :
    letI : QuasiSeparatedSpace (pullback f (h ≫ g) : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))
    letI : QuasiSeparatedSpace (pullback (pullback.snd f g) h : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h)
    let s := horizontalOrdinaryUpperComparison f g h
    let e := pullbackLeftPullbackSndIso f g h
    let q := pullback.snd f (h ≫ g)
    let p := pullback.snd (pullback.snd f g) h
    let k := horizontalOrdinaryTransfer e q p (pullbackLeftPullbackSndIso_hom_snd f g h)
    let τ := qcInverseBaseChange f (h ≫ g) hβh
    let σ := qcInverseBaseChange f g hβ ≫ₕ
      @qcInverseBaseChange _ (pullback f g) Y' Z _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
        (pullback.snd f g) _ _ h hβ₂
    ∀ E : schemeDerivedQCohCategory X,
      (qcDirectImage (pullback.snd (pullback.snd f g) h)).map
          (s.hom.app E) ≫ (τ ≫ₕ k).app E =
        σ.app E ≫ (horizontalOrdinaryBaseComparison g h).hom.app
          ((qcDirectImage f).obj E)
```

The three new definitions contain the original construction factors verbatim, with the
QCoh restriction names in the upper and base signatures; transfer keeps the horizontal names. They contain no sorry. No definition used by
a Challenge target is assigned different data, so this is an interface refactor rather
than a change in mathematical meaning.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.HorizontalOrdinaryInverseFixedPasting | D2 | Same statement; fixed construction bodies now have names. |
| Sheaf.AlgebraicGeometry.HorizontalInverseSquareFixedPasting | unclaimed | Forced proof adaptation: the old simp list cannot unfold the new construction names, so its final rfl fails at line 218. Existing signatures and visibility remain unchanged. |

The adapted caller adds three private, proved construction equations and uses them in
its existing normalization step. These generic equations avoid expensive delta reduction
at the concrete iterated pullback. The original compiler error is recorded
in report.md; the delivery tool repeats the counterfactual check.

## Status

landed 20261013T215558-L-895607 2026-10-13 (merge of deliver/D2/Sheaf.AlgebraicGeometry.HorizontalOrdinaryInverseFixedPasting)
