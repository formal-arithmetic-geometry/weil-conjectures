# Augmented self-Ext/self-Tor resolution split

## Reason

The returned local theorem was false for arbitrary T,J. For the identity on Spec k,
an infinite-dimensional degree-zero T cannot have a finite-free zero model. A closed
immersion alone also imposes no K-injectivity condition on J. The repair retains
actual augmented resolutions in the core and uses precisely those hypotheses locally.
These are new, unlanded split statements, not changes to a library target.

## Old

```lean
theorem exists_selfExt_tor_resolution_core
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (n : ℕ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    let Q := (Scheme.Modules.tensorPullback i).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (-(n : ℤ))).obj
          (S.obj B ⊗ S.obj B))
    ∃ (T J : CochainComplex Z.Modules ℤ)
      (hJ : ∀ k : ℤ, k ≠ 0 → IsZero (J.homology k))
      (e0 : J.homology 0 ≅ SheafOfModules.unit Z.ringCatSheaf)
      (eG : (Scheme.Modules.tensorPullback i).obj G ≅
        (homComplex (R := Z.sheaf) T J).homology (n : ℤ))
      (eQ : Q ≅ T.homology (-(n : ℤ))), True

theorem selfExt_tor_resolution_local
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] (T J : CochainComplex Z.Modules ℤ) :
    ∀ (V : Z.Opens) (U : Y.affineOpens)
      (_hU : ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f),
      let W := V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1)
      let Fc := moduleOpenOverComplexFunctor Z V W
      CochainComplex.IsKInjective (Fc.obj J) ∧
        HasFiniteFreeZeroModel (V.toScheme.ringCatSheaf.over W) (Fc.obj T)
```

## New

```lean
theorem exists_selfExt_tor_resolution_core
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (n : ℕ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    let Q := (Scheme.Modules.tensorPullback i).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (-(n : ℤ))).obj
          (S.obj B ⊗ S.obj B))
    ∃ (_add : (Scheme.Modules.tensorPullback i).Additive)
      (P : CochainComplex Y.Modules ℤ) (J : CochainComplex Z.Modules ℤ)
      (a : P ⟶ (HomologicalComplex.single Y.Modules (.up ℤ) 0).obj B)
      (b : (HomologicalComplex.single Z.Modules (.up ℤ) 0).obj
        (SheafOfModules.unit Z.ringCatSheaf) ⟶ J),
      CochainComplex.IsKFlatResolution (R := Y.sheaf) a ∧
      (∀ k : ℤ, SheafOfModules.IsFlat (P.X k)) ∧
      QuasiIso b ∧ J.IsKInjective ∧
      let T := ((Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj P
      ∃ (hJ : ∀ k : ℤ, k ≠ 0 → IsZero (J.homology k))
      (e0 : J.homology 0 ≅ SheafOfModules.unit Z.ringCatSheaf)
      (eG : (Scheme.Modules.tensorPullback i).obj G ≅
        (homComplex (R := Z.sheaf) T J).homology (n : ℤ))
      (eQ : Q ≅ T.homology (-(n : ℤ))), True

theorem selfExt_tor_resolution_local
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [(Scheme.Modules.tensorPullback i).Additive]
    (P : CochainComplex Y.Modules ℤ) (J : CochainComplex Z.Modules ℤ)
    (a : P ⟶ (HomologicalComplex.single Y.Modules (.up ℤ) 0).obj
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))
    (b : (HomologicalComplex.single Z.Modules (.up ℤ) 0).obj
      (SheafOfModules.unit Z.ringCatSheaf) ⟶ J)
    (_hP : CochainComplex.IsKFlatResolution (R := Y.sheaf) a)
    (_hflat : ∀ k : ℤ, SheafOfModules.IsFlat (P.X k))
    (_hb : QuasiIso b) (_hJ : J.IsKInjective) :
    let T := ((Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj P
    ∀ (V : Z.Opens) (U : Y.affineOpens)
      (_hU : ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f),
      let W := V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1)
      let Fc := moduleOpenOverComplexFunctor Z V W
      CochainComplex.IsKInjective (Fc.obj J) ∧
        HasFiniteFreeZeroModel (V.toScheme.ringCatSheaf.over W) (Fc.obj T)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SelfExtTorResolutionModel | B2 | proof now passes the actual resolution maps and properties; signature and visibility unchanged |

The split modules do not exist in the repository baseline. Their only user is this
item; no other held module is adapted. No target definition changes.

## Status

landed 20261013T190134-L-3213959 2026-10-13 (merge of deliver/B2/Sheaf.AlgebraicGeometry.SelfExtTorResolutionModel)
