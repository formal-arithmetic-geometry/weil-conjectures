# AlgebraicGeometry.schemeOrdinaryHomComparison

## Reason

The accepted packet at `689fc8ee20` was returned after landing detected a concurrent
change to `ExactSourceEvaluationLocalComparisons`. The repair reads that consumer's
current server quarantine archive, confirms it matches the shared archive, and
reapplies the compatibility import while retaining the current header, public
imports, and source/blueprint module documentation. The delivery is rebuilt on the
freshly fetched `sheaf-dag` base.

The upstream sync quarantined the local localization module with the universe constraint
`?u + 1 = u` in `homComplex`, and quarantined its eight evaluation consumers.
The adopted upstream tree already contains complete proofs of all their declarations.
The upstream localization definition is the same fixed K-injective augmentation construction,
with explicit `homComplex.{u, u, u, u}` universe arguments. Re-exporting that construction
repairs the root and avoids maintaining duplicate public declarations.

All nine modules retain their public declaration names and proposition types through compatibility imports. Previous explicit
public imports are retained in the eight consumer wrappers, including the old K-flat API.
The root's previous public dependencies are still re-exported by its upstream twin.
The upstream K-flat predicate `IsKFlatTensor` is definitionally equal to the previous
`IsAcyclicTensorKFlat` in these signatures. Temporary Lean examples check every former public
signature against the corresponding upstream constant, retaining the former predicate and
binder names and fixing only the ambiguous Hom-complex universes.

All nine delivered modules compile individually in the sandbox set. The eleven re-exported
public constants use only `propext`, `Classical.choice`, and `Quot.sound`. No new proof hole
or construction is introduced. No upstream file or target is edited. The actual definition
used by target statements remains the displayed augmentation construction; no mathematical
meaning changes. The ten DAG Lean attachments now identify the actual upstream declarations.

## Old

The old root definition was the following (from the quarantined module):

```lean
def schemeOrdinaryHomComparison (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (P M : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    DerivedCategory.Q.obj (homComplex (R := Y.sheaf) P M) ⟶
      (derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf).obj
        (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj M) := by
  haveI := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  exact DerivedCategory.Q.map (((homComplexFunctor (R := Y.sheaf)).obj (op P)).map
    ((CochainComplex.toKInjectiveResolution.{u}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))).app M)) ≫
    (schemeDerivedInternalHomResolutionIso Y P M).inv
```

The old public signatures of all nine modules are recorded verbatim below. Private helpers
were fully proved; they are replaced by the corresponding upstream proof implementations.

`Sheaf.AlgebraicGeometry.ExactSourceEvaluationLocalComparisons`:

```lean
theorem exists_exactSource_evaluation_local_comparisons (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory X) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (_hhom : ∀ (M M' : CochainComplex (localEvaluationModules X U) ℤ) (t : M ⟶ M'),
      QuasiIso t → QuasiIso (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map t))
    (_hdual : (localEvaluationDual X U P).IsAcyclicTensorKFlat)
    (_eK : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj P)
    (_eN : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj N ≅ DerivedCategory.Q.obj F)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (_hf : IsLocalOrdinaryEvaluation X U P F f) :
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory X))
    let g := ((schemeDerivedTensorHomEquiv X) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv X) D K (𝟙_ (schemeDerivedCategory X)) (𝟙 D)) ≫
          (ρ_ N).hom)
    ∃ a : R.obj (N ⊗ D) ≅ DerivedCategory.Q.obj (localEvaluationTensor X U P F),
      ∃ b : R.obj (H.obj (op K, N)) ≅
          DerivedCategory.Q.obj (homComplex (R := X.sheaf.over U) P F),
        R.map g ≫ b.hom = a.hom ≫ DerivedCategory.Q.map f

```

`Sheaf.AlgebraicGeometry.ExactSourceEvaluationOpenModels`:

```lean
theorem exists_exactSource_evaluation_open_models (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory U.toScheme)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (_hhom : ∀ (M M' : CochainComplex (localEvaluationModules X U) ℤ) (t : M ⟶ M'),
      QuasiIso t → QuasiIso (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map t))
    (_hdual : (localEvaluationDual X U P).IsAcyclicTensorKFlat)
    (_eK : (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj
      (DerivedCategory.Q.obj P) ≅ K)
    (_eN : (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj
      (DerivedCategory.Q.obj F) ≅ N)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (_hf : IsLocalOrdinaryEvaluation X U P F f) :
    let E := (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let H := derivedInternalHom
      (Opens.grothendieckTopology U.toScheme.toRingedSpace) U.toScheme.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory U.toScheme))
    let g := ((schemeDerivedTensorHomEquiv U.toScheme) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv U.toScheme) D K
          (𝟙_ (schemeDerivedCategory U.toScheme)) (𝟙 D)) ≫ (ρ_ N).hom)
    ∃ a : N ⊗ D ≅ E.obj (DerivedCategory.Q.obj (localEvaluationTensor X U P F)),
      ∃ b : H.obj (op K, N) ≅
          E.obj (DerivedCategory.Q.obj (homComplex (R := X.sheaf.over U) P F)),
        g ≫ b.hom = a.hom ≫ E.map (DerivedCategory.Q.map f)

```

`Sheaf.AlgebraicGeometry.ExactSourceKInjectiveEvaluationOpenModels`:

```lean
theorem exists_exactSource_kInjective_evaluation_open_models (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory U.toScheme)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (_hhom : ∀ (M M' : CochainComplex (localEvaluationModules X U) ℤ) (t : M ⟶ M'),
      QuasiIso t → QuasiIso (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map t))
    (_hdual : (localEvaluationDual X U P).IsAcyclicTensorKFlat)
    (_eK : (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj
      (DerivedCategory.Q.obj P) ≅ K)
    (_eN : (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj
      (DerivedCategory.Q.obj F) ≅ N)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (_hf : IsLocalOrdinaryEvaluation X U P F f) [F.IsKInjective] :
    let E := (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let H := derivedInternalHom
      (Opens.grothendieckTopology U.toScheme.toRingedSpace) U.toScheme.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory U.toScheme))
    let g := ((schemeDerivedTensorHomEquiv U.toScheme) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv U.toScheme) D K
          (𝟙_ (schemeDerivedCategory U.toScheme)) (𝟙 D)) ≫ (ρ_ N).hom)
    ∃ a : N ⊗ D ≅ E.obj (DerivedCategory.Q.obj (localEvaluationTensor X U P F)),
      ∃ b : H.obj (op K, N) ≅
          E.obj (DerivedCategory.Q.obj (homComplex (R := X.sheaf.over U) P F)),
        g ≫ b.hom = a.hom ≫ E.map (DerivedCategory.Q.map f)

```

`Sheaf.AlgebraicGeometry.KInjectiveSchemeEvaluationModels`:

```lean
theorem exists_kInjective_scheme_evaluation_models (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (K N : schemeDerivedCategory Y)
    (P F : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hhom : ∀ (M M' : CochainComplex
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) (t : M ⟶ M'),
      QuasiIso t → QuasiIso (((homComplexFunctor (R := Y.sheaf)).obj (op P)).map t))
    (hdual : (homComplex (R := Y.sheaf) P
      ((HomologicalComplex.single _ (.up ℤ) 0).obj
        (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace))))).IsAcyclicTensorKFlat)
    (eK : DerivedCategory.Q.obj P ≅ K) (eN : DerivedCategory.Q.obj F ≅ N)
    (f : pullbackTensorTotal Y F
        (homComplex (R := Y.sheaf) P
          ((HomologicalComplex.single _ (.up ℤ) 0).obj
            (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace))))) ⟶
      homComplex (R := Y.sheaf) P F)
    (hf : IsSchemeOrdinaryEvaluation Y P F f) [F.IsKInjective] :
    let H := derivedInternalHom (Opens.grothendieckTopology Y.toRingedSpace) Y.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory Y))
    let g := ((schemeDerivedTensorHomEquiv Y) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv Y) D K
          (𝟙_ (schemeDerivedCategory Y)) (𝟙 D)) ≫ (ρ_ N).hom)
    ∃ a : N ⊗ D ≅ DerivedCategory.Q.obj (pullbackTensorTotal Y F
          (homComplex (R := Y.sheaf) P
            ((HomologicalComplex.single _ (.up ℤ) 0).obj
              (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))))),
      ∃ b : H.obj (op K, N) ≅ DerivedCategory.Q.obj (homComplex (R := Y.sheaf) P F),
        g ≫ b.hom = a.hom ≫ DerivedCategory.Q.map f

```

`Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationLocalization`:

```lean
def schemeOrdinaryHomComparison (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (P M : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    DerivedCategory.Q.obj (homComplex (R := Y.sheaf) P M) ⟶
      (derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf).obj
        (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj M)

theorem schemeDerivedTensorHomEquiv_naturality (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (K K' L L' M M' : schemeDerivedCategory Y)
    (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M')
    (g : K ⟶ (derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf).obj
      (op L, M)) :
    schemeDerivedTensorHomEquiv Y K' L' M'
        (a ≫ g ≫ (derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf).map
          (b.op, c)) =
      (a ⊗ₘ b) ≫ schemeDerivedTensorHomEquiv Y K L M g ≫ c

theorem schemeOrdinaryEvaluation_localization (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (K N : schemeDerivedCategory Y)
    (P F : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (eK : DerivedCategory.Q.obj P ≅ K) (eN : DerivedCategory.Q.obj F ≅ N)
    (f : pullbackTensorTotal Y F
        (homComplex (R := Y.sheaf) P
          ((HomologicalComplex.single _ (.up ℤ) 0).obj
            (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace))))) ⟶
      homComplex (R := Y.sheaf) P F)
    (hf : IsSchemeOrdinaryEvaluation Y P F f) :
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf
    let O := (HomologicalComplex.single _ (.up ℤ) 0).obj
      (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    let V := homComplex (R := Y.sheaf) P O
    let c := schemeOrdinaryHomComparison Y P F ≫ H.map (eK.inv.op, eN.hom)
    let d := schemeOrdinaryHomComparison Y P O ≫
      H.map (eK.inv.op, ((DerivedCategory.quotientCompQhIso _).app O).inv)
    schemeDerivedTensorHomEquiv Y (N ⊗ DerivedCategory.Q.obj V) K N
        ((eN.inv ▷ DerivedCategory.Q.obj V) ≫ pullbackTensorModelMap Y F V ≫
          DerivedCategory.Q.map f ≫ c) =
      (α_ N (DerivedCategory.Q.obj V) K).hom ≫ N ◁
        (schemeDerivedTensorHomEquiv Y (DerivedCategory.Q.obj V) K
          (𝟙_ (schemeDerivedCategory Y)) d) ≫ (ρ_ N).hom

```

`Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationComparisons`:

```lean
theorem exists_strictlyPerfect_evaluation_comparisons (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (F : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (_hstrict : Scheme.IsStrictlyPerfect X U P)
    (_eK : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj P)
    (_eN : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj N ≅ DerivedCategory.Q.obj F)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (_hf : IsLocalOrdinaryEvaluation X U P F f) :
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory X))
    let g := ((schemeDerivedTensorHomEquiv X) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv X) D K (𝟙_ (schemeDerivedCategory X)) (𝟙 D)) ≫
          (ρ_ N).hom)
    ∃ a : R.obj (N ⊗ D) ≅ DerivedCategory.Q.obj (localEvaluationTensor X U P F),
      ∃ b : R.obj (H.obj (op K, N)) ≅
          DerivedCategory.Q.obj (homComplex (R := X.sheaf.over U) P F),
        R.map g ≫ b.hom = a.hom ≫ DerivedCategory.Q.map f

```

`Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationLocalRetraction`:

```lean
theorem exists_strictlyPerfect_evaluation_local_retraction (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (_hstrict : Scheme.IsStrictlyPerfect X U P)
    (_eK : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj P) :
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory X))
    let g := ((schemeDerivedTensorHomEquiv X) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv X) D K (𝟙_ (schemeDerivedCategory X)) (𝟙 D)) ≫
          (ρ_ N).hom)
    ∃ r : R.obj (H.obj (op K, N)) ⟶ R.obj (N ⊗ D),
      R.map g ≫ r = 𝟙 (R.obj (N ⊗ D))

```

`Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationLocalSection`:

```lean
theorem exists_strictlyPerfect_evaluation_local_section (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (_hstrict : Scheme.IsStrictlyPerfect X U P)
    (_eK : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj P) :
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory X))
    let g := ((schemeDerivedTensorHomEquiv X) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv X) D K (𝟙_ (schemeDerivedCategory X)) (𝟙 D)) ≫
          (ρ_ N).hom)
    ∃ s : R.obj (H.obj (op K, N)) ⟶ R.obj (N ⊗ D),
      s ≫ R.map g = 𝟙 (R.obj (H.obj (op K, N)))

```

`Sheaf.AlgebraicGeometry.StrictlyPerfectKInjectiveEvaluationComparisons`:

```lean
theorem exists_strictlyPerfect_kInjective_evaluation_comparisons (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (F : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    [F.IsKInjective]
    (_hstrict : Scheme.IsStrictlyPerfect X U P)
    (_eK : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj P)
    (_eN : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj N ≅ DerivedCategory.Q.obj F)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (_hf : IsLocalOrdinaryEvaluation X U P F f) :
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory X))
    let g := ((schemeDerivedTensorHomEquiv X) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv X) D K (𝟙_ (schemeDerivedCategory X)) (𝟙 D)) ≫
          (ρ_ N).hom)
    ∃ a : R.obj (N ⊗ D) ≅ DerivedCategory.Q.obj (localEvaluationTensor X U P F),
      ∃ b : R.obj (H.obj (op K, N)) ≅
          DerivedCategory.Q.obj (homComplex (R := X.sheaf.over U) P F),
        R.map g ≫ b.hom = a.hom ≫ DerivedCategory.Q.map f

```

## New

Each module re-exports its proved upstream twin under the same compatibility module path.
The old public declaration names therefore continue to resolve to the upstream declarations.
The old K-flat public dependency remains explicitly imported where it was previously public.
Some upstream theorem binders drop their leading underscore (`_hhom` to `hhom`,
`_hdual` to `hdual`, `_hstrict` to `hstrict`, `_eK` to `eK`, and `_hf` to `hf`, depending
on the theorem). These names do not change the proposition types. No live caller or
remaining quarantined caller outside this restored set imports one of these modules;
all restored module bodies are compatibility imports, so there is no named-argument
call to adapt. The DAG attachments quote the upstream binder names.

The adopted root definition, verbatim, is:

```lean
def schemeOrdinaryHomComparison (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (P M : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    DerivedCategory.Q.obj (homComplex.{u, u, u, u} (R := Y.sheaf) P M) ⟶
      (derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf).obj
        (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj M) := by
  haveI := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  exact DerivedCategory.Q.map (((homComplexFunctor (R := Y.sheaf)).obj (op P)).map
    ((CochainComplex.toKInjectiveResolution.{u}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))).app M)) ≫
    (schemeDerivedInternalHomResolutionIso Y P M).inv
```

The exact new module contents are:

`Sheaf.AlgebraicGeometry.ExactSourceEvaluationLocalComparisons`:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.ExactSourceEvaluationLocalComparisons

/-! # The local representative equation for evaluation with an exact Hom source

Source: Stacks Project, Tags 08DL, 08DM and 08DQ, the ordinary complex models;
Tag 08DJ, the tensor-Hom representative equation.
(blueprint: lem-pc-exact-source-evaluation-local-comparisons).

The declarations are supplied by the proved upstream evaluation implementation.
The public dependencies of the current quarantined module remain available.
-/

@[expose] public section
```

`Sheaf.AlgebraicGeometry.ExactSourceEvaluationOpenModels`:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.ExactSourceEvaluationOpenModels

/-!
Compatibility import for the proved upstream evaluation implementation.
The existing public dependencies remain available to users of this module.
-/

@[expose] public section
```

`Sheaf.AlgebraicGeometry.ExactSourceKInjectiveEvaluationOpenModels`:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ExactSourceKInjectiveEvaluationOpenModels

/-!
Compatibility import for the proved upstream evaluation implementation.
The existing public dependencies remain available to users of this module.
-/

@[expose] public section
```

`Sheaf.AlgebraicGeometry.KInjectiveSchemeEvaluationModels`:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.KInjectiveSchemeEvaluationModels

/-!
Compatibility import for the proved upstream evaluation implementation.
The existing public dependencies remain available to users of this module.
-/

@[expose] public section
```

`Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationLocalization`:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationLocalization

/-! # Localization of the ordinary evaluation equation

Compatibility import for the proved upstream implementation. Its fixed Hom-complex
universes repair the ambiguous universe inference of the former local copy.
Source: Stacks Project, Tags 08DJ, 08DM and 08DQ.
(blueprint: lem-pc-scheme-ordinary-evaluation-localization).
-/

@[expose] public section
```

`Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationComparisons`:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictlyPerfectOrdinaryEvaluation
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
public import WeilConjectures.AlgebraicGeometry.StrictlyPerfectEvaluationComparisons

/-!
Compatibility import for the proved upstream evaluation implementation.
The existing public dependencies remain available to users of this module.
-/

@[expose] public section
```

`Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationLocalRetraction`:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
public import WeilConjectures.AlgebraicGeometry.StrictlyPerfectEvaluationLocalRetraction

/-!
Compatibility import for the proved upstream evaluation implementation.
The existing public dependencies remain available to users of this module.
-/

@[expose] public section
```

`Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationLocalSection`:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
public import WeilConjectures.AlgebraicGeometry.StrictlyPerfectEvaluationLocalSection

/-!
Compatibility import for the proved upstream evaluation implementation.
The existing public dependencies remain available to users of this module.
-/

@[expose] public section
```

`Sheaf.AlgebraicGeometry.StrictlyPerfectKInjectiveEvaluationComparisons`:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictlyPerfectOrdinaryEvaluation
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
public import WeilConjectures.AlgebraicGeometry.StrictlyPerfectKInjectiveEvaluationComparisons

/-!
Compatibility import for the proved upstream evaluation implementation.
The existing public dependencies remain available to users of this module.
-/

@[expose] public section
```

## Users

`tools/downstream.py` with `--allow-missing --uses` reports zero live downstream users,
since the cluster is quarantined. A source import scan of both library roots and quarantine
finds exactly the eight consumer modules below; all are restored in this delivery.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ExactSourceEvaluationLocalComparisons | unclaimed | Restore the cluster consumer as a compatibility import; preserve its old public dependencies. |
| Sheaf.AlgebraicGeometry.ExactSourceEvaluationOpenModels | unclaimed | Restore the cluster consumer as a compatibility import; preserve its old public dependencies. |
| Sheaf.AlgebraicGeometry.ExactSourceKInjectiveEvaluationOpenModels | unclaimed | Restore the cluster consumer as a compatibility import; preserve its old public dependencies. |
| Sheaf.AlgebraicGeometry.KInjectiveSchemeEvaluationModels | unclaimed | Restore the cluster consumer as a compatibility import; preserve its old public dependencies. |
| Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationLocalization | C7 | Restore the repaired root as an upstream compatibility import. |
| Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationComparisons | unclaimed | Restore the cluster consumer as a compatibility import; preserve its old public dependencies. |
| Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationLocalRetraction | unclaimed | Restore the cluster consumer as a compatibility import; preserve its old public dependencies. |
| Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationLocalSection | unclaimed | Restore the cluster consumer as a compatibility import; preserve its old public dependencies. |
| Sheaf.AlgebraicGeometry.StrictlyPerfectKInjectiveEvaluationComparisons | unclaimed | Restore the cluster consumer as a compatibility import; preserve its old public dependencies. |

The original consumer proof files also need explicit Hom-complex universes: for example,
`KInjectiveSchemeEvaluationModels.lean:152` fails with `?u.350 + 1 = u` when restored verbatim.
Annotating those universes allows the first consumers to compile; the next full duplicate
proof exceeds the per-file limit. The final packet reuses the existing upstream proofs
instead. The delivered compatibility imports compile in 2.5–12.6 seconds each, and public
signature probes verify that the imported implementation has definitionally equal proposition types.

## Status

landed 20261020T154042-L-3034341 2026-10-20 (merge of deliver/C7/Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationLocalization)
