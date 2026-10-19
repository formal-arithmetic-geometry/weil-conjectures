# DerivedSupportDirectImageComparison normalization and elaboration

## Reason

The original concrete expressions repeatedly expanded the chosen ModuleCat kernels,
Grothendieck-abelian derived-category instances, and canonical derived adjunctions
while elaborating the compatibility proof. Whole-file compilation exceeded 60 seconds.
Keep the specified functors, maps, and equations, but give the inferred functors explicit
types, name the generic composition-normalization equation, and factor the specified
open pullback comparisons through abstract coefficient-category constructions.

No Challenge declaration changes. The structure fields below expand to exactly
the previous equations, with the same binders and K-injectivity hypotheses. No new
hypothesis is imposed on the item or on any previous public declaration. The generic
coefficient helper's left-adjoint instances are already supplied at its specialization.
The comparison identities have the same identity components; only their presentation
changes from NatIso.ofComponents to Iso.refl. The derived adjunction keeps its original
canonical construction, changing its reducibility from abbrev to def.

## Old

```lean
noncomputable abbrev supportEt {C T : Scheme.{u}} (i : C ⟶ T)
    [IsClosedImmersion i] :=
  Sheaf.supportedSectionsFunctor (T.smallEtaleTopology) (ModuleCat.{u + 1} A)
    (Etale.supportRestrictionArrow i)
```

```lean
noncomputable abbrev supportEvalEt (T : Scheme.{u}) :=
  sheafToPresheaf (T.smallEtaleTopology) (ModuleCat.{u + 1} A) ⋙
    (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 T)))
```

```lean
noncomputable abbrev supportPro {C T : Scheme.{u}} (i : C ⟶ T)
    [IsClosedImmersion i] :=
  Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)
    (supportRestrictionArrow i)
```

```lean
noncomputable abbrev supportEvalPro (T : Scheme.{u}) :=
  sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
    (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 T)))
```

```lean
noncomputable abbrev supportNu (T : Scheme.{u}) :=
  comparisonLowerStar (ModuleCat.{u + 1} A) T
```

```lean
noncomputable abbrev supportDerivedAdjunction (T : Scheme.{u}) :=
  (comparisonAdjunction (ModuleCat.{u + 1} A) T).mapDerivedCategoryRightDerivedAdjunction
```

```lean
noncomputable def supportKernelIdentity {C T : Scheme.{u}} (i : C ⟶ T)
    [IsClosedImmersion i] : supportNu A T ⋙ supportEt A i ≅ supportPro A i :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
```

```lean
noncomputable def supportEvaluationIdentity (T : Scheme.{u}) :
    supportNu A T ⋙ supportEvalEt A T ≅ supportEvalPro A T :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
```

```lean
noncomputable def supportOpenPullback {T : Scheme.{u}} (V : T.Opens) :
    supportRestrictEt A V ⋙ comparisonUpperStar (ModuleCat.{u + 1} A) V ≅
      comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙ supportRestrictPro A V :=
  Functor.isoWhiskerRight
      (Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) V.ι).symm _ ≪≫
    supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) V.ι ≪≫
      Functor.isoWhiskerLeft _
        (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) V.ι)
```

```lean
noncomputable def supportDerivedOpenPullback {T : Scheme.{u}} (V : T.Opens) :=
  (Functor.mapDerivedCategoryCompIso (supportRestrictEt A V)
    (comparisonUpperStar (ModuleCat.{u + 1} A) V)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (supportOpenPullback A V) ≪≫
      Functor.mapDerivedCategoryCompIso
        (comparisonUpperStar (ModuleCat.{u + 1} A) T) (supportRestrictPro A V)
```

The affected structure fields:

```lean
  kernel_normalization : ∀ {C T : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i]
      (J : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ)
      [J.IsKInjective],
    supportResolutionUnit (supportEt A i)
        (((supportNu A T).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) ≫
      (supportEt A i).rightDerivedFunctor.map (supportResolutionUnit (supportNu A T) J) ≫
      (b i).hom.app (DerivedCategory.Q.obj J) =
    DerivedCategory.Q.map
        (((supportKernelIdentity A i).hom.mapHomologicalComplex (ComplexShape.up ℤ)).app J) ≫
      supportResolutionUnit (supportPro A i) J
  /-- Identity on the indicated K-injective section complex. -/
  final_normalization : ∀ (T : Scheme.{u})
      (J : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ)
      [J.IsKInjective],
    supportResolutionUnit (supportEvalEt A T)
        (((supportNu A T).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) ≫
      (supportEvalEt A T).rightDerivedFunctor.map (supportResolutionUnit (supportNu A T) J) ≫
      (g T).hom.app (DerivedCategory.Q.obj J) =
    DerivedCategory.Q.map
        (((supportEvaluationIdentity A T).hom.mapHomologicalComplex (ComplexShape.up ℤ)).app J) ≫
      supportResolutionUnit (supportEvalPro A T) J
```

## New

```lean
noncomputable abbrev supportEt {C T : Scheme.{u}} (i : C ⟶ T)
    [IsClosedImmersion i] :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
  Sheaf.supportedSectionsFunctor (T.smallEtaleTopology) (ModuleCat.{u + 1} A)
    (Etale.supportRestrictionArrow i)
```

```lean
noncomputable abbrev supportEvalEt (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
  sheafToPresheaf (T.smallEtaleTopology) (ModuleCat.{u + 1} A) ⋙
    (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 T)))
```

```lean
noncomputable abbrev supportPro {C T : Scheme.{u}} (i : C ⟶ T)
    [IsClosedImmersion i] :
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
  Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)
    (supportRestrictionArrow i)
```

```lean
noncomputable abbrev supportEvalPro (T : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
  sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
    (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 T)))
```

```lean
noncomputable abbrev supportNu (T : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⥤
      Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  comparisonLowerStar (ModuleCat.{u + 1} A) T
```

```lean
noncomputable def supportDerivedAdjunction (T : Scheme.{u}) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⊣
      (supportNu A T).rightDerivedFunctor :=
  (comparisonAdjunction (ModuleCat.{u + 1} A) T).mapDerivedCategoryRightDerivedAdjunction
```

```lean
noncomputable def supportKernelIdentity {C T : Scheme.{u}} (i : C ⟶ T)
    [IsClosedImmersion i] : supportNu A T ⋙ supportEt A i ≅ supportPro A i :=
  Iso.refl _
```

```lean
noncomputable def supportEvaluationIdentity (T : Scheme.{u}) :
    supportNu A T ⋙ supportEvalEt A T ≅ supportEvalPro A T :=
  Iso.refl _
```

```lean
noncomputable def supportOpenPullback {T : Scheme.{u}} (V : T.Opens) :
    supportRestrictEt A V ⋙ comparisonUpperStar (ModuleCat.{u + 1} A) V ≅
      comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙ supportRestrictPro A V :=
  supportCoefficientOpenPullback (ModuleCat.{u + 1} A) V
```

```lean
noncomputable def supportDerivedOpenPullback {T : Scheme.{u}} (V : T.Opens) :
    (supportRestrictEt A V).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⋙
        (supportRestrictPro A V).mapDerivedCategory :=
  supportDerivedCoefficientOpenPullback (ModuleCat.{u + 1} A) V
```

```lean
def supportCompositionNormalization
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    (e : F ⋙ G ≅ H)
    (b : F.rightDerivedFunctor ⋙ G.rightDerivedFunctor ≅ H.rightDerivedFunctor)
    (I : CochainComplex C ℤ) : Prop :=
  supportResolutionUnit G ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
    G.rightDerivedFunctor.map (supportResolutionUnit F I) ≫
      b.hom.app (DerivedCategory.Q.obj I) =
  DerivedCategory.Q.map ((e.hom.mapHomologicalComplex (.up ℤ)).app I) ≫
    supportResolutionUnit H I
```

```lean
noncomputable def supportCoefficientOpenPullback
    (D : Type vD) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    {T : Scheme.{u}} (V : T.Opens) :
    Etale.openImmersionRestriction D V.ι ⋙ comparisonUpperStar D V ≅
      comparisonUpperStar D T ⋙ openImmersionRestriction D V.ι :=
  Functor.isoWhiskerRight (Etale.upperStarIsoOpenImmersionRestriction D V.ι).symm _ ≪≫
    supportSiteComparisonCoefficientPullbackIso D V.ι ≪≫
      Functor.isoWhiskerLeft _ (upperStarIsoOpenImmersionRestriction D V.ι)
```

```lean
noncomputable def supportDerivedCoefficientOpenPullback
    (D : Type vD) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    {T : Scheme.{u}} (V : T.Opens)
    [(Etale.openImmersionRestriction D V.ι).IsLeftAdjoint]
    [(openImmersionRestriction D V.ι).IsLeftAdjoint] :
    (Etale.openImmersionRestriction D V.ι).mapDerivedCategory ⋙
        (comparisonUpperStar D V).mapDerivedCategory ≅
      (comparisonUpperStar D T).mapDerivedCategory ⋙
        (openImmersionRestriction D V.ι).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (Etale.openImmersionRestriction D V.ι)
    (comparisonUpperStar D V)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (supportCoefficientOpenPullback D V) ≪≫
      Functor.mapDerivedCategoryCompIso (comparisonUpperStar D T)
        (openImmersionRestriction D V.ι)
```

The affected structure fields:

```lean
  kernel_normalization : ∀ {C T : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i]
      (J : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ)
      [J.IsKInjective],
    supportCompositionNormalization (supportNu A T) (supportEt A i) (supportPro A i)
      (supportKernelIdentity A i) (b i) J
  /-- Identity on the indicated K-injective section complex. -/
  final_normalization : ∀ (T : Scheme.{u})
      (J : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ)
      [J.IsKInjective],
    supportCompositionNormalization (supportNu A T) (supportEvalEt A T) (supportEvalPro A T)
      (supportEvaluationIdentity A T) (g T) J
```

The open-square equation is also named generically, without changing its maps
or binders. Its old and new field declarations are:

Old:

```lean
  open_square : ∀ {C T : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i] (V : T.Opens),
    (b i).hom ≫ derivedOpenPro i V =
      Functor.whiskerLeft (supportNu A T).rightDerivedFunctor (derivedOpenEt i V) ≫
        Functor.whiskerRight (rho V).hom
          (supportEt A (pullback.snd i V.ι)).rightDerivedFunctor ≫
        Functor.whiskerLeft (supportRestrictPro A V).mapDerivedCategory
          (b (pullback.snd i V.ι)).hom
```

New:

```lean
  open_square : ∀ {C T : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i] (V : T.Opens),
    supportRestrictionSquare (supportNu A T).rightDerivedFunctor
      (supportRestrictEt A V).mapDerivedCategory (supportRestrictPro A V).mapDerivedCategory
      (supportNu A V).rightDerivedFunctor (supportEt A i).rightDerivedFunctor
      (supportPro A i).rightDerivedFunctor
      (supportEt A (pullback.snd i V.ι)).rightDerivedFunctor
      (supportPro A (pullback.snd i V.ι)).rightDerivedFunctor
      (b i).hom (rho V).hom (b (pullback.snd i V.ι)).hom
      (derivedOpenEt i V) (derivedOpenPro i V)
```

The new equation definition:

```lean
def supportRestrictionSquare
    {C D B E U : Type*}
    [Category C] [Category D] [Category B] [Category E] [Category U]
    (F : C ⥤ D) (R : D ⥤ E) (S : C ⥤ B) (H : B ⥤ E)
    (K : D ⥤ U) (P : C ⥤ U) (K' : E ⥤ U) (P' : B ⥤ U)
    (b : F ⋙ K ⟶ P) (r : F ⋙ R ⟶ S ⋙ H) (b' : H ⋙ K' ⟶ P')
    (et : K ⟶ R ⋙ K') (pro : P ⟶ S ⋙ P') : Prop :=
  b ≫ pro = Functor.whiskerLeft F et ≫ Functor.whiskerRight r K' ≫
    Functor.whiskerLeft S b'
```

## Users

`tools/downstream.py` was run for every modified public declaration and for the
structure and its three affected projections. There are 205 transitive importers.
The two direct importers below mention the module name only, and the similarly named
`SupportedBottomEdge.kernel_normalization` is a different structure projection.
No downstream proof or statement refers to any changed definition or projection.
The explicit type annotations are definitionally identical to the original inferred
types. The public normalization predicate abbreviates the original equation; it
neither weakens nor strengthens it. Thus all downstream mathematical statements,
including the targets, retain their meaning. Direct consumers are checked unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedSupportDirectImageComparison | C5 | Same statement; canonical constructions and complete proof; equivalent normalization fields. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | S2 | Imports the module for its future proof; no source adaptation. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | K4 | Publicly imports the module; its own kernel_normalization field is unrelated; no adaptation. |

## Status

landed 20261019T231050-L-544822 2026-10-19 (merge of deliver/C5/Sheaf.AlgebraicGeometry.DerivedSupportDirectImageComparison)
