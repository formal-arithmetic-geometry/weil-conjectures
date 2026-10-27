# FiniteCoefficientTotalComparison.Ordinary

## Reason

The source pure-tensor normalization and the generic total-complex lift repeated
an expanded ordinary tensor natural-isomorphism type after finite coefficient
specialization. Destructing the source existence proof and applying the generic
lift repeatedly unfolded the large inverse-image and sheafification constructions.
Share that type as one generic definition, before any site specialization.
The alias is exactly the previous natural-isomorphism type: no datum, hypothesis,
normalization equation or conclusion changes. Definition-meaning review is reopened
for targets using these definitions. No target signature changes.

## Old

The ordinary type was repeated inline; there was no shared `Ordinary` definition.

```lean
def FiniteCoefficientTensorNormalization :
    letI := finiteCoefficientIntrinsicMonoidal X A
    (tensor (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⋙
          finiteCoefficientIntrinsicComparison X A ≅
        (finiteCoefficientIntrinsicComparison X A).prod
          (finiteCoefficientIntrinsicComparison X A) ⋙ tensor _) → Prop :=
  letI := finiteCoefficientIntrinsicMonoidal X A
  fun e ↦ ∀ (M N : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) (U : X.Etale)
      (x : M.obj.obj (op U)) (y : N.obj.obj (op U)),
    (e.app (M, N)).hom.val.app (op (X.toProEt.obj U))
      (finiteCoefficientComparisonSection X A (M ⊗ N) U
        (finiteCoefficientEtalePure X A M N U x y)) =
    finiteCoefficientIntrinsicPure X A
      ((finiteCoefficientIntrinsicComparison X A).obj M)
      ((finiteCoefficientIntrinsicComparison X A).obj N) (op (X.toProEt.obj U))
      (finiteCoefficientComparisonSection X A M U x)
      (finiteCoefficientComparisonSection X A N U y)
```

```lean
def normalizedTensorEquation
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalCategory D]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor D).obj M).PreservesZeroMorphisms]
    (G : C ⥤ D) [G.Additive]
    (e : tensor C ⋙ G ≅ G.prod G ⋙ tensor D)
    (P Q : CochainComplex C ℤ) [HomologicalComplex.HasTensor P Q]
    [HomologicalComplex.HasMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)]
    (a : (G.mapHomologicalComplex (.up ℤ)).obj (HomologicalComplex.tensorObj P Q) ≅
      HomologicalComplex.mapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
        ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)) : Prop :=
      ∀ (p q k : ℤ) (h : p + q = k),
        G.map (HomologicalComplex.ιTensorObj P Q p q k h) ≫ a.hom.f k =
          (e.app (P.X p, Q.X q)).hom ≫
            HomologicalComplex.ιMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
              ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ) p q k h

/-- Total normalization for a specified ordinary tensor normalization.
Source: Stacks 06YN (blueprint: lem-sf-finite-intrinsic-chain-tensor-generators). -/
def Normalization
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalCategory D]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor D).obj M).PreservesZeroMorphisms]
    (G : C ⥤ D) [G.Additive]
    (N : (tensor C ⋙ G ≅ G.prod G ⋙ tensor D) → Prop)
    (P Q : CochainComplex C ℤ) [HomologicalComplex.HasTensor P Q]
    [HomologicalComplex.HasMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)]
    (a : (G.mapHomologicalComplex (.up ℤ)).obj (HomologicalComplex.tensorObj P Q) ≅
      HomologicalComplex.mapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
        ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)) : Prop :=
  ∃ e, N e ∧ normalizedTensorEquation G e P Q a
```

The corresponding private constructor definitions are:

```lean
private def curryTensorComparison
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (G : C ⥤ D) (e : tensor C ⋙ G ≅ G.prod G ⋙ tensor D) :
    (Functor.postcompose₂.obj G).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj G).obj G).obj (curriedTensor D) :=
  { app := fun M ↦
      { app := fun N ↦ e.hom.app (M, N)
        naturality := by
          intro N N' f
          simpa using e.hom.naturality (X := (M, N)) (Y := (M, N')) (𝟙 M, f) }
    naturality := by
      intro M M' f
      apply NatTrans.ext
      funext N
      simpa using e.hom.naturality (X := (M, N)) (Y := (M', N)) (f, 𝟙 N) }
```

```lean
private def liftTensorIso
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D] [HasZeroObject C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalCategory D]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor D).obj M).PreservesZeroMorphisms]
    (G : C ⥤ D) [G.Additive] [PreservesColimitsOfSize.{0, 0} G]
    (e : tensor C ⋙ G ≅ G.prod G ⋙ tensor D)
    (P Q : CochainComplex C ℤ) [HomologicalComplex.HasTensor P Q]
    [HomologicalComplex.HasMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)] :
    (G.mapHomologicalComplex (.up ℤ)).obj (HomologicalComplex.tensorObj P Q) ≅
      HomologicalComplex.mapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
        ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ) := by
  let τ := curryTensorComparison G e
  have (M N : C) : IsIso ((τ.app M).app N) := (e.app (M, N)).isIso_hom
  exact asIso (HomologicalComplex.mapBifunctorComparison τ (.up ℤ) P Q)
```

```lean
private def totalIsoEquation
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalCategory D]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor D).obj M).PreservesZeroMorphisms]
    (G : C ⥤ D) [G.Additive] [PreservesColimitsOfSize.{0, 0} G]
    (e : tensor C ⋙ G ≅ G.prod G ⋙ tensor D)
    (P Q : CochainComplex C ℤ) [HomologicalComplex.HasTensor P Q]
    [HomologicalComplex.HasMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)]
    (a : (G.mapHomologicalComplex (.up ℤ)).obj (HomologicalComplex.tensorObj P Q) ≅
      HomologicalComplex.mapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
        ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)) : Prop :=
      ∀ (p q k : ℤ) (h : p + q = k),
        G.map (HomologicalComplex.ιTensorObj P Q p q k h) ≫ a.hom.f k =
          (e.app (P.X p, Q.X q)).hom ≫
            HomologicalComplex.ιMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
              ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ) p q k h
```

## New

```lean
def Ordinary {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (G : C ⥤ D) : Type _ :=
  tensor C ⋙ G ≅ G.prod G ⋙ tensor D
```

```lean
def FiniteCoefficientTensorNormalization :
    letI := finiteCoefficientIntrinsicMonoidal X A
    FiniteCoefficientTotalComparison.Ordinary
      (finiteCoefficientIntrinsicComparison X A) → Prop :=
  letI := finiteCoefficientIntrinsicMonoidal X A
  fun e ↦ ∀ (M N : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) (U : X.Etale)
      (x : M.obj.obj (op U)) (y : N.obj.obj (op U)),
    (e.app (M, N)).hom.val.app (op (X.toProEt.obj U))
      (finiteCoefficientComparisonSection X A (M ⊗ N) U
        (finiteCoefficientEtalePure X A M N U x y)) =
    finiteCoefficientIntrinsicPure X A
      ((finiteCoefficientIntrinsicComparison X A).obj M)
      ((finiteCoefficientIntrinsicComparison X A).obj N) (op (X.toProEt.obj U))
      (finiteCoefficientComparisonSection X A M U x)
      (finiteCoefficientComparisonSection X A N U y)

omit [Finite A] in
```

```lean
def normalizedTensorEquation
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalCategory D]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor D).obj M).PreservesZeroMorphisms]
    (G : C ⥤ D) [G.Additive]
    (e : FiniteCoefficientTotalComparison.Ordinary G)
    (P Q : CochainComplex C ℤ) [HomologicalComplex.HasTensor P Q]
    [HomologicalComplex.HasMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)]
    (a : FiniteCoefficientTotalComparison.ChainIso G P Q) : Prop :=
      ∀ (p q k : ℤ) (h : p + q = k),
        G.map (HomologicalComplex.ιTensorObj P Q p q k h) ≫ a.hom.f k =
          (e.app (P.X p, Q.X q)).hom ≫
            HomologicalComplex.ιMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
              ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ) p q k h
```

```lean
def Normalization
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalCategory D]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor D).obj M).PreservesZeroMorphisms]
    (G : C ⥤ D) [G.Additive]
    (N : (FiniteCoefficientTotalComparison.Ordinary G) → Prop)
    (P Q : CochainComplex C ℤ) [HomologicalComplex.HasTensor P Q]
    [HomologicalComplex.HasMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)]
    (a : FiniteCoefficientTotalComparison.ChainIso G P Q) : Prop :=
  ∃ e, N e ∧ normalizedTensorEquation G e P Q a
```

The curried comparison, lifted isomorphism, summand equation and uniqueness
helpers use `Ordinary G` for the identical ordinary comparison type. Their proof
bodies are retained. The specialized ordinary uniqueness helper uses the same alias.
The additional `ChainIso` sharing and named unique chain comparison are recorded in
`finite-chain-comparison-sharing.md`. The displayed normalization equations and
both public existence-and-uniqueness conclusions are unchanged.

The corresponding private constructor definitions are:

```lean
private def curryTensorComparison
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (G : C ⥤ D) (e : FiniteCoefficientTotalComparison.Ordinary G) :
    (Functor.postcompose₂.obj G).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj G).obj G).obj (curriedTensor D) :=
  { app := fun M ↦
      { app := fun N ↦ e.hom.app (M, N)
        naturality := by
          intro N N' f
          simpa using e.hom.naturality (X := (M, N)) (Y := (M, N')) (𝟙 M, f) }
    naturality := by
      intro M M' f
      apply NatTrans.ext
      funext N
      simpa using e.hom.naturality (X := (M, N)) (Y := (M', N)) (f, 𝟙 N) }
```

```lean
private def liftTensorIso
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D] [HasZeroObject C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalCategory D]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor D).obj M).PreservesZeroMorphisms]
    (G : C ⥤ D) [G.Additive] [PreservesColimitsOfSize.{0, 0} G]
    (e : FiniteCoefficientTotalComparison.Ordinary G)
    (P Q : CochainComplex C ℤ) [HomologicalComplex.HasTensor P Q]
    [HomologicalComplex.HasMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)] :
    FiniteCoefficientTotalComparison.ChainIso G P Q := by
  let τ := curryTensorComparison G e
  have (M N : C) : IsIso ((τ.app M).app N) := (e.app (M, N)).isIso_hom
  exact asIso (HomologicalComplex.mapBifunctorComparison τ (.up ℤ) P Q)
```

```lean
private def totalIsoEquation
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalCategory D]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor D).obj M).PreservesZeroMorphisms]
    (G : C ⥤ D) [G.Additive] [PreservesColimitsOfSize.{0, 0} G]
    (e : FiniteCoefficientTotalComparison.Ordinary G)
    (P Q : CochainComplex C ℤ) [HomologicalComplex.HasTensor P Q]
    [HomologicalComplex.HasMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)]
    (a : FiniteCoefficientTotalComparison.ChainIso G P Q) : Prop :=
      ∀ (p q k : ℤ) (h : p + q = k),
        G.map (HomologicalComplex.ιTensorObj P Q p q k h) ≫ a.hom.f k =
          (e.app (P.X p, Q.X q)).hom ≫
            HomologicalComplex.ιMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
              ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ) p q k h
```

## Users

The source-import closure and whole-name searches give the following consumers.
Every unchanged consumer retains its statement because the changed types and
constructors unfold to the original ones. Rows also retain adapted and new modules.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Unchanged; the shared type or constructor is definitionally identical where used. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Unchanged; the shared type or constructor is definitionally identical where used. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Unchanged; the shared type or constructor is definitionally identical where used. |
| Sheaf.Paper.FiniteCoefficientIntrinsicChainTensor | unclaimed | Uses the shared ordinary type in its generic helpers and normalization. |
| Sheaf.Paper.FiniteCoefficientIntrinsicTensor | unclaimed | Defines the shared type and uses it in the identical pure-tensor normalization. |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | unclaimed | Unchanged source consumer, checked with the revised definitions. |
| Sheaf.Paper.FiniteCoefficientSiteTensorNaturality | new, Y7 | Specializes the generic lifting proof through the same shared type. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Unchanged; the shared type or constructor is definitionally identical where used. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Unchanged; the shared type or constructor is definitionally identical where used. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | Unchanged; the shared type or constructor is definitionally identical where used. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Unchanged; the shared type or constructor is definitionally identical where used. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed | Unchanged; the shared type or constructor is definitionally identical where used. |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed | Unchanged; the shared type or constructor is definitionally identical where used. |
| WeilConjectures | unclaimed | Aggregate import names contain the textual token Normalization; this is not a use of the changed normalization predicate. The aggregate source and its public imports remain unchanged. |

## Status

landed 20261022T114256-L-598666 2026-10-22 (merge of deliver/Y7/Sheaf.Paper.FiniteCoefficientSiteHomArrow)
