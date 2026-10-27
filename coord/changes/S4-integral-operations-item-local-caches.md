# Item-local sharing for integral tensor transitions

## Declaration

`Sheaf.Paper.IntegralOperationsWellDefined`; thirteen existing declarations below:
ten private theorem headers, the private restrictComplexMap header, and the bodies of
integralOperationsTensorLevel and the private integralOperationsProjection.
The public theorems integralOperationsPullbackTransition_existsUnique and
integralOperationsTensorTransition_existsUnique and the private liftMap_apply keep
their original statements byte for byte (reviewer correction, below).
All 111 original declarations remain, including private goodComplexes_isLocalization.
Seven new public transparent helper definitions are attached to the existing node.
Every existing operation return type stays verbatim. No other module changes.

## Reason

The completed coefficient ring and sheaf tensor structures make repeated section
coercions expensive to elaborate and check. The helpers record the same forgetful
functors, section evaluation, termwise scalar restriction and signed-total tensor
composite once. The first five helpers are reducible; the restriction and tensor
composite helpers are ordinary transparent definitions. All changed propositions,
functor data and the private scalar-restriction header are definitionally equal to
the originals. No hypotheses, objects, scalar actions, generator formulas, universes
or conclusions change. TensorLevel remains an ordinary definition, with its original
return type, whose body factors the original composite through transparent helpers.
The private projection uses the same forgetful sheaf functor through its alias.

The tensor transition is the adjunction mate of the normalized finite scalar-extension
tensor comparison. Homogeneous-generator calculations prove its naturality and
uniqueness. A private chain-adjunction definition shares the same unchanged adjunction.
The eight new private proof definitions use no_expose to keep their implementation
bodies private; no existing declaration receives that attribute.
This repair takes the reviewer's item-local option and drops every returned edit to
CompletedIntegralCoefficients and IntegralReductionTowerUnrestricted. It also drops
the returned extra operation type annotations and implicit_reducible attribute.

## Reviewer correction (cc review of 14229d41)

The delivered statements of the two public transition theorems and of the private
liftMap_apply (wrapped in integralOperationsNaturalSectionApply and
integralOperationsSectionApply) are definitionally equal to the originals but not
syntactically: `rw` in unchanged consumers no longer finds the original pattern.
Compiled against the delivered module, NormalizedIntegralPullbackTower:355
(`rw [liftMap_apply]`), CompletedTensorFiniteShift:380 and
IntegralTensorLeftShiftUnique:522 (`rw [...] at` the `choose_spec` of the tensor
transition theorem) failed; all three pass against the published module. The
reviewer restored the three original statements verbatim; the proofs are unchanged.
The aliases remain in use inside the item's private proofs only.

## Old

```lean
private noncomputable def restrictComplexMap
    {P : CochainComplex (SheafOfModules.{r} S) ℤ}
    {Q : CochainComplex (SheafOfModules.{r} T) ℤ}
    (φ : P ⟶ ((restrictScalars q).mapHomologicalComplex (.up ℤ)).obj Q) :
    ((restrictScalars f).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((restrictScalars g).mapHomologicalComplex (.up ℤ)).obj Q where
  -- Unchanged component and differential-compatibility fields.
```

```lean
private theorem restrictComplexMap_apply
    {P : CochainComplex (SheafOfModules.{r} S) ℤ}
    {Q : CochainComplex (SheafOfModules.{r} T) ℤ}
    (φ : P ⟶ ((restrictScalars q).mapHomologicalComplex (.up ℤ)).obj Q)
    (j : ℤ) (U : Cᵒᵖ) (x : (P.X j).val.obj U) :
    ((restrictComplexMap f g q hq φ).f j).val.app U x = (φ.f j).val.app U x
```

```lean
private theorem pushRestrictionIso_apply (N : SheafOfModules.{r} R₁)
    (U : Cᵒᵖ) (x : N.val.obj (F.op.obj U)) :
    ((pushRestrictionIso F qR qS φ₀ φ₁ h).inv.app N).val.app U x = x
```

```lean
private theorem mate_generator {M : SheafOfModules.{r} S₀} {N : SheafOfModules.{r} S₁}
    (a : M ⟶ (restrictScalars qS).obj N) (U : Cᵒᵖ) (x : M.val.obj U) :
    (IntegralMateProof.mate adj₀ adj₁ (restrictScalars qS) (restrictScalars qR)
      (pushRestrictionIso F qR qS φ₀ φ₁ h) a).val.app (F.op.obj U)
        ((adj₀.unit.app M).val.app U x) =
      (adj₁.unit.app N).val.app U (a.val.app U x)
```

```lean
private theorem mateData_unit_formula
    {M : SheafOfModules.{r} S₀} {N : SheafOfModules.{r} S₁}
    (a : M ⟶ (restrictScalars qS).obj N) (U : Cᵒᵖ) (x : M.val.obj U) :
    (mateData F qR qS φ₀ φ₁ h adj₀ adj₁ a).val.app (F.op.obj U)
        (unitSection F φ₀ adj₀ M U x) =
      unitSection F φ₁ adj₁ N U (a.val.app U x)
```

```lean
private theorem restricted_hom_ext
    {R : Sheaf K RingCat.{r}} (π₀ : R ⟶ R₀) (π₁ : R ⟶ R₁)
    (hπ : π₀ ≫ qR = π₁) [Presheaf.IsLocallySurjective K π₀.hom]
    (M : SheafOfModules.{r} S₀) (N : SheafOfModules.{r} R₁)
    (a b : (restrictScalars π₀).obj (L₀.obj M) ⟶ (restrictScalars π₁).obj N)
    (hab : ∀ (U : Cᵒᵖ) (x : M.val.obj U),
      a.val.app (F.op.obj U) (unitSection F φ₀ adj₀ M U x) =
        b.val.app (F.op.obj U) (unitSection F φ₀ adj₀ M U x)) : a = b
```

```lean
private noncomputable def integralOperationsProjection (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    completedIntegralCoefficientSheafUnrestricted l E W ⟶ integralCoefficientSheaf l E W n :=
  (sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (completedIntegralCommRingProjectionUnrestricted l E W n)
```

```lean
private theorem completedProjection_locallySurjective (W : AlgebraicGeometry.Scheme.{t})
    (n : ℕ) : Presheaf.IsLocallySurjective (AlgebraicGeometry.Scheme.ProEt.topology W)
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (completedIntegralCommRingProjectionUnrestricted l E W n)).hom
```

```lean
private theorem integralProjection_step (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    (sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (completedIntegralCommRingProjectionUnrestricted l E W (n + 1)) ≫
          integralCoefficientSheafTransition l E W n =
    (sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (completedIntegralCommRingProjectionUnrestricted l E W n)
```

```lean
private theorem integralPullback_restricted_hom_ext
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    (M : integralOperationsFiniteModules l E Y (n + 1))
    (N : integralOperationsFiniteModules l E X n)
    (a b : (integralCompletedRestrict l E X (n + 1)).obj
        ((integralOperationsLevelPullback l E f (n + 1)).obj M) ⟶
      (integralCompletedRestrict l E X n).obj N)
    (h : ∀ (V : Y.ProEt) (x : M.val.obj (op V)),
      a.val.app ((integralOperationsBaseChange f).op.obj (op V))
          (integralOperationsPullbackGenerator l E f (n + 1) M V x) =
        b.val.app ((integralOperationsBaseChange f).op.obj (op V))
          (integralOperationsPullbackGenerator l E f (n + 1) M V x)) : a = b
```

```lean
noncomputable def integralOperationsTensorLevel (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    (CochainComplex (integralTowerModules l E W) ℤ) ×
      (CochainComplex (integralTowerModules l E W) ℤ) ⥤
        CochainComplex (integralTowerModules l E W) ℤ :=
  (unrestrictedIntegralFiniteComplex l E W n).prod
      (unrestrictedIntegralFiniteComplex l E W n) ⋙
    Functor.uncurry.obj
      ((MonoidalCategory.curriedTensor
        (integralOperationsFiniteModules l E W n)).map₂CochainComplex) ⋙
        integralOperationsRestrict l E W n
```

```lean
private theorem tensor_quasiIso
    {C : Type x} [Category.{y} C] [EssentiallySmall.{z} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{z}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [J.HasSheafCompose (forget₂ CommRingCat.{z} RingCat.{z})] {R : Sheaf J CommRingCat.{z}}
    {E E' K K' : CochainComplex (SheafOfModules.{z}
      ((sheafCompose J (forget₂ CommRingCat.{z} RingCat.{z})).obj R)) ℤ}
    (α : E ⟶ E') (β : K ⟶ K') (hα : QuasiIso α) (hβ : QuasiIso β)
    (hK : CochainComplex.IsKFlatIndependentCoefficients (R := R) K)
    (hE' : CochainComplex.IsKFlatIndependentCoefficients (R := R) E') :
    let
```

```lean
private theorem goodComplexes_isLocalization
    {C : Type a} [Category.{b} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    (P : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ))
    (hp : ∀ K, P K ↔ CochainComplex.IsKFlatIndependentCoefficients (R := R) K ∧
      ∀ i : ℤ, SheafOfModules.IsFlatOnSite (R := R) (K.X i)) :
    (P.ι ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage P.ι)
```

## New

```lean
private noncomputable def restrictComplexMap
    {P : CochainComplex (SheafOfModules.{r} S) ℤ}
    {Q : CochainComplex (SheafOfModules.{r} T) ℤ}
    (φ : P ⟶ (WeilConjectures.integralOperationsRestrictionComplex q).obj Q) :
    (WeilConjectures.integralOperationsRestrictionComplex f).obj P ⟶
      (WeilConjectures.integralOperationsRestrictionComplex g).obj Q where
  -- Unchanged component and differential-compatibility fields.
```

```lean
private theorem restrictComplexMap_apply
    {P : CochainComplex (SheafOfModules.{r} S) ℤ}
    {Q : CochainComplex (SheafOfModules.{r} T) ℤ}
    (φ : P ⟶ (WeilConjectures.integralOperationsRestrictionComplex q).obj Q)
    (j : ℤ) (U : Cᵒᵖ) (x : (P.X j).val.obj U) :
    (integralOperationsComplexSectionApply (restrictComplexMap f g q hq φ) j U) x =
      (integralOperationsComplexSectionApply φ j U) x
```

```lean
private theorem pushRestrictionIso_apply (N : SheafOfModules.{r} R₁)
    (U : Cᵒᵖ) (x : N.val.obj (F.op.obj U)) :
    (integralOperationsSectionApply ((pushRestrictionIso F qR qS φ₀ φ₁ h).inv.app N) U) x = x
```

```lean
private theorem mate_generator {M : SheafOfModules.{r} S₀} {N : SheafOfModules.{r} S₁}
    (a : M ⟶ (restrictScalars qS).obj N) (U : Cᵒᵖ) (x : M.val.obj U) :
    (integralOperationsSectionApply (IntegralMateProof.mate adj₀ adj₁ (restrictScalars qS)
      (restrictScalars qR)
      (pushRestrictionIso F qR qS φ₀ φ₁ h) a) (F.op.obj U))
        ((integralOperationsSectionApply (adj₀.unit.app M) U) x) =
      (integralOperationsSectionApply (adj₁.unit.app N) U) ((integralOperationsSectionApply a U)
        x)
```

```lean
private theorem mateData_unit_formula
    {M : SheafOfModules.{r} S₀} {N : SheafOfModules.{r} S₁}
    (a : M ⟶ (restrictScalars qS).obj N) (U : Cᵒᵖ) (x : M.val.obj U) :
    (integralOperationsSectionApply (mateData F qR qS φ₀ φ₁ h adj₀ adj₁ a) (F.op.obj U))
        (unitSection F φ₀ adj₀ M U x) =
      unitSection F φ₁ adj₁ N U ((integralOperationsSectionApply a U) x)
```

```lean
private theorem restricted_hom_ext
    {R : Sheaf K RingCat.{r}} (π₀ : R ⟶ R₀) (π₁ : R ⟶ R₁)
    (hπ : π₀ ≫ qR = π₁) [Presheaf.IsLocallySurjective K π₀.hom]
    (M : SheafOfModules.{r} S₀) (N : SheafOfModules.{r} R₁)
    (a b : (restrictScalars π₀).obj (L₀.obj M) ⟶ (restrictScalars π₁).obj N)
    (hab : ∀ (U : Cᵒᵖ) (x : M.val.obj U),
      (integralOperationsSectionApply a (F.op.obj U)) (unitSection F φ₀ adj₀ M U x) =
        (integralOperationsSectionApply b (F.op.obj U)) (unitSection F φ₀ adj₀ M U x)) : a = b
```

```lean
private noncomputable def integralOperationsProjection (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    completedIntegralCoefficientSheafUnrestricted l E W ⟶ integralCoefficientSheaf l E W n :=
  (integralOperationsForgetSheaf.{max u (t + 1)} (AlgebraicGeometry.Scheme.ProEt.topology W)).map
      (completedIntegralCommRingProjectionUnrestricted l E W n)
```

```lean
private theorem completedProjection_locallySurjective (W : AlgebraicGeometry.Scheme.{t})
    (n : ℕ) : Presheaf.IsLocallySurjective (AlgebraicGeometry.Scheme.ProEt.topology W)
      ((integralOperationsForgetSheaf.{max u (t + 1)} (AlgebraicGeometry.Scheme.ProEt.topology
        W)).map
        (completedIntegralCommRingProjectionUnrestricted l E W n)).hom
```

```lean
private theorem integralProjection_step (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    (integralOperationsForgetSheaf.{max u (t + 1)} (AlgebraicGeometry.Scheme.ProEt.topology W)).map
        (completedIntegralCommRingProjectionUnrestricted l E W (n + 1)) ≫
          integralCoefficientSheafTransition l E W n =
    (integralOperationsForgetSheaf.{max u (t + 1)} (AlgebraicGeometry.Scheme.ProEt.topology W)).map
        (completedIntegralCommRingProjectionUnrestricted l E W n)
```

```lean
private theorem integralPullback_restricted_hom_ext
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    (M : integralOperationsFiniteModules l E Y (n + 1))
    (N : integralOperationsFiniteModules l E X n)
    (a b : (integralCompletedRestrict l E X (n + 1)).obj
        ((integralOperationsLevelPullback l E f (n + 1)).obj M) ⟶
      (integralCompletedRestrict l E X n).obj N)
    (h : ∀ (V : Y.ProEt) (x : M.val.obj (op V)),
      (integralOperationsSectionApply a ((integralOperationsBaseChange f).op.obj (op V)))
          (integralOperationsPullbackGenerator l E f (n + 1) M V x) =
        (integralOperationsSectionApply b ((integralOperationsBaseChange f).op.obj (op V)))
          (integralOperationsPullbackGenerator l E f (n + 1) M V x)) : a = b
```

```lean
noncomputable def integralOperationsTensorLevel (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    (CochainComplex (integralTowerModules l E W) ℤ) ×
      (CochainComplex (integralTowerModules l E W) ℤ) ⥤
        CochainComplex (integralTowerModules l E W) ℤ :=
  integralOperationsTensorComposite (unrestrictedIntegralFiniteComplex l E W n)
    (SheafOfModules.restrictScalars ((integralOperationsForgetSheaf.{max u (t + 1)}
      (AlgebraicGeometry.Scheme.ProEt.topology W)).map
        (completedIntegralCommRingProjectionUnrestricted l E W n)))
```

```lean
private theorem tensor_quasiIso
    {C : Type x} [Category.{y} C] [EssentiallySmall.{z} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{z}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [J.HasSheafCompose WeilConjectures.integralOperationsRingForget.{z}]
    {R : Sheaf J CommRingCat.{z}}
    {E E' K K' : CochainComplex (SheafOfModules.{z}
      ((integralOperationsForgetSheaf.{z} J).obj R)) ℤ}
    (α : E ⟶ E') (β : K ⟶ K') (hα : QuasiIso α) (hβ : QuasiIso β)
    (hK : CochainComplex.IsKFlatIndependentCoefficients (R := R) K)
    (hE' : CochainComplex.IsKFlatIndependentCoefficients (R := R) E') :
    let
```

```lean
private theorem goodComplexes_isLocalization
    {C : Type a} [Category.{b} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [J.HasSheafCompose WeilConjectures.integralOperationsRingForget.{u}]
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory (SheafOfModules.{u}
      ((integralOperationsForgetSheaf.{u} J).obj R))]
    (P : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((integralOperationsForgetSheaf.{u} J).obj R)) ℤ))
    (hp : ∀ K, P K ↔ CochainComplex.IsKFlatIndependentCoefficients (R := R) K ∧
      ∀ i : ℤ, SheafOfModules.IsFlatOnSite (R := R) (K.X i)) :
    (P.ι ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage P.ι)
```

The seven new public transparent helper definitions are:

```lean
@[reducible] def WeilConjectures.integralOperationsRingForget : CommRingCat.{r} ⥤ RingCat.{r} :=
  forget₂ CommRingCat RingCat
```

```lean
@[reducible] noncomputable def WeilConjectures.integralOperationsForgetSheaf
    {C : Type uForget} [Category.{vForget} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose WeilConjectures.integralOperationsRingForget.{wForget}] :
    Sheaf J CommRingCat.{wForget} ⥤ Sheaf J RingCat.{wForget} :=
  sheafCompose J WeilConjectures.integralOperationsRingForget
```

```lean
@[reducible] def WeilConjectures.integralOperationsSectionApply
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}} {M N : SheafOfModules.{r} R}
    (φ : M ⟶ N) (U : Cᵒᵖ) : M.val.obj U → N.val.obj U :=
  fun x ↦ φ.val.app U x
```

```lean
@[reducible] def WeilConjectures.integralOperationsComplexSectionApply
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}}
    {K L : CochainComplex (SheafOfModules.{r} R) ℤ}
    (φ : K ⟶ L) (n : ℤ) (U : Cᵒᵖ) : (K.X n).val.obj U → (L.X n).val.obj U :=
  fun x ↦ (φ.f n).val.app U x
```

```lean
@[reducible] def WeilConjectures.integralOperationsNaturalSectionApply
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}} {D : Type c} [Category.{d} D]
    {F G : D ⥤ CochainComplex (SheafOfModules.{r} R) ℤ}
    (φ : F ⟶ G) (P : D) (n : ℤ) (U : Cᵒᵖ) :
    ((F.obj P).X n).val.obj U → ((G.obj P).X n).val.obj U :=
  fun x ↦ ((φ.app P).f n).val.app U x
```

```lean
noncomputable def WeilConjectures.integralOperationsRestrictionComplex
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (f : R ⟶ S) :
    CochainComplex (SheafOfModules.{r} S) ℤ ⥤
      CochainComplex (SheafOfModules.{r} R) ℤ :=
  (SheafOfModules.restrictScalars f).mapHomologicalComplex (.up ℤ)
```

```lean
noncomputable def integralOperationsTensorComposite
    {D : Type a} [Category.{b} D] {A : Type c} [Category.{d} A]
    [Preadditive A] [MonoidalCategory A]
    [(MonoidalCategory.curriedTensor A).PreservesZeroMorphisms]
    [∀ X : A, ((MonoidalCategory.curriedTensor A).obj X).PreservesZeroMorphisms]
    [∀ P Q : CochainComplex A ℤ, HomologicalComplex.HasMapBifunctor P Q
      (MonoidalCategory.curriedTensor A) (.up ℤ)]
    {B : Type a'} [Category.{b'} B] [HasZeroMorphisms B]
    (F : D ⥤ CochainComplex A ℤ) (R : A ⥤ B) [R.PreservesZeroMorphisms] :
    D × D ⥤ CochainComplex B ℤ :=
  F.prod F ⋙ Functor.uncurry.obj
    (MonoidalCategory.curriedTensor A).map₂CochainComplex ⋙
      R.mapHomologicalComplex (.up ℤ)
```

## Users

The table includes the textual users found by `tools/downstream.py` and every
consumer named in the return. Module and attached-node claims were checked in
`coord/claims`. No consumer is adapted or included in the delivery. Compatibility
compile results, including upstream quarantine and timing limitations, are recorded
in report.md; this table does not claim that every consumer has passed a fresh build.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.AlgebraicGeometry.ProperOpenSquareDerivedSupport | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.CoefficientTwistsDetailed | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.CompletedIntegralFiniteFree | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.CompletedIntegralPrincipalUnitCriterion | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.CompletedIntegralQuotientModelComparison | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.CompletedScalarChainShift | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.CompletedScalarShiftCoordinates | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.ConnectedAdicIntegralBasis | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.ConstantScalarUnitQuasiIsomorphism | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.FiniteComparisonPresentation | E3 | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.FiniteFreeCoefficientTransport | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.FiniteFreeCompletedScalarComparison | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.FiniteFreeSystemRestriction | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.FiniteFreeSystemRestrictionData | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.FinitePullbackTransitionGenerators | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.IntegralDerivedOperationsOnSlices | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.IntegralObjectFiniteBasis | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.IntegralObjectPullbackQuotientBasis | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.IntegralOperationsScalarComparisons | M4 | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.IntegralOperationsWellDefined | S4 | Tensor-transition proof and transparent caches |
| Sheaf.Paper.IntegralScalarExtensionWellDefined | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.IntegralStrictReductionModel | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.IntegralTensorReductionTowerComparison | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.IntegralTensorTransitionCompatibility | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.IsomorphismComparisonNatural | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.NormalizedIntegralTensorTower | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.NormalizedPullbackCompositionTransport | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.OrdinaryIntegralPullbackConstruction | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.PodCompletionScalarFormulas | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.PodQuotientAdjunctionRealization | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.PodSameIndexUnitDescent | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.PodScalarMultiplicationRealization | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.PointQuotientAugmentationDiagram | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.PointTransportConeComparisonDescent | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.PurTwistSheafLocallyFree | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.ScalarExtensionComposition | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.Paper.StrictQuotientExpressions | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.SixFunctors.CompletedTensorFiniteShift | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.SixFunctors.CompletedTensorShiftRight | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.SixFunctors.ConstructibleTensorCompletion | unclaimed | Source unchanged; operations and equations are definitionally equal |
| Sheaf.SixFunctors.QuotientCompletionActualReflector | unclaimed | Source unchanged; operations and equations are definitionally equal |

## Status

landed 20261027T021406-L-2764545 2026-10-27 (merge of deliver/S4/Sheaf.Paper.IntegralOperationsWellDefined)
