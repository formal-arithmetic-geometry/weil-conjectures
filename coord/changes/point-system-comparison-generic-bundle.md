# WeilConjectures.PointSystemNormalizedComparison.Data

## Reason

The concrete dependent structure repeatedly elaborates the completed coefficient site and
localization functors in its constructor and projections. The completed proof exceeds the
single-file compile limit with that representation. Parameterize the same sixteen fields by
three abelian categories and four functors, then specialize with an abbreviation. Name the
three concrete coefficient predicates and the generic normalization predicate, retaining their
formulas verbatim. No hypothesis or conclusion is dropped.

The realization formula is factored through `systemModel`, with the same two factors in the
same order. `ambientAbelian` is reducible so its inherited category instances agree with the
ones used before specialization. All other existing public imports and signatures remain.
There are no source-library changes and no target statement edits. Targets depending on these
definitions should receive the normal definition review.

## Old

```lean
structure Data (r : ℕ) where
  /-- Natural identification U G_r = F_r on the entire strict tower complexes. -/
  coefficient : (G D l E r).mapHomologicalComplex (.up ℤ) ⋙ X D l E ≅
    X D l E ⋙ ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      (F D l E r)).mapHomologicalComplex (.up ℤ)
  /-- The identification keeps every section, hence all original quotient transitions. -/
  coefficient_sections :
    ∀ (M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ)
      (i : ℤ) (n : ℕ) (V : (Spec (.of D.k)).ProEt)
      (x : ((((G D l E r).mapHomologicalComplex (.up ℤ) ⋙ X D l E).obj M).X i).obj
        (op n) |>.val.obj (op V)),
      HEq (((((coefficient.hom.app M).f i).app (op n)).val.app (op V)) x) x
  /-- Completed coefficient transport is determined by every finite projection. -/
  coefficient_projection : ∀ n : ℕ,
    inverseImageCompletedCoefficientMap l E (PointSystemTransport.pointPower D r).hom ≫
        limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op n) =
      (isoSectionwiseInverseImage (PointSystemTransport.pointPower D r).hom
        RingCat.{max u (t + 1)}).map
          (limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op n)) ≫
        inverseImageFiniteCoefficientMap l E (PointSystemTransport.pointPower D r).hom n
  /-- Finite levels are read through the recorded tensor-unit insertion, without flatness. -/
  finite_tensor_unit : ∀ (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ),
    IsIso (inverseImageFiniteComparisonComplex l E
      (PointSystemTransport.pointPower D r).hom n K)
  /-- One natural normalized model on ALL completed-module towers. -/
  theta : DerivedCategory.Q ⋙ LA D l E ≅ roosF ⋙ DerivedCategory.Q
  /-- Its K-injective normalization fixes the zero shifted-coordinate inclusion. -/
  theta_normalized : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A D l E) ℤ) [I.IsKInjective]
    (_hI : ∀ p : ℤ, Injective (I.X p)),
    ∃ iota : ((lim : (ℕᵒᵖ ⥤ A D l E) ⥤ A D l E).mapHomologicalComplex (.up ℤ)).obj I ⟶
      roosF.obj I,
      QuasiIso iota ∧
      (∀ p : ℤ, iota.f (p + 1) ≫ (roosχ I p).hom =
        biprod.lift 0 ((Pi.lift (fun n : ℕ ↦
          (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I)).f (p + 1))) ∧
      (lim : (ℕᵒᵖ ⥤ A D l E) ⥤ A D l E).rightDerivedFunctorUnitQ I ≫
        theta.hom.app I = DerivedCategory.Q.map iota
  /-- One natural normalized model on ALL constant integral scalar towers. -/
  eta : DerivedCategory.Q ⋙ LR.{t, u} l E ≅ roosF ⋙ DerivedCategory.Q
  /-- The scalar model has the same strict augmentation normalization. -/
  eta_normalized : ∀ (I : CochainComplex
    (ℕᵒᵖ ⥤ ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t, u} l E none)) ℤ)
    [I.IsKInjective] (_hI : ∀ p : ℤ, Injective (I.X p)),
    ∃ iota : ((lim :
      (ℕᵒᵖ ⥤ ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t, u} l E none)) ⥤
        ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t, u} l E none)).mapHomologicalComplex
          (.up ℤ)).obj I ⟶ roosF.obj I,
      QuasiIso iota ∧
      (∀ p : ℤ, iota.f (p + 1) ≫ (roosχ I p).hom =
        biprod.lift 0 ((Pi.lift (fun n : ℕ ↦
          (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I)).f (p + 1))) ∧
      (lim : (ℕᵒᵖ ⥤ ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t, u} l E none)) ⥤
        ModuleCat.{max u (t + 1)}
          (pointRestrictionScalars.{t, u} l E none)).rightDerivedFunctorUnitQ I ≫
            eta.hom.app I = DerivedCategory.Q.map iota
  /-- The inverse-image comparison, including whole-limit resolutions and augmentations. -/
  inverseImage : Comparison (C := A D l E) (B := A D l E)
    (abelianC := ambientAbelian D l E) (abelianB := ambientAbelian D l E)
    (F D l E r) theta theta
  /-- The sections comparison uses the SAME completed-module normalization. -/
  sections : Comparison (C := A D l E) (abelianC := ambientAbelian D l E)
    (B := ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t, u} l E none))
    (T D l E) theta eta
  /-- The natural inverse-image comparison on the entire ordinary derived system category. -/
  a : L D l E ⋙ (F D l E r).mapDerivedCategory ≅
    (G D l E r).mapDerivedCategory ⋙ L D l E
  /-- The natural sections comparison, with the required inverse orientation. -/
  zeta : PointSystemTransport.derivedSections D l E ⋙ LR.{t, u} l E ≅
    L D l E ⋙ (T D l E).mapDerivedCategory
  /-- a_r = theta_Y inverse kappa_F F(theta_X), including the strict coefficient identity. -/
  a_model : ∀ M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ,
    a.hom.app (DerivedCategory.Q.obj M) ≫
        (L D l E).map ((G D l E r).mapDerivedCategoryFactors.hom.app M) ≫
        (systemRealization D l E theta
          (((G D l E r).mapHomologicalComplex (.up ℤ)).obj M)).hom =
      (F D l E r).mapDerivedCategory.map ((systemRealization D l E theta M).hom) ≫
        (F D l E r).mapDerivedCategoryFactors.hom.app (roosF.obj ((X D l E).obj M)) ≫
        DerivedCategory.Q.map (inverseImage.kappa.hom.app ((X D l E).obj M)) ≫
        DerivedCategory.Q.map (roosF.map (coefficient.inv.app M))
  /-- zeta = T(theta_X inverse) kappa_T inverse eta, in the identical fixed models. -/
  zeta_model : ∀ M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ,
    zeta.hom.app (DerivedCategory.Q.obj M) ≫
        (T D l E).mapDerivedCategory.map ((systemRealization D l E theta M).hom) ≫
        (T D l E).mapDerivedCategoryFactors.hom.app (roosF.obj ((X D l E).obj M)) ≫
        DerivedCategory.Q.map (sections.kappa.hom.app ((X D l E).obj M)) =
      (LR.{t, u} l E).map
          ((PointSystemTransport.sections D l E).mapDerivedCategoryFactors.hom.app M) ≫
        eta.hom.app ((PointSystemTransport.complexSections D l E).obj M)
  /-- The signed coordinate chart has precisely d(x,y)=(dx,(1-s)x-dy). -/
  signed_differential : ∀ (V : CochainComplex (ℕᵒᵖ ⥤ A D l E) ℤ) (p : ℤ),
    (signedCoordinates V p).inv ≫ (roosF.obj V).d (p + 1) (p + 1 + 1) ≫
        (signedCoordinates V (p + 1)).hom =
      biprod.desc
        (biprod.lift ((roosP V).d (p + 1) (p + 1 + 1)) ((roosU V).f (p + 1)))
        (biprod.lift 0 (-((roosP V).d p (p + 1))))
```

The old realization body is:

```lean
  (LA D l E).mapIso ((U D l E).mapDerivedCategoryFactors.app M) ≪≫
    theta.app ((X D l E).obj M)
```

The old Abelian instance is:

```lean
instance ambientAbelian : Abelian (A D l E) := inferInstance
```

## New

```lean
section GenericData
variable {S C B : Type*} [Category* S] [Category* C] [Category* B]
  [Abelian S] [Abelian C] [Abelian B]
  [HasCountableProducts C] [HasCountableProducts B]
  [HasLimitsOfShape ℕᵒᵖ C] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory S] [HasDerivedCategory C] [HasDerivedCategory B]
  [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ C)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
  [(lim : (ℕᵒᵖ ⥤ C) ⥤ C).Additive] [(lim : (ℕᵒᵖ ⥤ B) ⥤ B).Additive]
  (U : S ⥤ (ℕᵒᵖ ⥤ C)) [U.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (G : S ⥤ S) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (T : C ⥤ B) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  (sections_property : (G.mapHomologicalComplex (.up ℤ) ⋙ U.mapHomologicalComplex (.up ℤ) ≅
    U.mapHomologicalComplex (.up ℤ) ⋙ ((Functor.whiskeringRight ℕᵒᵖ C C).obj
      F).mapHomologicalComplex (.up ℤ)) → Prop)
  (projection_property tensor_unit_property : Prop)

/-- The simultaneous comparison bundle, parametrized before specializing the coefficient site.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-normalized-comparison-data). -/
structure DataCore where
  coefficient : G.mapHomologicalComplex (.up ℤ) ⋙ U.mapHomologicalComplex (.up ℤ) ≅
    U.mapHomologicalComplex (.up ℤ) ⋙ ((Functor.whiskeringRight ℕᵒᵖ C C).obj
      F).mapHomologicalComplex (.up ℤ)
  coefficient_sections : sections_property coefficient
  coefficient_projection : projection_property
  finite_tensor_unit : tensor_unit_property
  theta : DerivedCategory.Q ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor ≅ roosF ⋙ DerivedCategory.Q
  theta_normalized : ModelNormalization theta
  eta : DerivedCategory.Q ⋙ (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor ≅ roosF ⋙ DerivedCategory.Q
  eta_normalized : ModelNormalization eta
  inverseImage : Comparison F theta theta
  sections : Comparison T theta eta
  a : (U.mapDerivedCategory ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor) ⋙ F.mapDerivedCategory ≅
    G.mapDerivedCategory ⋙ (U.mapDerivedCategory ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor)
  zeta : (U ⋙ (Functor.whiskeringRight ℕᵒᵖ C B).obj T).mapDerivedCategory ⋙ (lim : (ℕᵒᵖ ⥤ B) ⥤
    B).rightDerivedFunctor ≅
    (U.mapDerivedCategory ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor) ⋙ T.mapDerivedCategory
  a_model : ∀ M : CochainComplex S ℤ,
    a.hom.app (DerivedCategory.Q.obj M) ≫
      (U.mapDerivedCategory ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor).map
        (G.mapDerivedCategoryFactors.hom.app M) ≫
      (systemModel U theta ((G.mapHomologicalComplex (.up ℤ)).obj M)).hom =
    F.mapDerivedCategory.map ((systemModel U theta M).hom) ≫
      F.mapDerivedCategoryFactors.hom.app (roosF.obj ((U.mapHomologicalComplex (.up ℤ)).obj M)) ≫
      DerivedCategory.Q.map (inverseImage.kappa.hom.app ((U.mapHomologicalComplex (.up ℤ)).obj M)) ≫
      DerivedCategory.Q.map (roosF.map (coefficient.inv.app M))
  zeta_model : ∀ M : CochainComplex S ℤ,
    zeta.hom.app (DerivedCategory.Q.obj M) ≫
      T.mapDerivedCategory.map ((systemModel U theta M).hom) ≫
      T.mapDerivedCategoryFactors.hom.app (roosF.obj ((U.mapHomologicalComplex (.up ℤ)).obj M)) ≫
      DerivedCategory.Q.map (sections.kappa.hom.app ((U.mapHomologicalComplex (.up ℤ)).obj M)) =
    (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.map
      ((U ⋙ (Functor.whiskeringRight ℕᵒᵖ C B).obj T).mapDerivedCategoryFactors.hom.app M) ≫
      eta.hom.app (((U ⋙ (Functor.whiskeringRight ℕᵒᵖ C B).obj T).mapHomologicalComplex (.up
        ℤ)).obj M)
  signed_differential : ∀ (V : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) (p : ℤ),
    (signedCoordinates V p).inv ≫ (roosF.obj V).d (p + 1) (p + 1 + 1) ≫
      (signedCoordinates V (p + 1)).hom =
    biprod.desc
      (biprod.lift ((roosP V).d (p + 1) (p + 1 + 1)) ((roosU V).f (p + 1)))
      (biprod.lift 0 (-((roosP V).d p (p + 1))))

private theorem dataCore_nonempty
    (coefficient : G.mapHomologicalComplex (.up ℤ) ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      U.mapHomologicalComplex (.up ℤ) ⋙
        ((Functor.whiskeringRight ℕᵒᵖ C C).obj F).mapHomologicalComplex (.up ℤ))
    (hc : sections_property coefficient) (hp : projection_property)
    (ht : tensor_unit_property)
    (theta : DerivedCategory.Q ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor ≅
      roosF ⋙ DerivedCategory.Q)
    (eta : DerivedCategory.Q ⋙ (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor ≅
      roosF ⋙ DerivedCategory.Q)
    (htheta : ∀ I : CochainComplex (ℕᵒᵖ ⥤ C) ℤ,
      (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctorUnitQ I ≫ theta.hom.app I =
        DerivedCategory.Q.map (ordinaryInclusion I))
    (heta : ∀ I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ,
      (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctorUnitQ I ≫ eta.hom.app I =
        DerivedCategory.Q.map (ordinaryInclusion I))
    (hF : ∀ M : ℕ → C, IsIso (piComparison F M))
    (hT : ∀ M : ℕ → C, IsIso (piComparison T M)) :
    Nonempty (DataCore U G F T sections_property projection_property tensor_unit_property) := by
  obtain ⟨fc⟩ := makeComparison F theta theta htheta htheta hF
  obtain ⟨tc⟩ := makeComparison T theta eta htheta heta hT
  obtain ⟨a, zeta, ha, hz⟩ :=
    realizationDescentGeneric U G F T theta eta coefficient fc tc
  refine ⟨{
    coefficient := coefficient
    coefficient_sections := hc
    coefficient_projection := hp
    finite_tensor_unit := ht
    theta := theta
    theta_normalized := ?_
    eta := eta
    eta_normalized := ?_
    inverseImage := fc
    sections := tc
    a := a
    zeta := zeta
    a_model := ha
    zeta_model := hz
    signed_differential := signedDifferential }⟩
  · unfold ModelNormalization
    exact normalizedCoordinates theta htheta
  · unfold ModelNormalization
    exact normalizedCoordinates eta heta
end GenericData

/-- Specialization of the simultaneous bundle to the actual point coefficient systems.
All fields retain their original equations.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-normalized-comparison-data). -/
abbrev Data (r : ℕ) :=
  DataCore (U D l E) (G D l E r) (F D l E r) (T D l E)
    (DataCoefficientSections D l E r) (DataCoefficientProjection D l E r)
    (DataFiniteTensorUnit D l E r)
```

The named field predicates are:

```lean
def ModelNormalization
    {C : Type a} [Category.{b} C] [Abelian C]
    [HasCountableProducts C] [HasLimitsOfShape ℕᵒᵖ C]
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wTC} (ℕᵒᵖ ⥤ C)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ C)]
    [(lim : (ℕᵒᵖ ⥤ C) ⥤ C).Additive]
    (theta : DerivedCategory.Q ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor ≅
      roosF ⋙ DerivedCategory.Q) : Prop :=
  ∀ (I : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) [I.IsKInjective]
    (_hI : ∀ p : ℤ, Injective (I.X p)),
    ∃ iota : ((lim : (ℕᵒᵖ ⥤ C) ⥤ C).mapHomologicalComplex (.up ℤ)).obj I ⟶
      roosF.obj I,
      QuasiIso iota ∧
      (∀ p : ℤ, iota.f (p + 1) ≫ (roosχ I p).hom =
        biprod.lift 0 ((Pi.lift (fun n : ℕ ↦
          (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I)).f (p + 1))) ∧
      (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctorUnitQ I ≫
        theta.hom.app I = DerivedCategory.Q.map iota

attribute [local irreducible] ModelNormalization

/-- The recorded comparison equation, named without changing its content.
Source: blueprint proof (3)
(blueprint: lem-trf-point-system-normalized-comparison-data). -/
def DataCoefficientSections (r : ℕ)
    (coefficient : (G D l E r).mapHomologicalComplex (.up ℤ) ⋙ X D l E ≅
      X D l E ⋙ ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
        (F D l E r)).mapHomologicalComplex (.up ℤ)) : Prop :=
  ∀ (M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ)
      (i : ℤ) (n : ℕ) (V : (Spec (.of D.k)).ProEt)
      (x : ((((G D l E r).mapHomologicalComplex (.up ℤ) ⋙ X D l E).obj M).X i).obj
        (op n) |>.val.obj (op V)),
      HEq (((((coefficient.hom.app M).f i).app (op n)).val.app (op V)) x) x

/-- The recorded comparison equation, named without changing its content.
Source: blueprint proof (3)
(blueprint: lem-trf-point-system-normalized-comparison-data). -/
def DataCoefficientProjection (r : ℕ) : Prop :=
  ∀ n : ℕ,
    inverseImageCompletedCoefficientMap l E (PointSystemTransport.pointPower D r).hom ≫
        limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op n) =
      (isoSectionwiseInverseImage (PointSystemTransport.pointPower D r).hom
        RingCat.{max u (t + 1)}).map
          (limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op n)) ≫
        inverseImageFiniteCoefficientMap l E (PointSystemTransport.pointPower D r).hom n

/-- The recorded comparison equation, named without changing its content.
Source: blueprint proof (3)
(blueprint: lem-trf-point-system-normalized-comparison-data). -/
def DataFiniteTensorUnit (r : ℕ) : Prop :=
  ∀ (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ),
    IsIso (inverseImageFiniteComparisonComplex l E
      (PointSystemTransport.pointPower D r).hom n K)

attribute [local irreducible] systemModel
```

The generic realization helper is:

```lean
def systemModel
    (theta : DerivedCategory.Q ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor ≅
      roosF ⋙ DerivedCategory.Q) (M : CochainComplex S ℤ) :=
  (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor.mapIso
    (U.mapDerivedCategoryFactors.app M) ≪≫
    theta.app ((U.mapHomologicalComplex (.up ℤ)).obj M)
```

The realization body is now `systemModel (U D l E) theta M`, definitionally the
original composite. Its definition is sealed locally after its equation is established,
so bundle checking uses its stated type. Countable product and tower limit instances are
cached privately. The new Abelian instance is:

```lean
@[reducible] instance ambientAbelian : Abelian (A D l E) := inferInstance
```

Field notation resolves to `DataCore` projections. The consumer has no use of the old
`Data.mk` or `Data.rec` interface.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PointSystemNormalizedComparisonData | H3 | Both original theorems proved; all sixteen fields constructed. |
| Sheaf.Paper.PointSystemRoosTransport | Q2 | Uses this module's `exact_products`; its `Data` occurrences name its own bundle. No adaptation required. |

The users are the output of `tools/downstream.py` with the qualified `Data` name. The
consumer check was submitted against the final module; an earlier run stopped at the
item module because of the time limit. The delivery performs its required consumer checks.

## Status

landed 20261025T202151-L-2685512 2026-10-25 (merge of deliver/H3/Sheaf.Paper.PointSystemNormalizedComparisonData)
