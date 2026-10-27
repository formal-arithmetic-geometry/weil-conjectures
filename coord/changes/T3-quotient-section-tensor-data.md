# AlgebraicGeometry.ProEtale.QuotientSectionTensor normalization data

## Reason

Separate the fixed normalization definitions from the theorem that assembles them.
The scalar tensor construction, regular-unit proof and independent section transport
lemmas need the same definitions without importing their parent theorem. This prevents
an import cycle. This is a verbatim relocation, apart from docstring node tags.
No binder, instance, public attribute, formula, data choice, or target statement changes.
The parent reexports the new prerequisite with `public import`; the original public
import closure is retained through that prerequisite. No adopted source module changes.
The quarantine attachment and the parent theorem's dependency route are preserved.

## Old

The following declarations were in
`lean/Sheaf/Paper/QuotientSectionTensorNormalization.lean`:

```lean
/-- The actual section-ring quotient map, with the site's Hom universe retained.
Source: Stacks 03EL (blueprint: lem-sfb-quotient-section-tensor-normalization). -/
abbrev sectionQuotient (T : Scheme.{u}) :=
  CondensedRing.sectionRingMap T (coefficientMap a T)

/-- A universal sectionwise scalar-extension model from the recorded change-of-rings API.
Source: Stacks 06YY (blueprint: lem-sfb-quotient-section-tensor-normalization). -/
abbrev SectionModel (T : Scheme.{u})
    [HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
    [HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)] :=
  SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 1, u + 1}
    (sectionQuotient a T)

/-- The ordinary scalar-unit normalized tensorator, totalized with the signed differential.
Source: Stacks 03EL and 07A4
(blueprint: lem-sfb-quotient-section-tensor-normalization). -/
def totalScalar (T : Scheme.{u})
    (P Q : CochainComplex (Modules Λ T) ℤ) :
    ((extension a T).mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ⟶
      ((extension a T).mapHomologicalComplex (.up ℤ)).obj P ⊗
        ((extension a T).mapHomologicalComplex (.up ℤ)).obj Q :=
  letI := CondensedRing.internalScalarMonoidal a T
  HomologicalComplex.mapBifunctorComparison
    (Functor.OplaxMonoidal.δNatTrans (extension a T)) (.up ℤ) P Q

/-- Normalization on every flat-term K-flat pair by the actual localization counits.
The ordinary tensorator is the balancing map (u tensor v) tensor s to
(u tensor 1) tensor (v tensor s), rather than a freely chosen isomorphism.
Source: Stacks 07A4 (blueprint: lem-sfb-quotient-section-tensor-normalization). -/
def TensorNormalized (T : Scheme.{u})
    (b : Functor.uncurry.obj (CondensedRing.derivedTensor Λ T) ⋙
        D a T ≅
      ((D a T).prod (D a T)) ⋙
        Functor.uncurry.obj (CondensedRing.derivedTensor Λ' T)) : Prop :=
  letI : (DerivedCategory.Q (C := Modules Λ T)).LaxMonoidal := Mod.laxMonoidalQ
  letI : (DerivedCategory.Q (C := Modules Λ' T)).LaxMonoidal := Mod.laxMonoidalQ
  ∀ P Q : CochainComplex (Modules Λ T) ℤ,
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q →
    (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
    (∀ i : ℤ, ObjectProperty.flat (Q.X i)) →
      b.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          (compute a T P ⊗ₘ compute a T Q) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q
            (((extension a T).mapHomologicalComplex (.up ℤ)).obj P)
            (((extension a T).mapHomologicalComplex (.up ℤ)).obj Q) =
        (D a T).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
          compute a T (P ⊗ Q) ≫
          DerivedCategory.Q.map (totalScalar a T P Q)

set_option backward.isDefEq.respectTransparency false in
/-- The regular scalar unit localized in degree zero, using multiplication in the quotient.
Source: Stacks 03EL and 07A4
(blueprint: lem-sfb-quotient-section-tensor-normalization). -/
def scalarRegularUnit (T : Scheme.{u}) :
    (D a T).obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj (𝟙_ (Modules Λ T)))) ⟶
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj (𝟙_ (Modules Λ' T))) :=
  letI := CondensedRing.internalScalarMonoidal a T
  compute a T _ ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (extension a T) (.up ℤ) 0).hom.app (𝟙_ _)) ≫
    DerivedCategory.Q.map ((HomologicalComplex.single _ (.up ℤ) 0).map
      (Functor.OplaxMonoidal.η (extension a T)))

open ModuleRingedComparison

variable [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

/-- The ordinary and derived scalar comparisons, normalized on section generators and
by the universal localization counits. The target is an actual sectionwise extension
model, so c is a map of quotient-module sheaves, retaining the quotient action.
Source: Stacks 03EK, 03EL, 06YY
(blueprint: lem-sfb-quotient-section-tensor-normalization). -/
structure ScalarSectionData (T : Scheme.{u}) where
  model : SectionModel a T
  ordinary : QuotientChange.extension a T ⋙
      (equivalence Λ' T).functor ≅
    (equivalence Λ T).functor ⋙ model.E
  derived : D a T ⋙ derivedFunctor Λ' T ≅
    derivedFunctor Λ T ⋙ model.T

/-- The scalar section comparisons are fixed on scalar-unit generators and by the
localization counits. In particular the quotient action is retained.
Source: Stacks 03EL, 06YY
(blueprint: lem-sfb-quotient-section-tensor-normalization). -/
def ScalarSectionNormalized (T : Scheme.{u}) (c : ScalarSectionData a T) : Prop :=
  (∀ (M : Modules Λ T) (W : T.ProEtᵒᵖ) (m : M.X.obj.obj W),
    (((c.ordinary.hom.app M) ≫ eqToHom (c.model.obj_eq _)).val.app W)
        (((Mod.extendUnit (ProEtale.coefficientMap a T) M).hom.hom.app W) m) =
      (toSheafify (Scheme.ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheaf (sectionQuotient a T)
          ((equivalence Λ T).functor.obj M)).presheaf).app W
            ((1 : (ring Λ' T).obj.obj W)
              ⊗ₜ[(ring Λ T).obj.obj W,
                ((sectionQuotient a T).hom.app W).hom] m)) ∧
  ∀ P : CochainComplex (Modules Λ T) ℤ,
    c.derived.hom.app (DerivedCategory.Q.obj P) ≫
        c.model.T.map (sectionLocalizationComparison Λ T P).hom ≫
        c.model.ε.app
          (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P) =
      (derivedFunctor Λ' T).map (compute a T P) ≫
        (sectionLocalizationComparison Λ' T
          (((QuotientChange.extension a T).mapHomologicalComplex
            (.up ℤ)).obj P)).hom ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso c.ordinary (.up ℤ)).hom.app P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
            (Iso.refl ((equivalence Λ T).functor ⋙ c.model.E)) (.up ℤ)).inv.app P)

/-- The derived tensor bifunctor before scalar extension.
Source: Stacks 07A4 (blueprint: lem-sfb-quotient-section-tensor-normalization). -/
abbrev TensorIso (T : Scheme.{u}) :=
  Functor.uncurry.obj (CondensedRing.derivedTensor Λ T) ⋙ D a T ≅
    ((D a T).prod (D a T)) ⋙ Functor.uncurry.obj (CondensedRing.derivedTensor Λ' T)

set_option backward.isDefEq.respectTransparency false in
/-- The scalar regular unit in the derived monoidal category, using its actual
homotopy-localization unit and the ordinary multiplication unit.
Source: Stacks 03EL, 07A4
(blueprint: lem-sfb-quotient-section-tensor-normalization). -/
def derivedScalarUnit (T : Scheme.{u}) :
    (D a T).obj (𝟙_ (DerivedCategory (Modules Λ T))) ⟶
      𝟙_ (DerivedCategory (Modules Λ' T)) :=
  letI := CondensedRing.internalScalarMonoidal a T
  letI := DerivedCategory.isIso_ε_Qh (Modules Λ' T)
  (D a T).map (Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := Modules Λ T))) ≫
    (scalarCounit a T).app (𝟙_ (HomotopyCategory (Modules Λ T) (.up ℤ))) ≫
    DerivedCategory.Qh.map
      (((QuotientChange.extension a T).mapHomotopyCategoryFactors (.up ℤ)).hom.app
          (𝟙_ (CochainComplex (Modules Λ T) ℤ)) ≫
        (HomotopyCategory.quotient _ (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex
            (QuotientChange.extension a T) (.up ℤ) 0).hom.app (𝟙_ _) ≫
            (HomologicalComplex.single _ (.up ℤ) 0).map
              (Functor.OplaxMonoidal.η (QuotientChange.extension a T)))) ≫
    inv (Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := Modules Λ' T)))

/-- The tensor comparison has the regular scalar unit and the tensor constraints.
Source: Stacks 03EL, 07A4
(blueprint: lem-sfb-quotient-section-tensor-normalization). -/
def UnitCondition (T : Scheme.{u}) (b : TensorIso a T) : Prop :=
  IsIso (scalarRegularUnit a T) ∧ IsIso (derivedScalarUnit a T) ∧
    TensorConstraintCondition (D a T)
      (Functor.uncurry.obj (CondensedRing.derivedTensor Λ T))
      (Functor.uncurry.obj (CondensedRing.derivedTensor Λ' T))
      (𝟙_ (DerivedCategory (Modules Λ T))) (𝟙_ (DerivedCategory (Modules Λ' T)))
      (fun M N P ↦ α_ M N P) (fun M ↦ λ_ M) (fun M ↦ ρ_ M)
      (fun M N P ↦ α_ M N P) (fun M ↦ λ_ M) (fun M ↦ ρ_ M)
      b.hom (derivedScalarUnit a T)

/-- The actual sheafified scalar generator in the chosen ordinary section model.
The left-scalar convention s tensor m denotes m tensor s in the statement.
Source: Stacks 03EL (blueprint: lem-sfb-quotient-section-tensor-normalization). -/
def sectionScalarElement (T : Scheme.{u}) (c : ScalarSectionData a T)
    (M : modules Λ T) (W : T.ProEtᵒᵖ) (m : M.val.obj W)
    (s : (ring Λ' T).obj.obj W) : (c.model.E.obj M).val.obj W :=
  (eqToHom (c.model.obj_eq M).symm).val.app W
    ((toSheafify (Scheme.ProEt.topology T)
      (SheafOfModules.changeOfRingsPresheaf (sectionQuotient a T) M).presheaf).app W
        (s ⊗ₜ[(ring Λ T).obj.obj W, ((sectionQuotient a T).hom.app W).hom] m))

attribute [local irreducible] sectionScalarElement
  ModuleRingedComparison.qTensor

set_option backward.isDefEq.respectTransparency false in
/-- Section-side characterization of the canonical scalar tensor comparison.
The ordinary map is fixed on every sheafified pure scalar tensor. On every flat-term
K-flat pair its signed total, specified on each (i,j) summand, computes barB through
the model's own universal counit and the fixed section tensor localization maps.
Source: Stacks 03EK, 03EL and 07A4
(blueprint: lem-sfb-quotient-section-tensor-normalization). -/
def SectionTensorNormalized (T : Scheme.{u}) (c : ScalarSectionData a T)
    (barB : tensor Λ T ⋙ c.model.T ≅
      (c.model.T.prod c.model.T) ⋙ tensor Λ' T) : Prop :=
  ∃ e : (Functor.postcompose₂.obj c.model.E).obj (curriedTensor (modules Λ T)) ⟶
      (((Functor.whiskeringLeft₂ _).obj c.model.E).obj c.model.E).obj
        (curriedTensor (modules Λ' T)),
    (∀ (M N : modules Λ T) (W : T.ProEtᵒᵖ) (m : M.val.obj W) (n : N.val.obj W)
      (s : (ring Λ' T).obj.obj W),
      (((e.app M).app N).val.app W)
          (sectionScalarElement a T c (M ⊗ N) W (sectionPureTensor Λ T M N W m n) s) =
        sectionPureTensor Λ' T (c.model.E.obj M) (c.model.E.obj N) W
          (sectionScalarElement a T c M W m 1) (sectionScalarElement a T c N W n s)) ∧
    ∀ P Q : CochainComplex (modules Λ T) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ T) P →
      CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ T) Q →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology T)
        (R := ring Λ T) (P.X i)) →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology T)
        (R := ring Λ T) (Q.X i)) →
      ∃ g : (c.model.E.mapHomologicalComplex (.up ℤ)).obj ((totalTensor Λ T).obj (P, Q)) ⟶
          (totalTensor Λ' T).obj
            ((c.model.E.mapHomologicalComplex (.up ℤ)).obj P,
              (c.model.E.mapHomologicalComplex (.up ℤ)).obj Q),
        (∀ (i j k : ℤ) (h : i + j = k),
          c.model.E.map
              (CochainComplex.ιMapBifunctor P Q (curriedTensor (modules Λ T)) i j k h) ≫
              g.f k =
            (e.app (P.X i)).app (Q.X j) ≫
              CochainComplex.ιMapBifunctor
                ((c.model.E.mapHomologicalComplex (.up ℤ)).obj P)
                ((c.model.E.mapHomologicalComplex (.up ℤ)).obj Q)
                (curriedTensor (modules Λ' T)) i j k h) ∧
        barB.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
            (tensor Λ' T).map (Prod.mkHom (c.model.ε.app P) (c.model.ε.app Q)) ≫
            (qTensor Λ' T).app
              ((c.model.E.mapHomologicalComplex (.up ℤ)).obj P,
                (c.model.E.mapHomologicalComplex (.up ℤ)).obj Q) =
          c.model.T.map ((qTensor Λ T).app (P, Q)) ≫
            c.model.ε.app ((totalTensor Λ T).obj (P, Q)) ≫ DerivedCategory.Q.map g

/-- The section image of the scalar tensorator, using the fixed tensor comparisons.
SectionTensorNormalized separately fixes its signed-total balancing normalization
on all section flat-term K-flat pairs.
Source: Stacks 03EL, 06YY and 07A4
(blueprint: lem-sfb-quotient-section-tensor-normalization). -/
def TensorSectionCondition (T : Scheme.{u}) (c : ScalarSectionData a T)
    (b : TensorIso a T)
    (barB : tensor Λ T ⋙ c.model.T ≅
      (c.model.T.prod c.model.T) ⋙ tensor Λ' T) : Prop :=
  ∀ M N : DerivedCategory (Modules Λ T),
    (derivedFunctor Λ' T).map (b.hom.app (M, N)) ≫
        (tensorComparison Λ' T).hom.app ((D a T).obj M, (D a T).obj N) =
      c.derived.hom.app (M ⊗ N) ≫
        c.model.T.map ((tensorComparison Λ T).hom.app (M, N)) ≫
        barB.hom.app ((derivedFunctor Λ T).obj M, (derivedFunctor Λ T).obj N) ≫
        (tensor Λ' T).map (Prod.mkHom (c.derived.inv.app M) (c.derived.inv.app N))

/-- The actual pullback tensor transformation and both adjunction structure maps
become the specified ringed operations under the fixed geometric comparisons.
Source: Stacks 07A4, 07A6
(blueprint: lem-sfb-quotient-section-tensor-normalization). -/
def GeometricCondition
    (B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj B] [IsCommMonObj B]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules B T)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  (∀ M N : DerivedCategory (internalModules B Y),
    HEq ((derivedFunctor B X).map
      (((CondensedRing.leftDerivedUpperStarTensor B f).app M).app N))
      ((derivedPullComparison B f).hom.app (M ⊗ N) ≫
        (derivedPullback B f).map ((tensorComparison B Y).hom.app (M, N)) ≫
        (tensorPullComparison B f).hom.app
          ((derivedFunctor B Y).obj M, (derivedFunctor B Y).obj N) ≫
        (tensor B X).map (Prod.mkHom
          ((derivedPullComparison B f).inv.app M) ((derivedPullComparison B f).inv.app N)) ≫
        (tensorComparison B X).inv.app
          ((internalDerivedPullback B f).obj M, (internalDerivedPullback B f).obj N))) ∧
  (∀ M : DerivedCategory (internalModules B Y),
    (derivedAdjunction B f).unit.app ((derivedFunctor B Y).obj M) =
      (derivedFunctor B Y).map ((normalizationInternalAdjunction B f).unit.app M) ≫
        (derivedPushComparison B f).hom.app ((internalDerivedPullback B f).obj M) ≫
        (derivedPushforward B f).map ((derivedPullComparison B f).hom.app M)) ∧
  (∀ N : DerivedCategory (internalModules B X),
    (derivedAdjunction B f).counit.app ((derivedFunctor B X).obj N) =
      (derivedPullback B f).map ((derivedPushComparison B f).inv.app N) ≫
        (derivedPullComparison B f).inv.app ((internalDerivedPushforward B f).obj N) ≫
        (derivedFunctor B X).map ((normalizationInternalAdjunction B f).counit.app N))

attribute [local semireducible] QuotientChange.L

/-- Section-side scalar/pullback normalization by the ordinary balancing comparison
and the actual section pullback localization maps and scalar-model counits.
The ordinary comparison is fixed through the ordinary section equivalences, independently
of lam or barLam: it carries f inverse (x tensor s) to f inverse x tensor f inverse s.
Source: Stacks 03EL, 0D6D and 0G7E
(blueprint: lem-sfb-quotient-section-tensor-normalization). -/
def SectionPullNormalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (barLam : cY.model.T ⋙ derivedPullback Λ' f ≅
      derivedPullback Λ f ⋙ cX.model.T) : Prop :=
  ∃ e : cY.model.E ⋙ pullback Λ' f ≅ pullback Λ f ⋙ cX.model.E,
    (∀ M : Modules Λ Y,
      (equivalence Λ' X).functor.map ((CondensedRing.pullIso a f).inv.app M) ≫
          cX.ordinary.hom.app ((CondensedRing.upperStar Λ f).obj M) ≫
          cX.model.E.map ((pullComparison Λ f).hom.app M) =
        (pullComparison Λ' f).hom.app ((QuotientChange.extension a Y).obj M) ≫
          (pullback Λ' f).map (cY.ordinary.hom.app M) ≫
          e.hom.app ((equivalence Λ Y).functor.obj M)) ∧
    ∀ P : CochainComplex (modules Λ Y) ℤ,
      barLam.hom.app (DerivedCategory.Q.obj P) ≫
          cX.model.T.map ((pullback Λ f).mapDerivedCategoryFactors.hom.app P) ≫
          cX.model.ε.app (((pullback Λ f).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
            (Iso.refl (pullback Λ f ⋙ cX.model.E)) (.up ℤ)).hom.app P) =
        (derivedPullback Λ' f).map (cY.model.ε.app P) ≫
          (pullback Λ' f).mapDerivedCategoryFactors.hom.app
            ((cY.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P)

/-- Conjugation of the specified scalar/pullback comparison by the same scalar and
geometric realization maps. SectionPullNormalized separately fixes the ringed
comparison through the section pullback and scalar-model computation counits.
Source: Stacks 0D6D, 0G7E, 07A6
(blueprint: lem-sfb-quotient-section-tensor-normalization). -/
def PullSectionCondition {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X)
    (barLam : cY.model.T ⋙ derivedPullback Λ' f ≅
      derivedPullback Λ f ⋙ cX.model.T) : Prop :=
  ∀ M : DerivedCategory (Modules Λ Y),
    (derivedFunctor Λ' X).map (lam.hom.app M) ≫
        cX.derived.hom.app ((L Λ f).obj M) ≫
        cX.model.T.map ((derivedPullComparison Λ f).hom.app M) =
      (derivedPullComparison Λ' f).hom.app ((D a Y).obj M) ≫
        (derivedPullback Λ' f).map (cY.derived.hom.app M) ≫
        barLam.hom.app ((derivedFunctor Λ Y).obj M)
```

## New

The declaration block above is moved verbatim to
`lean/Sheaf/Paper/QuotientSectionTensorData.lean` (only its docstring blueprint tags
now name `def-sfb-quotient-section-tensor-data`). The parent publicly imports that
module, so every existing qualified declaration name and its visibility is retained.
`ComparisonSpec` and `quotient_section_tensor_normalization` stay in the parent.
The old private proof imports leave the parent; the new proof imports name its
actual independent proof steps. The public import closure is unchanged.

```lean
/-- The actual section-ring quotient map, with the site's Hom universe retained.
Source: Stacks 03EL (blueprint: def-sfb-quotient-section-tensor-data). -/
abbrev sectionQuotient (T : Scheme.{u}) :=
  CondensedRing.sectionRingMap T (coefficientMap a T)

/-- A universal sectionwise scalar-extension model from the recorded change-of-rings API.
Source: Stacks 06YY (blueprint: def-sfb-quotient-section-tensor-data). -/
abbrev SectionModel (T : Scheme.{u})
    [HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
    [HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)] :=
  SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 1, u + 1}
    (sectionQuotient a T)

/-- The ordinary scalar-unit normalized tensorator, totalized with the signed differential.
Source: Stacks 03EL and 07A4
(blueprint: def-sfb-quotient-section-tensor-data). -/
def totalScalar (T : Scheme.{u})
    (P Q : CochainComplex (Modules Λ T) ℤ) :
    ((extension a T).mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ⟶
      ((extension a T).mapHomologicalComplex (.up ℤ)).obj P ⊗
        ((extension a T).mapHomologicalComplex (.up ℤ)).obj Q :=
  letI := CondensedRing.internalScalarMonoidal a T
  HomologicalComplex.mapBifunctorComparison
    (Functor.OplaxMonoidal.δNatTrans (extension a T)) (.up ℤ) P Q

/-- Normalization on every flat-term K-flat pair by the actual localization counits.
The ordinary tensorator is the balancing map (u tensor v) tensor s to
(u tensor 1) tensor (v tensor s), rather than a freely chosen isomorphism.
Source: Stacks 07A4 (blueprint: def-sfb-quotient-section-tensor-data). -/
def TensorNormalized (T : Scheme.{u})
    (b : Functor.uncurry.obj (CondensedRing.derivedTensor Λ T) ⋙
        D a T ≅
      ((D a T).prod (D a T)) ⋙
        Functor.uncurry.obj (CondensedRing.derivedTensor Λ' T)) : Prop :=
  letI : (DerivedCategory.Q (C := Modules Λ T)).LaxMonoidal := Mod.laxMonoidalQ
  letI : (DerivedCategory.Q (C := Modules Λ' T)).LaxMonoidal := Mod.laxMonoidalQ
  ∀ P Q : CochainComplex (Modules Λ T) ℤ,
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q →
    (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
    (∀ i : ℤ, ObjectProperty.flat (Q.X i)) →
      b.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          (compute a T P ⊗ₘ compute a T Q) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q
            (((extension a T).mapHomologicalComplex (.up ℤ)).obj P)
            (((extension a T).mapHomologicalComplex (.up ℤ)).obj Q) =
        (D a T).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
          compute a T (P ⊗ Q) ≫
          DerivedCategory.Q.map (totalScalar a T P Q)

set_option backward.isDefEq.respectTransparency false in
/-- The regular scalar unit localized in degree zero, using multiplication in the quotient.
Source: Stacks 03EL and 07A4
(blueprint: def-sfb-quotient-section-tensor-data). -/
def scalarRegularUnit (T : Scheme.{u}) :
    (D a T).obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj (𝟙_ (Modules Λ T)))) ⟶
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj (𝟙_ (Modules Λ' T))) :=
  letI := CondensedRing.internalScalarMonoidal a T
  compute a T _ ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (extension a T) (.up ℤ) 0).hom.app (𝟙_ _)) ≫
    DerivedCategory.Q.map ((HomologicalComplex.single _ (.up ℤ) 0).map
      (Functor.OplaxMonoidal.η (extension a T)))

open ModuleRingedComparison

variable [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

/-- The ordinary and derived scalar comparisons, normalized on section generators and
by the universal localization counits. The target is an actual sectionwise extension
model, so c is a map of quotient-module sheaves, retaining the quotient action.
Source: Stacks 03EK, 03EL, 06YY
(blueprint: def-sfb-quotient-section-tensor-data). -/
structure ScalarSectionData (T : Scheme.{u}) where
  model : SectionModel a T
  ordinary : QuotientChange.extension a T ⋙
      (equivalence Λ' T).functor ≅
    (equivalence Λ T).functor ⋙ model.E
  derived : D a T ⋙ derivedFunctor Λ' T ≅
    derivedFunctor Λ T ⋙ model.T

/-- The scalar section comparisons are fixed on scalar-unit generators and by the
localization counits. In particular the quotient action is retained.
Source: Stacks 03EL, 06YY
(blueprint: def-sfb-quotient-section-tensor-data). -/
def ScalarSectionNormalized (T : Scheme.{u}) (c : ScalarSectionData a T) : Prop :=
  (∀ (M : Modules Λ T) (W : T.ProEtᵒᵖ) (m : M.X.obj.obj W),
    (((c.ordinary.hom.app M) ≫ eqToHom (c.model.obj_eq _)).val.app W)
        (((Mod.extendUnit (ProEtale.coefficientMap a T) M).hom.hom.app W) m) =
      (toSheafify (Scheme.ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheaf (sectionQuotient a T)
          ((equivalence Λ T).functor.obj M)).presheaf).app W
            ((1 : (ring Λ' T).obj.obj W)
              ⊗ₜ[(ring Λ T).obj.obj W,
                ((sectionQuotient a T).hom.app W).hom] m)) ∧
  ∀ P : CochainComplex (Modules Λ T) ℤ,
    c.derived.hom.app (DerivedCategory.Q.obj P) ≫
        c.model.T.map (sectionLocalizationComparison Λ T P).hom ≫
        c.model.ε.app
          (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P) =
      (derivedFunctor Λ' T).map (compute a T P) ≫
        (sectionLocalizationComparison Λ' T
          (((QuotientChange.extension a T).mapHomologicalComplex
            (.up ℤ)).obj P)).hom ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso c.ordinary (.up ℤ)).hom.app P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
            (Iso.refl ((equivalence Λ T).functor ⋙ c.model.E)) (.up ℤ)).inv.app P)

/-- The derived tensor bifunctor before scalar extension.
Source: Stacks 07A4 (blueprint: def-sfb-quotient-section-tensor-data). -/
abbrev TensorIso (T : Scheme.{u}) :=
  Functor.uncurry.obj (CondensedRing.derivedTensor Λ T) ⋙ D a T ≅
    ((D a T).prod (D a T)) ⋙ Functor.uncurry.obj (CondensedRing.derivedTensor Λ' T)

set_option backward.isDefEq.respectTransparency false in
/-- The scalar regular unit in the derived monoidal category, using its actual
homotopy-localization unit and the ordinary multiplication unit.
Source: Stacks 03EL, 07A4
(blueprint: def-sfb-quotient-section-tensor-data). -/
def derivedScalarUnit (T : Scheme.{u}) :
    (D a T).obj (𝟙_ (DerivedCategory (Modules Λ T))) ⟶
      𝟙_ (DerivedCategory (Modules Λ' T)) :=
  letI := CondensedRing.internalScalarMonoidal a T
  letI := DerivedCategory.isIso_ε_Qh (Modules Λ' T)
  (D a T).map (Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := Modules Λ T))) ≫
    (scalarCounit a T).app (𝟙_ (HomotopyCategory (Modules Λ T) (.up ℤ))) ≫
    DerivedCategory.Qh.map
      (((QuotientChange.extension a T).mapHomotopyCategoryFactors (.up ℤ)).hom.app
          (𝟙_ (CochainComplex (Modules Λ T) ℤ)) ≫
        (HomotopyCategory.quotient _ (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex
            (QuotientChange.extension a T) (.up ℤ) 0).hom.app (𝟙_ _) ≫
            (HomologicalComplex.single _ (.up ℤ) 0).map
              (Functor.OplaxMonoidal.η (QuotientChange.extension a T)))) ≫
    inv (Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := Modules Λ' T)))

/-- The tensor comparison has the regular scalar unit and the tensor constraints.
Source: Stacks 03EL, 07A4
(blueprint: def-sfb-quotient-section-tensor-data). -/
def UnitCondition (T : Scheme.{u}) (b : TensorIso a T) : Prop :=
  IsIso (scalarRegularUnit a T) ∧ IsIso (derivedScalarUnit a T) ∧
    TensorConstraintCondition (D a T)
      (Functor.uncurry.obj (CondensedRing.derivedTensor Λ T))
      (Functor.uncurry.obj (CondensedRing.derivedTensor Λ' T))
      (𝟙_ (DerivedCategory (Modules Λ T))) (𝟙_ (DerivedCategory (Modules Λ' T)))
      (fun M N P ↦ α_ M N P) (fun M ↦ λ_ M) (fun M ↦ ρ_ M)
      (fun M N P ↦ α_ M N P) (fun M ↦ λ_ M) (fun M ↦ ρ_ M)
      b.hom (derivedScalarUnit a T)

/-- The actual sheafified scalar generator in the chosen ordinary section model.
The left-scalar convention s tensor m denotes m tensor s in the statement.
Source: Stacks 03EL (blueprint: def-sfb-quotient-section-tensor-data). -/
def sectionScalarElement (T : Scheme.{u}) (c : ScalarSectionData a T)
    (M : modules Λ T) (W : T.ProEtᵒᵖ) (m : M.val.obj W)
    (s : (ring Λ' T).obj.obj W) : (c.model.E.obj M).val.obj W :=
  (eqToHom (c.model.obj_eq M).symm).val.app W
    ((toSheafify (Scheme.ProEt.topology T)
      (SheafOfModules.changeOfRingsPresheaf (sectionQuotient a T) M).presheaf).app W
        (s ⊗ₜ[(ring Λ T).obj.obj W, ((sectionQuotient a T).hom.app W).hom] m))

attribute [local irreducible] sectionScalarElement
  ModuleRingedComparison.qTensor

set_option backward.isDefEq.respectTransparency false in
/-- Section-side characterization of the canonical scalar tensor comparison.
The ordinary map is fixed on every sheafified pure scalar tensor. On every flat-term
K-flat pair its signed total, specified on each (i,j) summand, computes barB through
the model's own universal counit and the fixed section tensor localization maps.
Source: Stacks 03EK, 03EL and 07A4
(blueprint: def-sfb-quotient-section-tensor-data). -/
def SectionTensorNormalized (T : Scheme.{u}) (c : ScalarSectionData a T)
    (barB : tensor Λ T ⋙ c.model.T ≅
      (c.model.T.prod c.model.T) ⋙ tensor Λ' T) : Prop :=
  ∃ e : (Functor.postcompose₂.obj c.model.E).obj (curriedTensor (modules Λ T)) ⟶
      (((Functor.whiskeringLeft₂ _).obj c.model.E).obj c.model.E).obj
        (curriedTensor (modules Λ' T)),
    (∀ (M N : modules Λ T) (W : T.ProEtᵒᵖ) (m : M.val.obj W) (n : N.val.obj W)
      (s : (ring Λ' T).obj.obj W),
      (((e.app M).app N).val.app W)
          (sectionScalarElement a T c (M ⊗ N) W (sectionPureTensor Λ T M N W m n) s) =
        sectionPureTensor Λ' T (c.model.E.obj M) (c.model.E.obj N) W
          (sectionScalarElement a T c M W m 1) (sectionScalarElement a T c N W n s)) ∧
    ∀ P Q : CochainComplex (modules Λ T) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ T) P →
      CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ T) Q →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology T)
        (R := ring Λ T) (P.X i)) →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology T)
        (R := ring Λ T) (Q.X i)) →
      ∃ g : (c.model.E.mapHomologicalComplex (.up ℤ)).obj ((totalTensor Λ T).obj (P, Q)) ⟶
          (totalTensor Λ' T).obj
            ((c.model.E.mapHomologicalComplex (.up ℤ)).obj P,
              (c.model.E.mapHomologicalComplex (.up ℤ)).obj Q),
        (∀ (i j k : ℤ) (h : i + j = k),
          c.model.E.map
              (CochainComplex.ιMapBifunctor P Q (curriedTensor (modules Λ T)) i j k h) ≫
              g.f k =
            (e.app (P.X i)).app (Q.X j) ≫
              CochainComplex.ιMapBifunctor
                ((c.model.E.mapHomologicalComplex (.up ℤ)).obj P)
                ((c.model.E.mapHomologicalComplex (.up ℤ)).obj Q)
                (curriedTensor (modules Λ' T)) i j k h) ∧
        barB.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
            (tensor Λ' T).map (Prod.mkHom (c.model.ε.app P) (c.model.ε.app Q)) ≫
            (qTensor Λ' T).app
              ((c.model.E.mapHomologicalComplex (.up ℤ)).obj P,
                (c.model.E.mapHomologicalComplex (.up ℤ)).obj Q) =
          c.model.T.map ((qTensor Λ T).app (P, Q)) ≫
            c.model.ε.app ((totalTensor Λ T).obj (P, Q)) ≫ DerivedCategory.Q.map g

/-- The section image of the scalar tensorator, using the fixed tensor comparisons.
SectionTensorNormalized separately fixes its signed-total balancing normalization
on all section flat-term K-flat pairs.
Source: Stacks 03EL, 06YY and 07A4
(blueprint: def-sfb-quotient-section-tensor-data). -/
def TensorSectionCondition (T : Scheme.{u}) (c : ScalarSectionData a T)
    (b : TensorIso a T)
    (barB : tensor Λ T ⋙ c.model.T ≅
      (c.model.T.prod c.model.T) ⋙ tensor Λ' T) : Prop :=
  ∀ M N : DerivedCategory (Modules Λ T),
    (derivedFunctor Λ' T).map (b.hom.app (M, N)) ≫
        (tensorComparison Λ' T).hom.app ((D a T).obj M, (D a T).obj N) =
      c.derived.hom.app (M ⊗ N) ≫
        c.model.T.map ((tensorComparison Λ T).hom.app (M, N)) ≫
        barB.hom.app ((derivedFunctor Λ T).obj M, (derivedFunctor Λ T).obj N) ≫
        (tensor Λ' T).map (Prod.mkHom (c.derived.inv.app M) (c.derived.inv.app N))

/-- The actual pullback tensor transformation and both adjunction structure maps
become the specified ringed operations under the fixed geometric comparisons.
Source: Stacks 07A4, 07A6
(blueprint: def-sfb-quotient-section-tensor-data). -/
def GeometricCondition
    (B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj B] [IsCommMonObj B]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules B T)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  (∀ M N : DerivedCategory (internalModules B Y),
    HEq ((derivedFunctor B X).map
      (((CondensedRing.leftDerivedUpperStarTensor B f).app M).app N))
      ((derivedPullComparison B f).hom.app (M ⊗ N) ≫
        (derivedPullback B f).map ((tensorComparison B Y).hom.app (M, N)) ≫
        (tensorPullComparison B f).hom.app
          ((derivedFunctor B Y).obj M, (derivedFunctor B Y).obj N) ≫
        (tensor B X).map (Prod.mkHom
          ((derivedPullComparison B f).inv.app M) ((derivedPullComparison B f).inv.app N)) ≫
        (tensorComparison B X).inv.app
          ((internalDerivedPullback B f).obj M, (internalDerivedPullback B f).obj N))) ∧
  (∀ M : DerivedCategory (internalModules B Y),
    (derivedAdjunction B f).unit.app ((derivedFunctor B Y).obj M) =
      (derivedFunctor B Y).map ((normalizationInternalAdjunction B f).unit.app M) ≫
        (derivedPushComparison B f).hom.app ((internalDerivedPullback B f).obj M) ≫
        (derivedPushforward B f).map ((derivedPullComparison B f).hom.app M)) ∧
  (∀ N : DerivedCategory (internalModules B X),
    (derivedAdjunction B f).counit.app ((derivedFunctor B X).obj N) =
      (derivedPullback B f).map ((derivedPushComparison B f).inv.app N) ≫
        (derivedPullComparison B f).inv.app ((internalDerivedPushforward B f).obj N) ≫
        (derivedFunctor B X).map ((normalizationInternalAdjunction B f).counit.app N))

attribute [local semireducible] QuotientChange.L

/-- Section-side scalar/pullback normalization by the ordinary balancing comparison
and the actual section pullback localization maps and scalar-model counits.
The ordinary comparison is fixed through the ordinary section equivalences, independently
of lam or barLam: it carries f inverse (x tensor s) to f inverse x tensor f inverse s.
Source: Stacks 03EL, 0D6D and 0G7E
(blueprint: def-sfb-quotient-section-tensor-data). -/
def SectionPullNormalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (barLam : cY.model.T ⋙ derivedPullback Λ' f ≅
      derivedPullback Λ f ⋙ cX.model.T) : Prop :=
  ∃ e : cY.model.E ⋙ pullback Λ' f ≅ pullback Λ f ⋙ cX.model.E,
    (∀ M : Modules Λ Y,
      (equivalence Λ' X).functor.map ((CondensedRing.pullIso a f).inv.app M) ≫
          cX.ordinary.hom.app ((CondensedRing.upperStar Λ f).obj M) ≫
          cX.model.E.map ((pullComparison Λ f).hom.app M) =
        (pullComparison Λ' f).hom.app ((QuotientChange.extension a Y).obj M) ≫
          (pullback Λ' f).map (cY.ordinary.hom.app M) ≫
          e.hom.app ((equivalence Λ Y).functor.obj M)) ∧
    ∀ P : CochainComplex (modules Λ Y) ℤ,
      barLam.hom.app (DerivedCategory.Q.obj P) ≫
          cX.model.T.map ((pullback Λ f).mapDerivedCategoryFactors.hom.app P) ≫
          cX.model.ε.app (((pullback Λ f).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
            (Iso.refl (pullback Λ f ⋙ cX.model.E)) (.up ℤ)).hom.app P) =
        (derivedPullback Λ' f).map (cY.model.ε.app P) ≫
          (pullback Λ' f).mapDerivedCategoryFactors.hom.app
            ((cY.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P)

/-- Conjugation of the specified scalar/pullback comparison by the same scalar and
geometric realization maps. SectionPullNormalized separately fixes the ringed
comparison through the section pullback and scalar-model computation counits.
Source: Stacks 0D6D, 0G7E, 07A6
(blueprint: def-sfb-quotient-section-tensor-data). -/
def PullSectionCondition {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X)
    (barLam : cY.model.T ⋙ derivedPullback Λ' f ≅
      derivedPullback Λ f ⋙ cX.model.T) : Prop :=
  ∀ M : DerivedCategory (Modules Λ Y),
    (derivedFunctor Λ' X).map (lam.hom.app M) ≫
        cX.derived.hom.app ((L Λ f).obj M) ≫
        cX.model.T.map ((derivedPullComparison Λ f).hom.app M) =
      (derivedPullComparison Λ' f).hom.app ((D a Y).obj M) ≫
        (derivedPullback Λ' f).map (cY.derived.hom.app M) ≫
        barLam.hom.app ((derivedFunctor Λ Y).obj M)
```


## Users

The table includes every module reported by the downstream --uses scan for the
sixteen relocated definitions (including textual overapproximations). None needs adaptation:
the entire declaration block and its instance arguments are unchanged and reexported.
Direct importers are `QuotientPullbackTensorCoherence`,
`QuotientPullbackTensorFlatModel` and `QuotientTensorFlatModelMaps` (the last landed
after the delivery was made); their unchanged source files compile against the delivery
(reviewer check, 2026-10-27).

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.QuotientSectionTensorNormalization | T3 | Reexports the unchanged definitions. |
| Sheaf.Paper.IntegralQuotientProjectionComparison | unclaimed (local record) | Identical public names, data and statement; no adaptation. |
| Sheaf.Paper.LisseRationalRealization | unclaimed (local record) | Identical public names, data and statement; no adaptation. |
| Sheaf.Paper.LisseTensorNormalization | unclaimed (local record) | Identical public names, data and statement; no adaptation. |
| Sheaf.Paper.LisseTensorPullbackRealizationData | unclaimed (local record) | Identical public names, data and statement; no adaptation. |
| Sheaf.Paper.QuotientPullbackTensorCoherence | unclaimed (local record) | Identical public names, data and statement; no adaptation. |
| Sheaf.Paper.QuotientPullbackTensorFlatModel | T2 | Identical public names, data and statement; no adaptation. |
| Sheaf.Paper.QuotientTensorFlatModelMaps | unclaimed (local record) | Identical public names, data and statement; no adaptation. |
| Sheaf.Paper.QuotientTensorLeftFlatComputation | unclaimed (local record) | Identical public names, data and statement; no adaptation. |
| Sheaf.Paper.QuotientTensorRightFlatComputation | unclaimed (local record) | Identical public names, data and statement; no adaptation. |
| Sheaf.Paper.TensorHeartSpecialization | unclaimed (local record) | Identical public names, data and statement; no adaptation. |
| WeilConjectures | unclaimed (local record) | Identical public names, data and statement; no adaptation. |

## Status

landed 20261027T135442-L-3709173 2026-10-27 (merge of deliver/T3/Sheaf.Paper.QuotientSectionTensorNormalization)

## Consumer validation

The direct importers Sheaf.Paper.QuotientPullbackTensorFlatModel,
Sheaf.Paper.QuotientTensorFlatModelMaps and
Sheaf.Paper.QuotientPullbackTensorCoherence compile unchanged against the relocated
data and completed assembly. No adaptation is delivered, and their temporary
sandbox copies have been removed. The launcher's compile tool supplied the flat
model's unpublished dependencies through its private overlay.
