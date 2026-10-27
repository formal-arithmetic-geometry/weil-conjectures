# ClosedTestLocalizedModelCoherence localization API

## Reason

The independent normalization and geometric subcalculations need a common statement module,
so move the existing data, preserving all declaration names and signatures, into
Sheaf.Paper.ClosedTestLocalizedModelData. The original module publicly reexports it.
Factor the original localization formula through its universal derived-evaluation unit.
The proved localizationUnit_eq_original equation identifies the factored definition with
the old termwise formula. evaluationLocalization has the same body and its equality is reflexive.
No chosen witness is used as data. The comparison-unit refactoring is detailed below. The four
site-object abbreviations test, liftedTest, sourceTest and targetTest become ordinary
definitions, so elaboration can retain their names instead of eagerly expanding nested
fibre products. The return types of sourceTest and targetTest are written explicitly as
X.ProEt and XZ.ProEt; these are definitionally their old inferred MorphismProperty.Over
types. Their objects and every projection remain unchanged.

Evaluation ev and evaluationLocalization also become ordinary definitions with unchanged
bodies; sections remains an abbreviation. Evaluation has an explicit return functor type and a
proved ev_additive instance, so typeclass search need not unfold its construction.

The sourceUnit and targetUnit definitions are marked irreducible and defined as components
of explicit natural transformations, sourceTransformation and targetTransformation.
The public sourceUnit_eq_original and targetUnit_eq_original equations prove that they
equal their former composites. Their signatures stay fixed. Naturality is then a direct
application of NatTrans.naturality. No unspecified data replaces a comparison map.

The shared data and its proofs retain the two cached monoidal structures, while disabling
the cached abelian and additive instances. The canonical instances supply those proof
properties. No imported instance declaration or mathematical structure is modified.

## Old

```lean
def localizationUnit {X : Scheme.{u}} (W : X.ProEt) (I : CochainComplex (Modules Λ X) ℤ) :
    DerivedCategory.Q.obj ((sections Λ W).obj I) ⟶
      (sectionsOver Λ W.hom).obj (DerivedCategory.Q.obj I) :=
  DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
    (CondensedRing.closedFibreModuleSectionsRestriction Λ W.hom W (𝟙 W.left)
      (Category.id_comp W.hom)) (.up ℤ)).app I) ≫
    (condensedModuleSections Λ W.left).rightDerivedFunctorUnitQ
      (((CondensedRing.upperStar Λ W.hom).mapHomologicalComplex (.up ℤ)).obj I) ≫
    (condensedModuleSections Λ W.left).rightDerivedFunctor.map
      ((CondensedRing.upperStar Λ W.hom).mapDerivedCategoryFactors.inv.app I)

abbrev evaluationLocalization {Y : Scheme.{u}} (W : Y.ProEt) :=
  CondensedRing.closedFibreModuleDerivedRestriction Λ W.hom W (𝟙 W.left)
    (Category.id_comp W.hom)

```

## New

```lean
def localizationUnit {X : Scheme.{u}} (W : X.ProEt) (I : CochainComplex (Modules Λ X) ℤ) :
    DerivedCategory.Q.obj ((sections Λ W).obj I) ⟶
      (sectionsOver Λ W.hom).obj (DerivedCategory.Q.obj I) :=
  (localizationTransformation Λ W).app I

def evaluationLocalization {Y : Scheme.{u}} (W : Y.ProEt) :=
  CondensedRing.closedFibreModuleDerivedRestriction Λ W.hom W (𝟙 W.left)
    (Category.id_comp W.hom)

```

The evaluation declarations retain their construction bodies:

```lean
def ev {X : Scheme.{u}} (W : X.ProEt) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤ Ab.{u + 1} :=
  CondensedRing.closedFibreModuleEvaluation Λ X W

instance ev_additive {X : Scheme.{u}} (W : X.ProEt) : (ev Λ W).Additive :=
  inferInstanceAs (CondensedRing.closedFibreModuleEvaluation Λ X W).Additive

abbrev sections {X : Scheme.{u}} (W : X.ProEt) :=
  (ev Λ W).mapHomologicalComplex (.up ℤ)
```

The old ev was an abbreviation with the same inferred functor type; sections is unchanged.
The new evaluationLocalization also replaces only `abbrev` by `def` in the formula above.

The site-object definitions have the same construction bodies as the former abbreviations:

```lean
def test (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt) :=
  (Scheme.AffineProEt.toProEt _).obj V

def liftedTest (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt) :=
  (Scheme.AffineProEt.toProEt _).obj ((Scheme.AffineProEt.closedSiteLift A 𝔞).obj V)

def sourceTest (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt) : X.ProEt :=
  (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj (liftedTest A 𝔞 V)

def targetTest (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt) : XZ.ProEt :=
  (MorphismProperty.Over.pullback @WeaklyEtale ⊤ fZ).obj (test A 𝔞 V)
```

The old declarations use `abbrev` in place of `def`, and sourceTest and targetTest infer
the displayed return types. No mathematical data changes.

The old sourceUnit and targetUnit construction bodies are:

```lean
def sourceUnit (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt)
    (I : CochainComplex (Modules Λ X) ℤ) [I.IsKInjective] :
    DerivedCategory.Q.obj ((sections Λ (sourceTest A 𝔞 f V)).obj I) ⟶
      (CondensedRing.moduleObjectDerivedPushforward Λ f ⋙ pull Λ (closedMap A 𝔞) ⋙
        (ev Λ (test A 𝔞 V)).rightDerivedFunctor).obj (DerivedCategory.Q.obj I) :=
  DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (closedUnit Λ A 𝔞 V)
      (.up ℤ)).app (((CondensedRing.lowerStar Λ f).mapHomologicalComplex (.up ℤ)).obj I)) ≫
    (ev Λ (test A 𝔞 V)).rightDerivedFunctorUnitQ
      (((CondensedRing.upperStar Λ (closedMap A 𝔞)).mapHomologicalComplex (.up ℤ)).obj
        (((CondensedRing.lowerStar Λ f).mapHomologicalComplex (.up ℤ)).obj I)) ≫
    (ev Λ (test A 𝔞 V)).rightDerivedFunctor.map
      ((CondensedRing.upperStar Λ (closedMap A 𝔞)).mapDerivedCategoryFactors.inv.app
          (((CondensedRing.lowerStar Λ f).mapHomologicalComplex (.up ℤ)).obj I) ≫
        (pull Λ (closedMap A 𝔞)).map
          ((CondensedRing.lowerStar Λ f).rightDerivedFunctorObjQIso I).inv)

/-- The normalized map from the target section model to its derived expression.
The direct-image section formula is literal; the other factors are resolution units.
Source: Tags 070I and 0D6E
(blueprint: lem-sfb-closed-test-localized-model-coherence). -/
def targetUnit (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt)
    (I : CochainComplex (Modules Λ X) ℤ)
    (J : CochainComplex (Modules Λ XZ) ℤ) [J.IsKInjective]
    (j : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j] :
    DerivedCategory.Q.obj ((sections Λ (targetTest A 𝔞 fZ V)).obj J) ⟶
      (pull Λ h ⋙ CondensedRing.moduleObjectDerivedPushforward Λ fZ ⋙
        (ev Λ (test A 𝔞 V)).rightDerivedFunctor).obj (DerivedCategory.Q.obj I) :=
  (ev Λ (test A 𝔞 V)).rightDerivedFunctorUnitQ
      (((CondensedRing.lowerStar Λ fZ).mapHomologicalComplex (.up ℤ)).obj J) ≫
    (ev Λ (test A 𝔞 V)).rightDerivedFunctor.map
      (((CondensedRing.lowerStar Λ fZ).rightDerivedFunctorObjQIso J).inv ≫
        (CondensedRing.moduleObjectDerivedPushforward Λ fZ).map
          ((asIso (DerivedCategory.Q.map j)).inv ≫
            (CondensedRing.upperStar Λ h).mapDerivedCategoryFactors.inv.app I))

```


The new comparison units and the equations identifying them with these old bodies are
recorded verbatim in ClosedTestLocalizedModelData.lean. The new comparison construction definitions are:

```lean
def derivedUnit {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C] (F : C ⥤ D) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor where
  app := F.rightDerivedFunctorUnitQ
  naturality _X _Y a := F.rightDerivedFunctorUnitQ_naturality a

/-- The localization comparison as a natural transformation on complexes.
Source: universal derived units, Stacks 070Y and 0D6G
(blueprint: def-sfb-closed-test-localized-model-data). -/
def localizationTransformation {X : Scheme.{u}} (W : X.ProEt) :
    sections Λ W ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ sectionsOver Λ W.hom :=
  derivedUnit (ev Λ W) ≫ Functor.whiskerLeft DerivedCategory.Q
    (CondensedRing.closedFibreModuleDerivedRestriction Λ W.hom W (𝟙 W.left)
      (Category.id_comp W.hom))

/-- The localized comparison on a complex. The ordinary map is the adjunction unit
restricted to the identity of W; under the slice equivalence it is the degreewise identity.
The remaining factors are the universal derived unit and exact-pullback factorization.
Source: Tag 0D6G (blueprint: def-sfb-closed-test-localized-model-data). -/
def localizationUnit {X : Scheme.{u}} (W : X.ProEt) (I : CochainComplex (Modules Λ X) ℤ) :
    DerivedCategory.Q.obj ((sections Λ W).obj I) ⟶
      (sectionsOver Λ W.hom).obj (DerivedCategory.Q.obj I) :=
  (localizationTransformation Λ W).app I

variable (A : Type u) [CommRing A] (𝔞 : Ideal A)

/-- The test as an object of the full small pro-etale site.
Source: Tag 09BL (blueprint: def-sfb-closed-test-localized-model-data). -/
def test (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt) :=
  (Scheme.AffineProEt.toProEt _).obj V

/-- The specified lift as an object of the full small pro-etale site.
Source: Tag 09BL (blueprint: def-sfb-closed-test-localized-model-data). -/
def liftedTest (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt) :=
  (Scheme.AffineProEt.toProEt _).obj ((Scheme.AffineProEt.closedSiteLift A 𝔞).obj V)

/-- The geometric map from the closed test into the base change of its specified lift.
Source: Tag 09BK (blueprint: def-sfb-closed-test-localized-model-data). -/
def closedTestArrow (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt) :
    test A 𝔞 V ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (closedMap A 𝔞)).obj
      (liftedTest A 𝔞 V) :=
  MorphismProperty.Over.homMk
    (pullback.lift (Scheme.AffineProEt.closedSiteLiftInclusion A 𝔞 V) V.hom
      ((Scheme.AffineProEt.affine_closed_site_functor_properties A 𝔞).the project server.2.2.2 V).2.1.w)
    (pullback.lift_snd _ _ _)

/-- The actual closed unit, evaluated on the specified lift and test.
Source: Tag 09BL (blueprint: def-sfb-closed-test-localized-model-data). -/
def closedUnit (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt) :=
  unitAt Λ (closedMap A 𝔞) (liftedTest A 𝔞 V) (test A 𝔞 V) (closedTestArrow A 𝔞 V)

variable {X XZ : Scheme.{u}} (f : X ⟶ Spec (.of A))
  (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ 𝔞)))
  (w : IsPullback h fZ f (closedMap A 𝔞))

/-- The lifted test fibre as a site object of X.
Source: Tag 0D6G (blueprint: def-sfb-closed-test-localized-model-data). -/
def sourceTest (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt) : X.ProEt :=
  (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj (liftedTest A 𝔞 V)

/-- The closed test fibre as a site object of X_Z.
Source: Tag 0D6G (blueprint: def-sfb-closed-test-localized-model-data). -/
def targetTest (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt) : XZ.ProEt :=
  (MorphismProperty.Over.pullback @WeaklyEtale ⊤ fZ).obj (test A 𝔞 V)

/-- The canonical fibre-product map used to evaluate the inverse-image unit.
Source: Tags 09BK and 0D6G
(blueprint: def-sfb-closed-test-localized-model-data). -/
def fibreTestArrow (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt) :
    targetTest A 𝔞 fZ V ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ h).obj
      (sourceTest A 𝔞 f V) :=
  MorphismProperty.Over.homMk
    (pullback.lift
      (pullback.lift
        (pullback.fst V.hom fZ ≫ Scheme.AffineProEt.closedSiteLiftInclusion A 𝔞 V)
        (pullback.snd V.hom fZ ≫ h)
        (by
          change (pullback.fst V.hom fZ ≫
            Scheme.AffineProEt.closedSiteLiftInclusion A 𝔞 V) ≫
              ((Scheme.AffineProEt.closedSiteLift A 𝔞).obj V).hom =
            (pullback.snd V.hom fZ ≫ h) ≫ f
          rw [Category.assoc,
            ((Scheme.AffineProEt.affine_closed_site_functor_properties A 𝔞).the project server.2.2.2
              V).2.1.w, ← Category.assoc, pullback.condition, Category.assoc, ← w.w]
          simp only [Category.assoc]))
      (pullback.snd V.hom fZ) (pullback.lift_snd _ _ _))
    (pullback.lift_snd _ _ _)

/-- The chain arrow j(T_0) after the actual unit section, localized to D(Ab).
Source: Tag 070I, the arrow r in the statement
(blueprint: def-sfb-closed-test-localized-model-data). -/
def modelArrow (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt)
    (I : CochainComplex (Modules Λ X) ℤ) (J : CochainComplex (Modules Λ XZ) ℤ)
    (j : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I ⟶ J) :
    DerivedCategory.Q.obj ((sections Λ (sourceTest A 𝔞 f V)).obj I) ⟶
      DerivedCategory.Q.obj ((sections Λ (targetTest A 𝔞 fZ V)).obj J) :=
  DerivedCategory.Q.map
    ((NatTrans.mapHomologicalComplex
      (unitAt Λ h (sourceTest A 𝔞 f V) (targetTest A 𝔞 fZ V)
        (fibreTestArrow A 𝔞 f h fZ w V)) (.up ℤ)).app I ≫
      (sections Λ (targetTest A 𝔞 fZ V)).map j)

/-- The complete source comparison, natural on complexes.
Source: universal derived units, Stacks 070Y
(blueprint: def-sfb-closed-test-localized-model-data). -/
@[irreducible] def sourceTransformation (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt) :
    sections Λ (sourceTest A 𝔞 f V) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ CondensedRing.moduleObjectDerivedPushforward Λ f ⋙
        pull Λ (closedMap A 𝔞) ⋙ (ev Λ (test A 𝔞 V)).rightDerivedFunctor :=
  Functor.whiskerLeft ((CondensedRing.lowerStar Λ f).mapHomologicalComplex (.up ℤ))
    (Functor.whiskerRight
        (NatTrans.mapHomologicalComplex (closedUnit Λ A 𝔞 V) (.up ℤ)) DerivedCategory.Q ≫
      Functor.whiskerLeft
        ((CondensedRing.upperStar Λ (closedMap A 𝔞)).mapHomologicalComplex (.up ℤ))
        (derivedUnit (ev Λ (test A 𝔞 V))) ≫
      Functor.whiskerRight
        (CondensedRing.upperStar Λ (closedMap A 𝔞)).mapDerivedCategoryFactors.inv
        (ev Λ (test A 𝔞 V)).rightDerivedFunctor) ≫
    Functor.whiskerRight (derivedUnit (CondensedRing.lowerStar Λ f))
      (pull Λ (closedMap A 𝔞) ⋙ (ev Λ (test A 𝔞 V)).rightDerivedFunctor)

/-- The complete target comparison, natural on complexes.
Source: universal derived units, Stacks 070Y
(blueprint: def-sfb-closed-test-localized-model-data). -/
@[irreducible] def targetTransformation (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt) :
    sections Λ (targetTest A 𝔞 fZ V) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ CondensedRing.moduleObjectDerivedPushforward Λ fZ ⋙
        (ev Λ (test A 𝔞 V)).rightDerivedFunctor :=
  Functor.whiskerLeft ((CondensedRing.lowerStar Λ fZ).mapHomologicalComplex (.up ℤ))
      (derivedUnit (ev Λ (test A 𝔞 V))) ≫
    Functor.whiskerRight (derivedUnit (CondensedRing.lowerStar Λ fZ))
      (ev Λ (test A 𝔞 V)).rightDerivedFunctor

/-- The normalized map from the source model to its derived section expression.
Its inverse is exactly the requested source comparison; the closed unit is never replaced
by an unspecified isomorphism.
Source: Tags 070I and 09BL
(blueprint: def-sfb-closed-test-localized-model-data). -/
@[irreducible] def sourceUnit (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt)
    (I : CochainComplex (Modules Λ X) ℤ) [I.IsKInjective] :
    DerivedCategory.Q.obj ((sections Λ (sourceTest A 𝔞 f V)).obj I) ⟶
      (CondensedRing.moduleObjectDerivedPushforward Λ f ⋙ pull Λ (closedMap A 𝔞) ⋙
        (ev Λ (test A 𝔞 V)).rightDerivedFunctor).obj (DerivedCategory.Q.obj I) :=
  (sourceTransformation Λ A 𝔞 f V).app I

/-- The transformation component equals the original sourceUnit composite.
Source: universal derived units, Stacks 070Y
(blueprint: def-sfb-closed-test-localized-model-data). -/
theorem sourceUnit_eq_original (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt)
    (I : CochainComplex (Modules Λ X) ℤ) [I.IsKInjective] :
    sourceUnit Λ A 𝔞 f V I =
  DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (closedUnit Λ A 𝔞 V)
      (.up ℤ)).app (((CondensedRing.lowerStar Λ f).mapHomologicalComplex (.up ℤ)).obj I)) ≫
    (ev Λ (test A 𝔞 V)).rightDerivedFunctorUnitQ
      (((CondensedRing.upperStar Λ (closedMap A 𝔞)).mapHomologicalComplex (.up ℤ)).obj
        (((CondensedRing.lowerStar Λ f).mapHomologicalComplex (.up ℤ)).obj I)) ≫
    (ev Λ (test A 𝔞 V)).rightDerivedFunctor.map
      ((CondensedRing.upperStar Λ (closedMap A 𝔞)).mapDerivedCategoryFactors.inv.app
          (((CondensedRing.lowerStar Λ f).mapHomologicalComplex (.up ℤ)).obj I) ≫
        (pull Λ (closedMap A 𝔞)).map
          ((CondensedRing.lowerStar Λ f).rightDerivedFunctorObjQIso I).inv) := by
  simp only [sourceUnit, sourceTransformation, derivedUnit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.map_comp, Functor.rightDerivedFunctorUnitQ_eq, Category.assoc]

/-- The normalized map from the target section model to its derived expression.
The direct-image section formula is literal; the other factors are resolution units.
Source: Tags 070I and 0D6E
(blueprint: def-sfb-closed-test-localized-model-data). -/
@[irreducible] def targetUnit (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt)
    (I : CochainComplex (Modules Λ X) ℤ)
    (J : CochainComplex (Modules Λ XZ) ℤ) [J.IsKInjective]
    (j : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j] :
    DerivedCategory.Q.obj ((sections Λ (targetTest A 𝔞 fZ V)).obj J) ⟶
      (pull Λ h ⋙ CondensedRing.moduleObjectDerivedPushforward Λ fZ ⋙
        (ev Λ (test A 𝔞 V)).rightDerivedFunctor).obj (DerivedCategory.Q.obj I) :=
  (targetTransformation Λ A 𝔞 fZ V).app J ≫
    (ev Λ (test A 𝔞 V)).rightDerivedFunctor.map
      ((CondensedRing.moduleObjectDerivedPushforward Λ fZ).map
        ((asIso (DerivedCategory.Q.map j)).inv ≫
          (CondensedRing.upperStar Λ h).mapDerivedCategoryFactors.inv.app I))

/-- The transformation component equals the original targetUnit composite.
Source: universal derived units, Stacks 070Y
(blueprint: def-sfb-closed-test-localized-model-data). -/
theorem targetUnit_eq_original (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt)
    (I : CochainComplex (Modules Λ X) ℤ)
    (J : CochainComplex (Modules Λ XZ) ℤ) [J.IsKInjective]
    (j : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j] :
    targetUnit Λ A 𝔞 h fZ V I J j =
  (ev Λ (test A 𝔞 V)).rightDerivedFunctorUnitQ
      (((CondensedRing.lowerStar Λ fZ).mapHomologicalComplex (.up ℤ)).obj J) ≫
    (ev Λ (test A 𝔞 V)).rightDerivedFunctor.map
      (((CondensedRing.lowerStar Λ fZ).rightDerivedFunctorObjQIso J).inv ≫
        (CondensedRing.moduleObjectDerivedPushforward Λ fZ).map
          ((asIso (DerivedCategory.Q.map j)).inv ≫
            (CondensedRing.upperStar Λ h).mapDerivedCategoryFactors.inv.app I)) := by
  simp only [targetUnit, targetTransformation, derivedUnit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Functor.rightDerivedFunctorUnitQ_eq, Category.assoc]

```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ClosedTestLocalizedModelCoherence | E2 | Definitions move to the common data module and are publicly reexported; proof uses their normalization API. |
| Sheaf.Paper.ClosedTestLocalizedModelData | new, E2 | Owns the same names, with the equivalent factored localization body and proved equations. |
| Sheaf.Paper.ClosedTestComparisonTestNaturality | new, E2 | Imports the common data. |
| Sheaf.Paper.ClosedTestLocalizedRestrictionNormalization | new, E2 | Imports the common data. |
| Sheaf.Paper.ClosedTestDerivedComparisonNormalization | new, E2 | Imports the common data. |
| Sheaf.Paper.ClosedTestGeometricSectionCoherence | new, E2 | Imports the common data. |

The downstream tool reports zero current importers of the item. Searches for localizationUnit
and evaluationLocalization find only the item. DAG parents still require the item and remain
unchanged. Public import visibility is preserved transitively. The target definitions do not
change meaning; the normalization equations explicitly witness equality.

## Status

landed 20261023T230716-L-3468184 2026-10-23 (merge of deliver/E2/Sheaf.Paper.ClosedTestLocalizedModelCoherence)
