# AlgebraicGeometry.supportBoundaryNormalization and the support comparison maps

## Reason

Move the eight existing public definitions from SupportComparisonBoundary to
SupportComparisonBoundaryMaps, so the normalized-site and cochain-model proofs
can import the definitions without importing the theorem they are used to prove.
SupportComparisonBoundary publicly imports Maps, preserving every name, type,
visibility and body. This is a source organization change, not a mathematical
change to any definition. No downstream statement changes, and no target
statement or meaning changes. The obsolete pro-etale finite-coefficient
lower-shriek import is replaced by its current source-library module,
WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Defs.
No module held by another group is edited. The original consumer files are
checked against the relocated public interface.

## Old

The following definitions lived in lean/Sheaf/AlgebraicGeometry/SupportComparisonBoundary.lean.

```lean
/-- The adjunction-unit comparison on sections over any etale object of `T`.
Source: blueprint comparison-global-cohomology and comparison-pullback clauses;
(blueprint: lem-pur-support-comparison-boundary).
Proof: evaluate the actual comparison adjunction unit at the chosen etale object;
naturality is the componentwise unit naturality equation. -/
noncomputable def finiteComparisonSectionUnit (T : Scheme.{u}) (A : Type (u + 1)) [Ring A]
    (V : Scheme.Etale T) :
    (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
      (evaluation _ _).obj (op V)) ⋙ 𝟭 (ModuleCat.{u + 1} A) ⟶
      comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙
        (sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
          (evaluation _ _).obj (op ((Scheme.toProEt T).obj V))) where
  app F := ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app F).hom.app
    (op V)
  naturality F G f := by
    exact congrArg (fun t ↦ t.hom.app (op V))
      ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.naturality f)

/-- The canonical derived comparison on sections over an arbitrary etale object.
At the terminal object this is the same unit-normalized map as
`finiteComparisonGlobalSections`; at an open complement it is the comparison map
used in the boundary ladder.
Source: blueprint comparison-global-cohomology and comparison-pullback clauses;
(blueprint: lem-pur-support-comparison-boundary).
Proof: apply right-derived-plus base change to `finiteComparisonSectionUnit`; the
comparison pullback coherence identifies its pro-etale target with the restriction
of the comparison on the open complement. -/
noncomputable def finiteComparisonSection (T : Scheme.{u}) (A : Type (u + 1)) [Ring A]
    (V : Scheme.Etale T) :
    (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
      (evaluation _ _).obj (op V)).rightDerivedFunctorPlus ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus ⋙
        (sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
          (evaluation _ _).obj (op ((Scheme.toProEt T).obj V))).rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso
      (ModuleCat.{u + 1} A))).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      (G := sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
        (evaluation _ _).obj (op V))
      (G' := sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
        (evaluation _ _).obj (op ((Scheme.toProEt T).obj V)))
      (β := comparisonUpperStar (ModuleCat.{u + 1} A) T)
      (γ := 𝟭 (ModuleCat.{u + 1} A)) (finiteComparisonSectionUnit T A V)

/-- The canonical comparison on supported hypercohomology in each integer degree.
Source: blueprint comparison map clause
(blueprint: lem-pur-support-comparison-boundary).
Proof: whisker the unit-normalized derived support comparison by the canonical
integer homology functor. -/
noncomputable def supportComparisonHypercohomology (A : Type (u + 1)) [CommRing A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] (q : ℤ) :
    Sheaf.supportHypercohomologyFunctor T.smallEtaleTopology
        (ModuleCat.{u + 1} A) (Etale.supportRestrictionArrow i) q ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus ⋙
        Sheaf.supportHypercohomologyFunctor (Scheme.ProEt.topology T)
          (ModuleCat.{u + 1} A) (ProEtale.supportRestrictionArrow i) q :=
  by
    simpa [Sheaf.supportHypercohomologyFunctor, etaleSupportKernel, supportSections] using
      (Functor.whiskerRight (supportComparison A i)
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q) ≫
        (Functor.associator
          (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus
          (supportSections i A).rightDerivedFunctorPlus
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q)).hom)

/-- The canonical degreewise comparison on sections over an etale object.
Source: blueprint comparison-map clauses
(blueprint: lem-pur-support-comparison-boundary).
Proof: whisker `finiteComparisonSection` by integer homology and reassociate the
composite functors.  For the terminal object this is the unit-normalized global
comparison of `finiteComparisonGlobalSections`; for an open object the pullback
coherence identifies the target with the restriction comparison. -/
noncomputable def finiteComparisonSectionHypercohomology
    (T : Scheme.{u}) (A : Type (u + 1)) [Ring A] (V : Scheme.Etale T) (q : ℤ) :
    Sheaf.sectionHypercohomologyFunctor T.smallEtaleTopology
        (ModuleCat.{u + 1} A) V q ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus ⋙
        Sheaf.sectionHypercohomologyFunctor (Scheme.ProEt.topology T)
          (ModuleCat.{u + 1} A) ((Scheme.toProEt T).obj V) q :=
  by
    simpa [Sheaf.sectionHypercohomologyFunctor] using
      (Functor.whiskerRight (finiteComparisonSection T A V)
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q) ≫
        (Functor.associator
          (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus
          ((sheafToPresheaf (Scheme.ProEt.topology T)
            (ModuleCat.{u + 1} A) ⋙
            (evaluation _ _).obj (op ((Scheme.toProEt T).obj V))).rightDerivedFunctorPlus)
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q)).hom)


/-- The degreewise map of the recorded, unit-induced global comparison.
Source: global comparison clause of the blueprint
(blueprint: lem-pur-support-comparison-boundary). -/
noncomputable def finiteComparisonGlobalHypercohomology
    (T : Scheme.{u}) (A : Type (u + 1)) [Ring A] (q : ℤ) :
    Sheaf.sectionHypercohomologyFunctor T.smallEtaleTopology
        (ModuleCat.{u + 1} A) (Scheme.Etale.mk (𝟙 T)) q ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus ⋙
        Sheaf.sectionHypercohomologyFunctor (Scheme.ProEt.topology T)
          (ModuleCat.{u + 1} A) (Scheme.ProEt.mk (𝟙 T)) q :=
  Functor.whiskerRight
    ((Functor.rightUnitor _).inv ≫
      (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso
        (ModuleCat.{u + 1} A))).inv ≫ finiteComparisonGlobalSections T A)
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q) ≫
      (Functor.associator _ _ _).hom

/-- The coefficient identification on the open complement, using exactly the
unit-normalized isomorphism whose coherence is
`supportSiteComparison_pullback_coherent`, transported to the actual restriction functors.
Source: comparison-pullback clause of the blueprint
(blueprint: lem-pur-support-comparison-boundary). -/
noncomputable def supportBoundaryOpenCoefficientIso
    (A : Type (u + 1)) [CommRing A] {U T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] :
    Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j ⋙
        comparisonUpperStar (ModuleCat.{u + 1} A) U ≅
      comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙
        openImmersionRestriction (ModuleCat.{u + 1} A) j :=
  Functor.isoWhiskerRight
    (Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).symm
    (comparisonUpperStar (ModuleCat.{u + 1} A) U) ≪≫
  supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) j ≪≫
  Functor.isoWhiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} A) T)
    (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j)

/-- Unit normalization on the open, ensuring that evaluation of the unit on `T`
over the open object is the unit on the restricted sheaf on `U`, with the specified
coefficient identification. Deriving evaluation of this equation gives the open
comparison `finiteComparisonSectionHypercohomology` in the localization ladder.
Source: comparison-pullback and open-global-comparison clauses of the blueprint
(blueprint: lem-pur-support-comparison-boundary). -/
def SupportBoundaryOpenUnitNormalized
    (A : Type (u + 1)) [CommRing A] {U T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] : Prop :=
  ∀ F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
    (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).map
        ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app F) =
      (comparisonAdjunction (ModuleCat.{u + 1} A) U).unit.app
          ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj F) ≫
        (comparisonLowerStar (ModuleCat.{u + 1} A) U).map
          ((supportBoundaryOpenCoefficientIso A j).hom.app F)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

/-- A support boundary is the snake boundary on each injective section complex,
transported through the canonical right-derived comparison maps.
Source: Stacks Project Tag 09XP and (blueprint: lem-pur-support-comparison-boundary).
Proof: for an injective complex, the kernel-inclusion and restriction maps form a
short exact complex; its `ShortExact.δ` is the snake boundary. -/
def supportBoundaryNormalization {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (A : Type (u + 1)) [CommRing A]
    {V W : C} (j : W ⟶ V)
    (δ : Sheaf.SupportSequenceBoundary J (ModuleCat.{u + 1} A) j ⊤) : Prop :=
  ∀ (I : CochainComplex.Plus (Sheaf J (ModuleCat.{u + 1} A)))
    [∀ r : ℤ, Injective (I.obj.X r)],
    ∃ (w :
        (NatTrans.mapHomologicalComplex
          (Sheaf.supportedSectionsInclusion J (ModuleCat.{u + 1} A) j)
          (ComplexShape.up ℤ)).app I.obj ≫
        (NatTrans.mapHomologicalComplex
          ((sheafSections J (ModuleCat.{u + 1} A)).map j.op)
          (ComplexShape.up ℤ)).app I.obj = 0)
      (hS : (ShortComplex.mk _ _ w).ShortExact),
      ∀ q : ℤ,
        Sheaf.supportSequenceModelBoundary J (ModuleCat.{u + 1} A) j ⊤ δ I
          ⟨DerivedCategory.Plus.Q.obj I, trivial⟩ (Iso.refl _) q =
          hS.δ q (q + 1) rfl

```

## New

The same source declarations now live in
lean/Sheaf/AlgebraicGeometry/SupportComparisonBoundaryMaps.lean.
Their old module contains `public import Sheaf.AlgebraicGeometry.SupportComparisonBoundaryMaps`.

```lean
/-- The adjunction-unit comparison on sections over any etale object of `T`.
Source: blueprint comparison-global-cohomology and comparison-pullback clauses;
(blueprint: def-pur-support-comparison-boundary-maps).
Proof: evaluate the actual comparison adjunction unit at the chosen etale object;
naturality is the componentwise unit naturality equation. -/
noncomputable def finiteComparisonSectionUnit (T : Scheme.{u}) (A : Type (u + 1)) [Ring A]
    (V : Scheme.Etale T) :
    (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
      (evaluation _ _).obj (op V)) ⋙ 𝟭 (ModuleCat.{u + 1} A) ⟶
      comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙
        (sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
          (evaluation _ _).obj (op ((Scheme.toProEt T).obj V))) where
  app F := ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app F).hom.app
    (op V)
  naturality F G f := by
    exact congrArg (fun t ↦ t.hom.app (op V))
      ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.naturality f)

/-- The canonical derived comparison on sections over an arbitrary etale object.
At the terminal object this is the same unit-normalized map as
`finiteComparisonGlobalSections`; at an open complement it is the comparison map
used in the boundary ladder.
Source: blueprint comparison-global-cohomology and comparison-pullback clauses;
(blueprint: def-pur-support-comparison-boundary-maps).
Proof: apply right-derived-plus base change to `finiteComparisonSectionUnit`; the
comparison pullback coherence identifies its pro-etale target with the restriction
of the comparison on the open complement. -/
noncomputable def finiteComparisonSection (T : Scheme.{u}) (A : Type (u + 1)) [Ring A]
    (V : Scheme.Etale T) :
    (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
      (evaluation _ _).obj (op V)).rightDerivedFunctorPlus ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus ⋙
        (sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
          (evaluation _ _).obj (op ((Scheme.toProEt T).obj V))).rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso
      (ModuleCat.{u + 1} A))).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      (G := sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
        (evaluation _ _).obj (op V))
      (G' := sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
        (evaluation _ _).obj (op ((Scheme.toProEt T).obj V)))
      (β := comparisonUpperStar (ModuleCat.{u + 1} A) T)
      (γ := 𝟭 (ModuleCat.{u + 1} A)) (finiteComparisonSectionUnit T A V)

/-- The canonical comparison on supported hypercohomology in each integer degree.
Source: blueprint comparison map clause
(blueprint: def-pur-support-comparison-boundary-maps).
Proof: whisker the unit-normalized derived support comparison by the canonical
integer homology functor. -/
noncomputable def supportComparisonHypercohomology (A : Type (u + 1)) [CommRing A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] (q : ℤ) :
    Sheaf.supportHypercohomologyFunctor T.smallEtaleTopology
        (ModuleCat.{u + 1} A) (Etale.supportRestrictionArrow i) q ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus ⋙
        Sheaf.supportHypercohomologyFunctor (Scheme.ProEt.topology T)
          (ModuleCat.{u + 1} A) (ProEtale.supportRestrictionArrow i) q :=
  by
    simpa [Sheaf.supportHypercohomologyFunctor, etaleSupportKernel, supportSections] using
      (Functor.whiskerRight (supportComparison A i)
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q) ≫
        (Functor.associator
          (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus
          (supportSections i A).rightDerivedFunctorPlus
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q)).hom)

/-- The canonical degreewise comparison on sections over an etale object.
Source: blueprint comparison-map clauses
(blueprint: def-pur-support-comparison-boundary-maps).
Proof: whisker `finiteComparisonSection` by integer homology and reassociate the
composite functors.  For the terminal object this is the unit-normalized global
comparison of `finiteComparisonGlobalSections`; for an open object the pullback
coherence identifies the target with the restriction comparison. -/
noncomputable def finiteComparisonSectionHypercohomology
    (T : Scheme.{u}) (A : Type (u + 1)) [Ring A] (V : Scheme.Etale T) (q : ℤ) :
    Sheaf.sectionHypercohomologyFunctor T.smallEtaleTopology
        (ModuleCat.{u + 1} A) V q ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus ⋙
        Sheaf.sectionHypercohomologyFunctor (Scheme.ProEt.topology T)
          (ModuleCat.{u + 1} A) ((Scheme.toProEt T).obj V) q :=
  by
    simpa [Sheaf.sectionHypercohomologyFunctor] using
      (Functor.whiskerRight (finiteComparisonSection T A V)
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q) ≫
        (Functor.associator
          (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus
          ((sheafToPresheaf (Scheme.ProEt.topology T)
            (ModuleCat.{u + 1} A) ⋙
            (evaluation _ _).obj (op ((Scheme.toProEt T).obj V))).rightDerivedFunctorPlus)
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q)).hom)


/-- The degreewise map of the recorded, unit-induced global comparison.
Source: global comparison clause of the blueprint
(blueprint: def-pur-support-comparison-boundary-maps). -/
noncomputable def finiteComparisonGlobalHypercohomology
    (T : Scheme.{u}) (A : Type (u + 1)) [Ring A] (q : ℤ) :
    Sheaf.sectionHypercohomologyFunctor T.smallEtaleTopology
        (ModuleCat.{u + 1} A) (Scheme.Etale.mk (𝟙 T)) q ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus ⋙
        Sheaf.sectionHypercohomologyFunctor (Scheme.ProEt.topology T)
          (ModuleCat.{u + 1} A) (Scheme.ProEt.mk (𝟙 T)) q :=
  Functor.whiskerRight
    ((Functor.rightUnitor _).inv ≫
      (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso
        (ModuleCat.{u + 1} A))).inv ≫ finiteComparisonGlobalSections T A)
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q) ≫
      (Functor.associator _ _ _).hom

/-- The coefficient identification on the open complement, using exactly the
unit-normalized isomorphism whose coherence is
`supportSiteComparison_pullback_coherent`, transported to the actual restriction functors.
Source: comparison-pullback clause of the blueprint
(blueprint: def-pur-support-comparison-boundary-maps). -/
noncomputable def supportBoundaryOpenCoefficientIso
    (A : Type (u + 1)) [CommRing A] {U T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] :
    Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j ⋙
        comparisonUpperStar (ModuleCat.{u + 1} A) U ≅
      comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙
        openImmersionRestriction (ModuleCat.{u + 1} A) j :=
  Functor.isoWhiskerRight
    (Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).symm
    (comparisonUpperStar (ModuleCat.{u + 1} A) U) ≪≫
  supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) j ≪≫
  Functor.isoWhiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} A) T)
    (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j)

/-- Unit normalization on the open, ensuring that evaluation of the unit on `T`
over the open object is the unit on the restricted sheaf on `U`, with the specified
coefficient identification. Deriving evaluation of this equation gives the open
comparison `finiteComparisonSectionHypercohomology` in the localization ladder.
Source: comparison-pullback and open-global-comparison clauses of the blueprint
(blueprint: def-pur-support-comparison-boundary-maps). -/
def SupportBoundaryOpenUnitNormalized
    (A : Type (u + 1)) [CommRing A] {U T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] : Prop :=
  ∀ F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
    (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).map
        ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app F) =
      (comparisonAdjunction (ModuleCat.{u + 1} A) U).unit.app
          ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj F) ≫
        (comparisonLowerStar (ModuleCat.{u + 1} A) U).map
          ((supportBoundaryOpenCoefficientIso A j).hom.app F)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

/-- A support boundary is the snake boundary on each injective section complex,
transported through the canonical right-derived comparison maps.
Source: Stacks Project Tag 09XP and (blueprint: def-pur-support-comparison-boundary-maps).
Proof: for an injective complex, the kernel-inclusion and restriction maps form a
short exact complex; its `ShortExact.δ` is the snake boundary. -/
def supportBoundaryNormalization {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (A : Type (u + 1)) [CommRing A]
    {V W : C} (j : W ⟶ V)
    (δ : Sheaf.SupportSequenceBoundary J (ModuleCat.{u + 1} A) j ⊤) : Prop :=
  ∀ (I : CochainComplex.Plus (Sheaf J (ModuleCat.{u + 1} A)))
    [∀ r : ℤ, Injective (I.obj.X r)],
    ∃ (w :
        (NatTrans.mapHomologicalComplex
          (Sheaf.supportedSectionsInclusion J (ModuleCat.{u + 1} A) j)
          (ComplexShape.up ℤ)).app I.obj ≫
        (NatTrans.mapHomologicalComplex
          ((sheafSections J (ModuleCat.{u + 1} A)).map j.op)
          (ComplexShape.up ℤ)).app I.obj = 0)
      (hS : (ShortComplex.mk _ _ w).ShortExact),
      ∀ q : ℤ,
        Sheaf.supportSequenceModelBoundary J (ModuleCat.{u + 1} A) j ⊤ δ I
          ⟨DerivedCategory.Plus.Q.obj I, trivial⟩ (Iso.refl _) q =
          hS.δ q (q + 1) rfl

end AlgebraicGeometry
```

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.SupportComparisonBoundary --uses
finiteComparisonSectionUnit finiteComparisonSection supportComparisonHypercohomology
finiteComparisonSectionHypercohomology finiteComparisonGlobalHypercohomology
supportBoundaryOpenCoefficientIso SupportBoundaryOpenUnitNormalized supportBoundaryNormalization`
was run against the current sources. The only direct declaration user outside the
item is Sheaf.Paper.PurityAffineLineOrientation (supportBoundaryNormalization).
The table also lists every transitive downstream module reported by the command.
Holders are the current claim records when this packet was prepared; no adaptation
is required because the declarations and their public reexport are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | A3 | Eight definitions moved verbatim to public Maps import; theorem signature unchanged and proof supplied. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | K4 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.AdicPurityFiniteTensor | W8 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.AdicPurityRootComparisons | X5 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.AdicPuritySourceReduction | X6 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.AdicPurityTwistReduction | X8 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.CartierClassAgreement | U5 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.ChernFlagFormula | G4 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | P2 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.FiniteReductionAffineOrientation | T6 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.FiniteReductionChartCalculus | S7 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.FiniteReductionComparisons | T7 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.FiniteReductionRootCharts | D8 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | V6 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.LocalizedTopChern | E5 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.PurAdicReconstruction | H8 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.PurityAffineLineOrientation | J6 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | E2 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | R3 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.PurityDiagonalDualizingObject | G3 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.PurityDivisorClass | J7 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.PurityDncComparisons | G3 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.PurityFrameIndependence | A4 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.PurityRankOneLocalCalculation | F2 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | K6 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.RegularImmersionClassData | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.RegularImmersionPurity | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.RelativeSupportBottomDescent | A3 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.SmoothPurityMap | R2 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.SmoothTrace | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.WeilFourierInversion | J6 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.WeilOne | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | K9 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6 | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| TargetsCheck | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.Statement | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Unchanged signature and body; public import reexports the relocated definitions. |

## Status

landed 20261019T192642-L-1850879 2026-10-19 (merge of deliver/A3/Sheaf.AlgebraicGeometry.SupportComparisonBoundary)
