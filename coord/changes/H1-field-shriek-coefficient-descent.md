# Field shriek composition normalization and coefficient descent

## Reason

The proper/open arrows and their normalization predicate were declared in the same
module as the integral and field existence theorems. The coefficient compatibility
step must refer to that predicate, while the Qbar theorem must import this step.
Move those existing definitions into a shared module, preserving their names,
signatures, attributes and bodies verbatim, and publicly re-export them from the
original module. This is interface organization for an acyclic proof dependency,
not a split to avoid compilation limits. No compilation timeout occurred.

A separate scalar-square theorem assumes supplied integral compositors satisfying
the original normalization and supplied rationalizations. It asserts one equation
at a coefficient inclusion. The Qbar theorem constructs and descends the compatible
finite family, proves invertibility by finite-stage isomorphisms, and proves
uniqueness by extensionality. The existing integral theorem remains open.

## Old

In `Sheaf.Paper.FieldShriekCompositionQcqs`, between its private rationalization
helper and `section Field`:

```lean
section Completed
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The pullback square comparison made from the canonical completed compositors.
Source: Stacks 0F7J, proper/open square
(blueprint: lem-zl-field-shriek-composition-qcqs). -/
def sfCompositionPullSquare {V T Y S : Scheme.{u}}
    (b : V ⟶ T) (r : V ⟶ Y) (p : T ⟶ S) (i : Y ⟶ S)
    (w : b ≫ p = r ≫ i) :
    pull (completed l E) i ⋙ pull (completed l E) r ≅
      pull (completed l E) p ⋙ pull (completed l E) b :=
  (geometricPullComposition (completed l E) r i (completedPull_comp l E r i)).symm ≪≫
    eqToIso (congrArg (fun h ↦ pull (completed l E) h) w.symm) ≪≫
    geometricPullComposition (completed l E) b p (completedPull_comp l E b p)

/-- The open restriction comparison: geometric exchange, then the inverse open unit.
The unit proof is supplied by the statement, rather than assumed as a geometric
hypothesis. Source: Stacks 0F7J, proper/open comparison
(blueprint: lem-zl-field-shriek-composition-qcqs). -/
def sfCompositionLambda {V T Y S : Scheme.{u}}
    (b : V ⟶ T) (r : V ⟶ Y) (p : T ⟶ S) (i : Y ⟶ S)
    [IsOpenImmersion b] (w : b ≫ p = r ≫ i)
    (N : DerivedCategory (scalarReductionSource l E V))
    (hη : IsIso ((openDerivedAdjunction (completed l E) b).unit.app N)) :
    (pull (completed l E) i).obj
        ((push (completed l E) p).obj
          ((openExtension (completed l E) b).mapDerivedCategory.obj N)) ⟶
      (push (completed l E) r).obj N :=
  (proEtaleRingDerivedAdjunction r ((completed l E).ring Y)
    ((completed l E).ring V) ((completed l E).pull r)).unit.app _ ≫
    (push (completed l E) r).map
      ((sfCompositionPullSquare l E b r p i w).hom.app _ ≫
        (pull (completed l E) b).map
          ((proEtaleRingDerivedAdjunction p ((completed l E).ring S)
            ((completed l E).ring T) ((completed l E).pull p)).counit.app _) ≫
        @inv _ _ _ _ ((openDerivedAdjunction (completed l E) b).unit.app N) hη)

/-- The proper/open map is the specified open adjunct of inverse restriction.
Source: Stacks 0F7J and 0F7B (blueprint: lem-zl-field-shriek-composition-qcqs). -/
def sfCompositionGamma {V T Y S : Scheme.{u}}
    (b : V ⟶ T) (r : V ⟶ Y) (p : T ⟶ S) (i : Y ⟶ S)
    [IsOpenImmersion b] [IsOpenImmersion i] (w : b ≫ p = r ≫ i)
    (N : DerivedCategory (scalarReductionSource l E V))
    (hη : IsIso ((openDerivedAdjunction (completed l E) b).unit.app N))
    (hLambda : IsIso (sfCompositionLambda l E b r p i w N hη)) :
    (openExtension (completed l E) i).mapDerivedCategory.obj
        ((push (completed l E) r).obj N) ⟶
      (push (completed l E) p).obj
        ((openExtension (completed l E) b).mapDerivedCategory.obj N) :=
  ((openDerivedAdjunction (completed l E) i).homEquiv _ _).symm
    (@inv _ _ _ _ (sfCompositionLambda l E b r p i w N hη) hLambda)

/-- The normalized open compositor, conjugate to composition of open restriction.
Source: Stacks 0F7J (blueprint: lem-zl-field-shriek-composition-qcqs). -/
def sfCompositionOpenComp {X V T : Scheme.{u}} (c : X ⟶ V) (b : V ⟶ T)
    [IsOpenImmersion c] [IsOpenImmersion b] :
    (openExtension (completed l E) c).mapDerivedCategory ⋙
        (openExtension (completed l E) b).mapDerivedCategory ≅
      (openExtension (completed l E) (c ≫ b)).mapDerivedCategory :=
  Adjunction.leftAdjointCompIso (openDerivedAdjunction (completed l E) c)
    (openDerivedAdjunction (completed l E) b)
    (openDerivedAdjunction (completed l E) (c ≫ b))
    (geometricPullComposition (completed l E) c b (completedPull_comp l E c b)).symm

/-- Equality transport for exact completed open extension.
Source: Stacks 0F7J, a=bc (blueprint: lem-zl-field-shriek-composition-qcqs). -/
def sfCompositionOpenCongr {X T : Scheme.{u}} {a b : X ⟶ T}
    [IsOpenImmersion a] [IsOpenImmersion b] (w : a = b) :
    (openExtension (completed l E) a).mapDerivedCategory ≅
      (openExtension (completed l E) b).mapDerivedCategory := by
  subst b
  exact Iso.refl _

/-- The actual compatible-tower composition, before rationalizing any Hom group.
The factors are Rq_* Gamma c_!, proper composition, and open composition a=bc.
Source: Stacks 0F7J, the displayed four equalities
(blueprint: lem-zl-field-shriek-composition-qcqs). -/
def sfCompletedCompositionOnTower {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d : Compactification g) (e : Compactification (f ≫ d.i))
    (K : DerivedCategory (scalarReductionSource l E X))
    (hη : IsIso ((openDerivedAdjunction (completed l E) (pullback.fst e.g d.i)).unit.app
      ((openExtension (completed l E) e.restrict.i).mapDerivedCategory.obj K)))
    (hLambda : IsIso (sfCompositionLambda l E (pullback.fst e.g d.i) e.restrict.g e.g d.i
      e.isPullback_restrict.w.symm
        ((openExtension (completed l E) e.restrict.i).mapDerivedCategory.obj K) hη)) :
    (image (completed l E) d).obj ((image (completed l E) e.restrict).obj K) ⟶
      (image (completed l E) (d.comp e)).obj K :=
  (push (completed l E) d.g).map
      (sfCompositionGamma l E (pullback.fst e.g d.i) e.restrict.g e.g d.i
        e.isPullback_restrict.w.symm
        ((openExtension (completed l E) e.restrict.i).mapDerivedCategory.obj K) hη hLambda) ≫
    (geometricPushComposition (completed l E) e.g d.g
      (completedPull_comp l E e.g d.g)).hom.app _ ≫
    (push (completed l E) (e.g ≫ d.g)).map
      ((sfCompositionOpenComp l E e.restrict.i (pullback.fst e.g d.i)).hom.app K ≫
        (sfCompositionOpenCongr l E e.restrict_i_fst).hom.app K)

/-- Normalization of a compactification-refinement comparison. The open adjunct is
fixed by the proper counit and the open unit, and its inverse is pushed forward
using the canonical proper compositor. Source: Stacks 0F7J, independence of choices
(blueprint: lem-zl-field-shriek-composition-qcqs). -/
def SfCompletedRefinementSpec {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : DerivedCategory (scalarReductionSource l E X))
    (ρ : (image (completed l E) c).obj K ≅ (image (completed l E) d).obj K) : Prop :=
  ∃ ε : (openExtension (completed l E) d.i).mapDerivedCategory.obj K ≅
      (push (completed l E) r.hom).obj
        ((openExtension (completed l E) c.i).mapDerivedCategory.obj K),
    (openDerivedAdjunction (completed l E) d.i).homEquiv _ _ ε.hom ≫
        refinementRestriction (completed l E) r (completedPull_comp l E c.i r.hom) K =
      (openDerivedAdjunction (completed l E) c.i).unit.app K ∧
    ρ.hom =
      ((geometricPushComposition (completed l E) r.hom d.g
        (completedPull_comp l E r.hom d.g) ≪≫
          eqToIso (congrArg (fun h ↦ push (completed l E) h) r.hom_g)).symm.app _).hom ≫
        (push (completed l E) d.g).map ε.inv

end Completed

section Integral
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))] [Z.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Z ↘ Spec (.of K₀))] [QuasiCompact (Z ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [g.IsOver (Spec (.of K₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))

/-- The canonical integral compactification composition, including arbitrary choices
of the three compactifications. On any compatible tower refining those choices it
is the actual completed proper/open map, conjugated by the specified refinement and
Roos comparisons. The refinements are constrained by their adjunction normalization.
Source: Stacks 0F7J, compatible tower and independence of choices
(blueprint: lem-zl-field-shriek-composition-qcqs). -/
def SfIntegralCompositionSpec
    (α : sfCompactSupportFiniteIntegralFunctor l K₀ hl cf E ⋙
        sfCompactSupportFiniteIntegralFunctor l K₀ hl cg E ≅
      sfCompactSupportFiniteIntegralFunctor l K₀ hl cfg E) : Prop :=
  ∀ (d : Compactification g) (e : Compactification (f ≫ d.i))
    (rf : e.restrict.Refinement cf) (rg : d.Refinement cg)
    (rfg : (d.comp e).Refinement cfg) (K : sfIntegralConstructibleCategory l E X),
  ∃ hη : IsIso ((openDerivedAdjunction (completed l E) (pullback.fst e.g d.i)).unit.app
      ((openExtension (completed l E) e.restrict.i).mapDerivedCategory.obj K.obj)),
  ∃ hLambda : IsIso (sfCompositionLambda l E (pullback.fst e.g d.i) e.restrict.g e.g d.i
      e.isPullback_restrict.w.symm
        ((openExtension (completed l E) e.restrict.i).mapDerivedCategory.obj K.obj) hη),
  ∃ (ρf : (image (completed l E) e.restrict).obj K.obj ≅
      (image (completed l E) cf).obj K.obj)
    (ρg : (image (completed l E) d).obj
        ((image (completed l E) e.restrict).obj K.obj) ≅
      (image (completed l E) cg).obj ((image (completed l E) e.restrict).obj K.obj))
    (ρfg : (image (completed l E) (d.comp e)).obj K.obj ≅
      (image (completed l E) cfg).obj K.obj),
    SfCompletedRefinementSpec l E rf K.obj ρf ∧
    SfCompletedRefinementSpec l E rg ((image (completed l E) e.restrict).obj K.obj) ρg ∧
    SfCompletedRefinementSpec l E rfg K.obj ρfg ∧
    (α.hom.app K).hom =
      (sfQcqsCompactSupportRealization l E K₀ hl cg).inv.app
          ((sfCompactSupportFiniteIntegralFunctor l K₀ hl cf E).obj K) ≫
        (image (completed l E) cg).map
          ((sfQcqsCompactSupportRealization l E K₀ hl cf).inv.app K) ≫
        (image (completed l E) cg).map ρf.inv ≫ ρg.inv ≫
        sfCompletedCompositionOnTower l E d e K.obj hη hLambda ≫ ρfg.hom ≫
        (sfQcqsCompactSupportRealization l E K₀ hl cfg).hom.app K

end Integral

```

## New

Exactly the preceding definitions occur in
`Sheaf.Paper.FieldShriekCompositionNormalization`; there is no duplicate declaration.
The original module now has the additional public import

```lean
public import Sheaf.Paper.FieldShriekCompositionNormalization
```

Its existing public imports remain verbatim. The new coefficient-square theorem
is a private proof import there. Thus all existing consumers see the same
normalization constants and their unchanged definitions. No target type or meaning
changes. No source-library declaration is changed.

## Users

Read-only `tools/downstream.py Sheaf.Paper.FieldShriekCompositionQcqs --uses`
was run for all eight moved declarations. There were 323 transitive importers.
Only `Sheaf.SixFunctors.CompletedShriekCompositionLaws` mentions a moved declaration
outside the item (`sfCompositionOpenCongr`); it continues to receive it through the
original public import. No consumer source adaptation is necessary. The complete
transitive audit follows. Ownership is immaterial because no consumer is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FieldShriekCompositionQcqs | H1 | Public re-export preserves definitions; Qbar proof added. |
| Sheaf.DeligneLaumon.QbarCurveDuality | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.DeligneLaumon.RawHeartAdicRestrictionBridge | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.FourierTransform.FourierDeligneTransform | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.A1LisseSectionEvaluation | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AdicCompactificationSectionRealization | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AdicCompletedProjectionShift | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AdicNormalizedPurityLift | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AdicProjectionShiftCoherence | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AdicProjectionShiftData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AdicPurityScalarNaturality | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AdicSectionCanonicalModels | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AdicSectionClosedSupport | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AdicTraceTensorShift | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AdicTraceTransposeData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AdicUnitTraceConstruction | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AdicUnitTraceReductionData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AdicUnitTraceScalarData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AdmissibleVerdierExchange | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AffineCurveHcZero | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AffineSpaceProductDomain | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AffineSpaceTraceFactorization | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.AnchoredPureCurveCriterion | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ArithmeticRoots | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ChernFlagFormula | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ClassicalFrontierExistence | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ClassicalLisseWeilFrontierData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ClassicalSuccessiveRestrictions | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ClassicalWeilRestrictionExistence | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.CoefficientGammaRepresentatives | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.CommonAdicOpenSectionData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.CommonAdicSectionData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.CommonStageFourierTransform | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.CommonStageFourierWeightUpper | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.CommonStageWeilFourierTransform | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.CommonStageWeilShriek | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.CompactSupportLerayFiltration | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.CompactSupportProjectionFormula | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.CompactWeilCocycleEndomorphismRecurrence | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.CompactificationCompletedRealization | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.CompactifiedTowerComparisons | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.CompletedHomScalarTranspose | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ConcreteProjectionFieldDescent | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ConnectedConstantH0 | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ConstantDirectImageTowerRealization | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ConstantExtensionCompactComparison | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ConstantExtensionMixedDescent | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ConstantExtensionPullbackReturnResidue | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ConstantExtensionReturnLocalOperators | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ConstantExtensionSheetCoefficientEquivalences | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ConstantExtensionSheetCommonStageEquivalences | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ConstantExtensionSheetGeometry | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ConstantExtensionSheetHeartCoordinates | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ConstantExtensionSheetHeartData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ConstructibleMateCoherence | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ConstructibleWeilModelSquares | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.CurveIntermediateExtension | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.CurveMiddleExtensionUpper | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.CurveRestrictionFiltrationSpectrum | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.DerivedPoincarePairing | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.DlConstantFieldCharts | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.DlConstructibleFibresExact | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.DualStalkFrobenius | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ExceptionalRefinementMates | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ExtensionByZeroPunctual | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FieldCohomologyPerfectDescent | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FieldWeilShriekShiftData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FiniteAdicImageNormalization | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FiniteAdicOpenSectionData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FiniteAdicProperSectionData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FiniteBoundaryWeights | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FiniteCompactificationWeilExact | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FiniteFreeCompactComposition | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FiniteFreeCompactScalar | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FiniteFreeProjectionExchange | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FiniteFreeScalarProjection | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FiniteGeometricSectionsPointOrbits | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FiniteIndHeartAdjunction | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FiniteRationalHeartComparison | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FiniteReductionOfPurity | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FiniteSheafH0Augmentation | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FiniteWeilIndPushExact | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FixedPairTruncationCohomology | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FlagLocalComparison | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FlagPullbackInjective | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FourierKernelConvolution | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FourierTraceFormula | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FrameworkPbcComparisonData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FrameworkPbcComparisonSystem | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FrameworkPbcIntegralComparisonLaws | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FrameworkPbcPullbackScalarBridge | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FrameworkPbcRawComparisonData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FrameworkPbcRawComparisonLaws | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FrobeniusEvaluationProjectionCoherence | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FrobeniusFixesUnitSection | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FrobeniusGeometricExchange | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FrobeniusSquareExchange | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.FrobeniusSystemExchangeInverse | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.GeneralCondensedWeilRealization | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.GlobalGeometricFrobenius | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.GlobalIdentityNormalization | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.GlobalVerdierDuality | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.GlobalVerdierDualityData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.HomChainPairingNaturality | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.IdentityCompactificationLimitComparisons | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.IdentityCompactificationSystemMate | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.IntegralDualizingExceptionalUnit | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.IntegralSectionsPerfectReduction | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.IntegralSemilinearGermSquare | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.LisseDenseOpenRecovery | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.LisseExtensionInertia | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.LocalFrobeniusConjugacy | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.LocalFrobeniusStepCompatibility | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.LocalizedFlagProduct | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.LocalizedTopChern | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.MiddleExtensionHcZero | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.NativeWeilScalarCounitData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.NormalizedFiniteFibreModels | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.NormalizedFiniteRealizationFibre | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.PodCtfAdjunctions | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.PodCtfPairingMaps | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.PodHomChainCounitFormula | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.PodHomChainCtfDomains | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.PodHomChainUncurriedTransport | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.PoincarePointFiniteness | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.PointCompletedEvaluation | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.PointFrobeniusTransportNormalization | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.PointWeilPairingRealization | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ProjectionFormulaCoherence | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ProjectionWeilTensorDomainBridge | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ProjectiveBundleFormula | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ProperCoincidenceFrobenius | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ProperCompactCoincidence | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ProperWeilIterateGermFormula | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.PurAdicReconstruction | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.PurityChernClasses | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.PurityTensorMapNaturality | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.RationalExceptionalFinalEquations | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.RationalOrdinaryCohomologyTensor | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.RationalPurityCoherenceDescent | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.RationalPurityComparisonDescent | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.RationalPurityScalarLocalization | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.RationalPuritySourceLocalization | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.RationalScalarComparisonData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.RationalScalarComparisonIdentification | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.RationalStalkExact | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ReducedFrontierMixedGluing | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.RelativeKunneth | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ScalarExchangeConstituents | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.SemilinearExchangeCubeCoherence | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.SemilinearGermIterationDescent | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.SfLocalizationAllStages | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.SfNormalizedRationalClosedComparison | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.SfNormalizedRationalWeilSquares | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.SmoothProperPurityHypotheses | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.SupportedProjectionSplitting | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.TensorAdjunctionExchange | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.TensorHomCoefficientTransposes | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.TensorHomExchange | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.TensorMapPresentationIndependent | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.TensorMateInvertibleInput | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.TraceCompactificationCohomology | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.TwFrobeniusAction | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.TwistFrobeniusScalar | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.TwistedPullbackPbcPullback | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.TwistedPullbackPbcTwist | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.TwistedPullbackScalarShifts | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.TwistedPullbackSquareMaps | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.TwistedPullbackSquareScalars | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.VectorBundleThom | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.VectorBundleThomClass | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.VectorBundleThomMaps | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.VectorBundleThomProduct | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.VerdierCoefficientRealization | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.VerdierCompositionMateNormalization | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.VerdierExchange | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.VerdierHomChainComposition | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.WeilBaseChangeSemilinearPasting | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.WeilChosenDualityExchange | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.WeilChosenDualityExchangeData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.WeilChosenExchangeConstruction | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.WeilChosenTransposeNaturality | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.WeilCompactSupportCohomology | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.WeilFourierInversion | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.WeilFourierPlancherel | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.WeilMixedUpperBounds | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.WeilOpenImageDelta | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.WeilPullbackFibreReturn | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.WeilShriekShiftCompatibility | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.WfTensorCompletionFrobenius | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ZlCanonicalImmersionCohomology | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ZlImmersionPullbackWeightPreservation | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ZlShriekComposition | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ZlWeilHeartLocalizationExact | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.CompactifiedProperTowerExchange | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.CompletedShriekCompositionLaws | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.FiniteAdjunctionNaturality | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.FiniteAdjunctionSquare | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.FiniteAdjunctionTransitionData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.FiniteMappingAdjunctionData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescent | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentIsIso | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentTranspose | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.FiniteReturnFrobeniusCancellation | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.FiniteScalarMateData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.FrobeniusFiniteExchangeInverse | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.IntegralNormalizedRefinementPasting | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.IntegralOperationShiftData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.SupportedWeilMateLift | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.TensorHomTranspositionData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.VerdierExchangeData | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.SixFunctors.WeilChosenDualityHom | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.TraceFormula.CompactDirectPowerTransportNormalization | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.TraceFormula.FrobeniusCompactPowerExchange | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.TraceFormula.FrobeniusProperPowerExchange | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.TraceFormula.LocalNormalizationStrictRealization | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | not edited | Unchanged signatures and data, publicly re-exported. |
| Sheaf.ZetaWeil.WeightPurityRoots | not edited | Unchanged signatures and data, publicly re-exported. |

## Status

landed 20261025T202137-L-2679198 2026-10-25 (merge of deliver/H1/Sheaf.Paper.FieldShriekCompositionQcqs)
