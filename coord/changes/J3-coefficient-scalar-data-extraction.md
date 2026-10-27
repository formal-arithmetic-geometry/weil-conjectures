# Coefficient scalar tensor realization data extraction

## Reason

The independent section realization and derived tensor square lemmas use the existing
scalar constructions and realization predicate. Extract them unchanged to
`Sheaf.Paper.CoefficientScalarTensorData` so that both lemmas and their parent theorem
import the same constructions without a cycle. The item publicly re-exports that
module. Every moved declaration retains its name, universe parameters, signature and
body. No source-library module or target statement is changed.

The two split statements are the distinct section-realization and tensor-equation
parts of the mathematical argument. The parent proves ordinary coefficient-square
monoidality and applies them. This is a partial decomposition, not a claimed completed
proof or a subdivision of a completed slow proof. The data module has no proof holes.

## Old

The following block was in `Sheaf.Paper.CoefficientScalarTensorRealization`:

```lean
/-- The section-ring map of the actual coefficient morphism.
Source: Stacks 03EK, 07A6
(blueprint: lem-sfb-coefficient-scalar-tensor-realization). -/
abbrev coefficientSectionScalarMap (Z : Scheme.{u}) :
    ModuleRingedComparison.ring R Z ⟶ ModuleRingedComparison.ring S Z :=
  InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
    (Scheme.ProEt.topology Z) (coefficientMap a Z)

variable [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R Z)]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S Z)]

/-- The canonical scalar/pullback path comparison, obtained by total left derivation
of the ordinary ring-compatible coefficient square. Thus its direction is P_S T_Y → T_X P_R.
Source: Stacks 0D6D, 07A4
(blueprint: lem-sfb-coefficient-scalar-tensor-realization). -/
def coefficientScalarPathIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    internalScalarExtension a Y ⋙ moduleObjectDerivedPullback S f ≅
      moduleObjectDerivedPullback R f ⋙ internalScalarExtension a X :=
  letI := internalScalarMonoidal a X
  letI := internalScalarMonoidal a Y
  Functor.leftDerivedFunctorCompNatIso (upperStar R f)
    (Mod.extendScalars (coefficientMap a X)) (Mod.extendScalars (coefficientMap a Y))
    (upperStar S f) (pullIso a f).symm

/-- The actual geometric derived tensor comparison, with its pointwise type displayed.
This is the comparison used in the module-object projection morphism, without replacing it
by an unspecified monoidal structure.
Source: blueprint main-20261015, six-functors basics, module derived push/pull
(blueprint: lem-sfb-coefficient-scalar-tensor-realization). -/
def coefficientGeometricTensorComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : DerivedCategory (ModuleRingedComparison.internalModules Λ Y)) :
    (moduleObjectDerivedPullback Λ f).obj (((derivedTensor Λ Y).obj A).obj B) ⟶
      ((derivedTensor Λ X).obj ((moduleObjectDerivedPullback Λ f).obj A)).obj
        ((moduleObjectDerivedPullback Λ f).obj B) :=
  ((leftDerivedUpperStarTensor Λ f).app A).app B

/-- The actual sheafification image of s tensor x, in a normalized section scalar pair.
The equality transport identifies its extension object with the existing changeOfRings.
Source: Stacks 03EK
(blueprint: lem-sfb-coefficient-scalar-tensor-realization). -/
def coefficientSectionScalarPure (Z : Scheme.{u})
    (b : SheafOfModules.ScalarDerivedPair.{u + 1, u, u + 1, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (coefficientSectionScalarMap a Z))
    (M : ModuleRingedComparison.modules R Z) (V : Z.ProEtᵒᵖ)
    (s : (ModuleRingedComparison.ring S Z).obj.obj V) (x : M.val.obj V) :
    (b.extension.obj M).val.obj V :=
  (eqToHom (b.extension_obj M).symm).val.app V
    ((toSheafify (Scheme.ProEt.topology Z)
      (SheafOfModules.changeOfRingsPresheaf (coefficientSectionScalarMap a Z) M).presheaf).app V
        (s ⊗ₜ[_, ((coefficientSectionScalarMap a Z).hom.app V).hom] x))

/-- The canonical exact scalar-extension comparison on a complex. Its two factors
are the universal derived-to-exact comparison and the exact localization comparison.
Source: Stacks 06YY, 07A6
(blueprint: lem-sfb-coefficient-scalar-tensor-realization). -/
def coefficientInternalScalarComplex (Z : Scheme.{u})
    (P : CochainComplex (ModuleRingedComparison.internalModules R Z) ℤ) :
    (internalScalarExtension a Z).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((Mod.extendScalars (coefficientMap a Z)).mapHomologicalComplex (.up ℤ)).obj P) :=
  (Mod.extendScalars (coefficientMap a Z)).leftDerivedFunctorIsoMapDerivedCategory.hom.app
      (DerivedCategory.Q.obj P) ≫
    (Mod.extendScalars (coefficientMap a Z)).mapDerivedCategoryFactors.hom.app P

/-- Signed direct-sum totalization of the ordinary scalar tensorator.
Source: Stacks 07A4, constituent maps of 03EL
(blueprint: lem-sfb-coefficient-scalar-tensor-realization). -/
def coefficientSectionScalarTotal (Z : Scheme.{u})
    (b : SheafOfModules.ScalarDerivedPair.{u + 1, u, u + 1, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (coefficientSectionScalarMap a Z))
    (m : b.extension.Monoidal)
    (P Q : CochainComplex (ModuleRingedComparison.modules R Z) ℤ) :
    (b.extension.mapHomologicalComplex (.up ℤ)).obj
        ((ModuleRingedComparison.totalTensor R Z).obj (P, Q)) ⟶
      (ModuleRingedComparison.totalTensor S Z).obj
        ((b.extension.mapHomologicalComplex (.up ℤ)).obj P,
          (b.extension.mapHomologicalComplex (.up ℤ)).obj Q) :=
  letI := m
  letI : PreservesColimitsOfSize.{0, 0} b.extension :=
    b.ordinaryAdjunction.leftAdjoint_preservesColimits
  (b.extension.mapHomologicalComplex (.up ℤ)).map
      (eqToHom (ModuleRingedComparison.totalTensor_obj R Z P Q)) ≫
    HomologicalComplex.mapBifunctorComparison
      (F := curriedTensor (ModuleRingedComparison.modules R Z))
      (F' := curriedTensor (ModuleRingedComparison.modules S Z))
      (G := b.extension) (G₁ := b.extension) (G₂ := b.extension)
      (Functor.OplaxMonoidal.δNatTrans b.extension) (.up ℤ) P Q ≫
    eqToHom (ModuleRingedComparison.totalTensor_obj S Z
      ((b.extension.mapHomologicalComplex (.up ℤ)).obj P)
      ((b.extension.mapHomologicalComplex (.up ℤ)).obj Q)).symm

/-- The scalar realization clauses, with every operation tied to the actual coefficient
map. The section pair has the existing universal left-derived and adjunction normalization.
The ordinary tensorator is pinned on all generalized balanced generators. The derived
one is pinned separately by its flat-term K-flat representative square, and is then
identified with the specified internal tensorator. No existence witness is chosen as data.
Source: Stacks 03EK, 03EL, 06YY, 07A4, 07A6
(blueprint: lem-sfb-coefficient-scalar-tensor-realization). -/
def CoefficientScalarSectionRealization (Z : Scheme.{u}) : Prop :=
  ∃ b : SheafOfModules.ScalarDerivedPair.{u + 1, u, u + 1, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (coefficientSectionScalarMap a Z),
  ∃ o : Mod.extendScalars (coefficientMap a Z) ⋙
      (ModuleRingedComparison.equivalence S Z).functor ≅
    (ModuleRingedComparison.equivalence R Z).functor ⋙ b.extension,
  ∃ r : Mod.comap (coefficientMap a Z) ⋙
      (ModuleRingedComparison.equivalence R Z).functor ≅
    (ModuleRingedComparison.equivalence S Z).functor ⋙
      SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
      (R := ModuleRingedComparison.ring R Z) (S := ModuleRingedComparison.ring S Z)
      (coefficientSectionScalarMap a Z),
  (∀ (M : ModuleRingedComparison.internalModules R Z) (V : Z.ProEtᵒᵖ)
      (s : (condensedRingObj S Z).obj.obj V) (x : M.X.obj.obj V),
    (o.hom.app M).val.app V
        (InternalAbelianSheafModule.internalScalarGenerator.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Z)
          (coefficientMap a Z) M V s x) =
      coefficientSectionScalarPure a Z b
        ((ModuleRingedComparison.equivalence R Z).functor.obj M) V s x) ∧
  (∀ (N : ModuleRingedComparison.internalModules S Z) (V : Z.ProEtᵒᵖ)
      (x : N.X.obj.obj V), (r.hom.app N).val.app V x = x) ∧
  (∀ (M : ModuleRingedComparison.internalModules R Z)
      (N : ModuleRingedComparison.internalModules S Z)
      (g : (Mod.extendScalars (coefficientMap a Z)).obj M ⟶ N),
    (ModuleRingedComparison.equivalence R Z).functor.map
        ((Mod.extendRestrictAdjunction (coefficientMap a Z)).homEquiv M N g) ≫
          r.hom.app N =
      b.ordinaryAdjunction.homEquiv _ _
        (o.inv.app M ≫ (ModuleRingedComparison.equivalence S Z).functor.map g)) ∧
  ∃ p : internalScalarExtension a Z ⋙
      (ModuleRingedComparison.derivedEquivalence S Z).functor ≅
    (ModuleRingedComparison.derivedEquivalence R Z).functor ⋙ b.derived,
  ∃ q : (Mod.comap (coefficientMap a Z)).mapDerivedCategory ⋙
      (ModuleRingedComparison.derivedEquivalence R Z).functor ≅
    (ModuleRingedComparison.derivedEquivalence S Z).functor ⋙
      SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
      (R := ModuleRingedComparison.ring R Z) (S := ModuleRingedComparison.ring S Z)
      (coefficientSectionScalarMap a Z),
  (q = (Functor.mapDerivedCategoryCompIso (Mod.comap (coefficientMap a Z))
      (ModuleRingedComparison.equivalence R Z).functor).symm ≪≫
    Functor.mapDerivedCategoryNatIso r ≪≫
    Functor.mapDerivedCategoryCompIso (ModuleRingedComparison.equivalence S Z).functor
      (SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
      (R := ModuleRingedComparison.ring R Z) (S := ModuleRingedComparison.ring S Z)
      (coefficientSectionScalarMap a Z))) ∧
  (∀ (P : CochainComplex (ModuleRingedComparison.internalModules R Z) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (R := ModuleRingedComparison.ring R Z)
      (((ModuleRingedComparison.equivalence R Z).functor.mapHomologicalComplex
        (.up ℤ)).obj P) →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (R := ModuleRingedComparison.ring R Z)
      ((ModuleRingedComparison.equivalence R Z).functor.obj (P.X n))) →
    (ModuleRingedComparison.derivedEquivalence S Z).functor.map
        (coefficientInternalScalarComplex a Z P) ≫
      (ModuleRingedComparison.equivalence S Z).functor.mapDerivedCategoryFactors.hom.app
        (((Mod.extendScalars (coefficientMap a Z)).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex o (.up ℤ)).hom.app P) =
    p.hom.app (DerivedCategory.Q.obj P) ≫
      b.derived.map
        ((ModuleRingedComparison.equivalence R Z).functor.mapDerivedCategoryFactors.hom.app P) ≫
      SheafOfModules.scalarPairComplexComparison
        (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
        (R := ModuleRingedComparison.ring R Z) (S := ModuleRingedComparison.ring S Z)
        b.extension b.extension_additive b.derived
        b.counit (((ModuleRingedComparison.equivalence R Z).functor.mapHomologicalComplex
          (.up ℤ)).obj P)) ∧
  (∀ (M : DerivedCategory (ModuleRingedComparison.internalModules R Z))
      (N : DerivedCategory (ModuleRingedComparison.internalModules S Z))
      (g : (internalScalarExtension a Z).obj M ⟶ N),
    (ModuleRingedComparison.derivedEquivalence R Z).functor.map
        ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Z)).homEquiv M N g) ≫
      q.hom.app N =
    b.adjunction.homEquiv _ _
      (p.inv.app M ≫ (ModuleRingedComparison.derivedEquivalence S Z).functor.map g)) ∧
  ∃ m : b.extension.Monoidal,
  (∀ (M N : ModuleRingedComparison.modules R Z) (V : Z.ProEtᵒᵖ)
      (s : (ModuleRingedComparison.ring S Z).obj.obj V)
      (x : M.val.obj V) (y : N.val.obj V),
    (m.toOplaxMonoidal.δ M N).val.app V
        (coefficientSectionScalarPure a Z b (M ⊗ N) V s
          (ModuleRingedComparison.sectionPureTensor R Z M N V x y)) =
      ModuleRingedComparison.sectionPureTensor S Z (b.extension.obj M) (b.extension.obj N) V
        (coefficientSectionScalarPure a Z b M V s x)
        (coefficientSectionScalarPure a Z b N V 1 y)) ∧
  ∃ t : ModuleRingedComparison.tensor R Z ⋙ b.derived ≅
      b.derived.prod b.derived ⋙ ModuleRingedComparison.tensor S Z,
  (∀ (P Q : CochainComplex (ModuleRingedComparison.modules R Z) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (R := ModuleRingedComparison.ring R Z) P →
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (R := ModuleRingedComparison.ring R Z) Q →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
      (R := ModuleRingedComparison.ring R Z) (P.X n)) →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
      (R := ModuleRingedComparison.ring R Z) (Q.X n)) →
    b.derived.map ((ModuleRingedComparison.qTensor R Z).app (P, Q)) ≫
      SheafOfModules.scalarPairComplexComparison
        (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
        (R := ModuleRingedComparison.ring R Z) (S := ModuleRingedComparison.ring S Z)
        b.extension b.extension_additive b.derived
        b.counit ((ModuleRingedComparison.totalTensor R Z).obj (P, Q)) ≫
      DerivedCategory.Q.map (coefficientSectionScalarTotal a Z b m P Q) =
    t.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (ModuleRingedComparison.tensor S Z).map (Prod.mkHom
        (SheafOfModules.scalarPairComplexComparison
        (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
        (R := ModuleRingedComparison.ring R Z) (S := ModuleRingedComparison.ring S Z)
        b.extension b.extension_additive b.derived
          b.counit P)
        (SheafOfModules.scalarPairComplexComparison
        (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
        (R := ModuleRingedComparison.ring R Z) (S := ModuleRingedComparison.ring S Z)
        b.extension b.extension_additive b.derived
          b.counit Q)) ≫
      (ModuleRingedComparison.qTensor S Z).app
        ((b.extension.mapHomologicalComplex (.up ℤ)).obj P,
          (b.extension.mapHomologicalComplex (.up ℤ)).obj Q)) ∧
  ∀ M N : DerivedCategory (ModuleRingedComparison.internalModules R Z),
    (ModuleRingedComparison.derivedEquivalence S Z).functor.map
        (((internalScalarTensorComparison a Z).app M).app N) ≫
      (ModuleRingedComparison.tensorComparison S Z).hom.app
        ((internalScalarExtension a Z).obj M, (internalScalarExtension a Z).obj N) ≫
      (ModuleRingedComparison.tensor S Z).map (Prod.mkHom (p.hom.app M) (p.hom.app N)) =
    p.hom.app (((derivedTensor R Z).obj M).obj N) ≫
      b.derived.map ((ModuleRingedComparison.tensorComparison R Z).hom.app (M, N)) ≫
      t.hom.app ((ModuleRingedComparison.derivedEquivalence R Z).functor.obj M,
        (ModuleRingedComparison.derivedEquivalence R Z).functor.obj N)
```

## New

The same block, verbatim, is in `Sheaf.Paper.CoefficientScalarTensorData`.
The original module retains all its existing public imports and adds:

```lean
public import Sheaf.Paper.CoefficientScalarTensorData
```

Thus each existing public declaration is still imported under the same name with
the same construction. The independent representative theorem privately imported
by the item has one separate mathematical proof obligation. Its hypotheses and
conclusion mention only this fixed shared data. No target meaning changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientScalarTensorRealization | J3 | Combines the two genuine remaining steps with the proved ordinary monoidality argument. |
| Sheaf.Paper.CoefficientScalarTensorData | new, J3 | Receives the identical six existing constructions and predicate. |
| Sheaf.Paper.CoefficientScalarSectionRealization | new, J3 | States section scalar realization, independently of a geometric morphism. |
| Sheaf.Paper.CoefficientScalarDerivedTensorSquare | new, J3 | States the tensor equation assuming ordinary square monoidality. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleCounitScalarModel | X8 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.AdicOperationDomainsSourceComparison | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.AffineCounitScalar | E1 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | E1 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | H2 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.BrownTowerBoundedTransport | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.BrownTowerFiniteEvaluation | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.BrownTowerFiniteSiteComparison | U5 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.BrownTowerRealization | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.BrownTowerSite | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.CartesianSectionData | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ChartCounitScalarTransport | M9 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.CoefSupportOpenTensorModel | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.CoefSupportPointSectionsData | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.CoefficientPathNormalization | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.CoefficientProjectionSquare | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | A4 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.CompactificationProjectionInverse | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ConcreteIntegralProjectionCone | D6 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ConcreteProjectionFieldDescent | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstruction | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.CondensedHomChainRealization | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | P3 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperScalarComparison | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | B4 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation | W6 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | Y6 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.EtaleCtfChartDomain | E2 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.EtaleOpenCounitFlatModels | H1 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y7 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.EtaleSumCounitScalar | V5 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.FiniteAdjointCompositorTransposes | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | P8 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportDomains | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.FiniteExceptionalCompositorCoefficients | F9 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | G6 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.FiniteLocalizingSmoothLocalFormula | C1 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.FiniteProperLocalizing | W4 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.FiniteTorStability | E5 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | K4 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.GeneralHomComparisonCocycles | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.GeometricComparisonData | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.GeometricGeneratorProjectionDevissage | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.GeometricOperations | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | P4 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | H4 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | K3 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.InverseContravariantBidual | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | F3 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.NativeCompactProjectionFormula | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.NativeWeilDualizingHomTransposition | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.NormAlgClInternalHomBaseChange | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.OpenExceptionalScalarLocality | J1 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.OpenProEtaleCounitScalar | F3 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.OrderedCompactificationScalarSquare | H3 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.OrderedTateScalarNormalization | H4 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.P1CounitScalar | F4 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.P1SplittingScalar | G1 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.PointTraceReconstruction | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | C2 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoherence | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ProjectiveDiagonalComposition | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ProperAlgClComparisonDomains | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPair | K9 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.PurIntegralSupportComparison | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U2 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.RationalP1AmbientComposites | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.RationalP1DiagonalTensor | C2 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.RationalP1Triangle | Q8 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.RationalP1UnitCounit | C3 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.RawChartScalarCounitPasting | P6 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.RelativeKunneth | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.RestrictionLocal | C3 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | S4 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.ShriekNormalizedTransitionComparison | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateCategories | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateRightComparisons | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateTensorComparisons | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitRepresentability | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGluing | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerReductionTranspose | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.SupportedLatticeNormProjection | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.TamePairProperGenerators | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.TateTwistedProjection | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.TowerProjectionDomainEvaluation | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | P1 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.TraceCorrespondences | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Paper.WeilCompactStructureTensorComparison | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction | G4 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.OpenScalarInverseTransposeFactorization | K7 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.Reduction | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | D3 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefPairingSystemDinaturality | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | V1 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefSystemProjectionEvaluation | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefficientProjectionPointData | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | G1 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteCounitRestrictionSquare | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | X3 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralAffinePurityInduction | J9 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | D3 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralProjectiveLineAdjunction | K5 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionFunctors | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralTateLineConstructible | K6 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | Y3 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | H7 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.ScalarCompositeModelPasting | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.ScalarRefinementClosureSquare | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.ScalarSixCompactSupport | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.ScalarSixCtf | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.ScalarSixDirectImage | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | D2 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | P2 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.WeilSheaf.NativePullbackStarPreservation | R3 | Identical names, signatures, bodies and public re-export; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| TargetsCheck | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | S6 | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.Statement | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Additivity | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.BaseChangeCoherence | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.BorelMoore | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.CoefficientMorphism | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.CompactCohomology | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.CompactPullback | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Correspondence | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.CorrespondencePair | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.CurvePieces | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Dualizing | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.FibreCoherence | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.FibreModel | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.FixedPoint | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.FixedPointScheme | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Frobenius | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.GenericQuotient | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.HomologyUnit | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.KunnethVerdier | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.LefschetzVerdier | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.LocalTerm | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.LocalTermLocality | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Main | D9 | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.ModelExtension | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.OpenPieceCoherence | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.OpenSquare | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.PointNormalization | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Product | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.ProperCompatibility | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.ProperCurve | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.ProperPushforward | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.PullbackFamily | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobenius | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusComparison | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusIterate | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunction | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionInduction | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Stalk | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.SupportedPairing | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.TraceClass | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.TraceClassAdditivity | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.WeilBaseChange | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.TraceFormula.WeilTrace | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.WeilObjectComparison | unclaimed | Identical names, signatures, bodies and public re-export; no adaptation. |

## Status

landed 20261025T202241-L-2698084 2026-10-25 (merge of deliver/J3/Sheaf.Paper.CoefficientScalarTensorRealization)
