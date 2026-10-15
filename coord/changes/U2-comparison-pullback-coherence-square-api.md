# AlgebraicGeometry.ProEtale.ComparisonPullbackCoherent

## Reason

The fully expanded square component equation forced the kernel to repeatedly compare
large instantiated sheaf-category expressions when specializing the generic square
pasting calculation. The same proof exceeded 60 seconds. Give that clause an API
which shares its canonical data in a structure and keeps the component predicate
named. The independently checked whole module compiles in 14.4 seconds on the project server.

This is a definitionally identical refactor: substitute the eighteen fields of
`comparisonSquareData` into `ComparisonSquareComponent` to obtain exactly the old
square equation, with the same binders, commutativity transport and coefficients.
The identity and composition clauses are verbatim unchanged. Every original
inverse-image functor, adjunction, identity/composition/square isomorphism and the
signature of `comparison_pullback_coherent` is unchanged. No target signature or
mathematical meaning changes. The independent second reading verified this expansion field by field. The local
continuity instance used only by the proof is private.

## Old

```lean
def ComparisonPullbackCoherent : Prop :=
  (∀ (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology D),
    (comparisonCoefficientPullbackIso D (𝟙 X)).hom.app F ≫
        (proEtaleComparisonId D X).hom.app ((comparisonCoefficientPullback D X).obj F) =
      (comparisonCoefficientPullback D X).map ((etaleComparisonId D X).hom.app F)) ∧
  (∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
      (F : Sheaf Z.smallEtaleTopology D),
    (comparisonCoefficientPullback D X).map ((etaleComparisonComp D f g).hom.app F) ≫
        (comparisonCoefficientPullbackIso D f).hom.app ((etaleComparisonPullback D g).obj F) ≫
        (proEtaleComparisonPullback D f).map ((comparisonCoefficientPullbackIso D g).hom.app F) =
      (comparisonCoefficientPullbackIso D (f ≫ g)).hom.app F ≫
        (proEtaleComparisonComp D f g).hom.app ((comparisonCoefficientPullback D Z).obj F)) ∧
  (∀ (X' X Y' Y : Scheme.{u}) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : ChosenCartesianSquare g' f' f g)
      (F : Sheaf Y.smallEtaleTopology D),
    (comparisonCoefficientPullbackIso D f').hom.app ((etaleComparisonPullback D g).obj F) ≫
        (proEtaleComparisonPullback D f').map ((comparisonCoefficientPullbackIso D g).hom.app F) ≫
        (proEtaleComparisonSquare D sq).hom.app ((comparisonCoefficientPullback D Y).obj F) =
      (comparisonCoefficientPullback D X').map ((etaleComparisonSquare D sq).hom.app F) ≫
        (comparisonCoefficientPullbackIso D g').hom.app ((etaleComparisonPullback D f).obj F) ≫
        (proEtaleComparisonPullback D g').map ((comparisonCoefficientPullbackIso D f).hom.app F))
```

## New

Three public, fully constructed auxiliary definitions are attached to the existing
node `lem-weil-pbc-comparison-pullback`; none contains a proof hole.

```lean
structure ComparisonSquareData
    (A B B' C P Q Q' R : Type*) [Category* A] [Category* B] [Category* B']
    [Category* C] [Category* P] [Category* Q] [Category* Q'] [Category* R] where
  L₁ : A ⥤ B
  L₂ : B ⥤ C
  L₁' : A ⥤ B'
  L₂' : B' ⥤ C
  K₀ : A ⥤ P
  K₁ : B ⥤ Q
  K₁' : B' ⥤ Q'
  K₂ : C ⥤ R
  R₁ : P ⥤ Q
  R₂ : Q ⥤ R
  R₁' : P ⥤ Q'
  R₂' : Q' ⥤ R
  c₂ : L₂ ⋙ K₂ ≅ K₁ ⋙ R₂
  c₁ : L₁ ⋙ K₁ ≅ K₀ ⋙ R₁
  c₂' : L₂' ⋙ K₂ ≅ K₁' ⋙ R₂'
  c₁' : L₁' ⋙ K₁' ≅ K₀ ⋙ R₁'
  se : L₁ ⋙ L₂ ≅ L₁' ⋙ L₂'
  sp : R₁ ⋙ R₂ ≅ R₁' ⋙ R₂'

/-- The componentwise square equation for the supplied comparison data.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof step 4
(blueprint: lem-weil-pbc-comparison-pullback). -/
def ComparisonSquareComponent
    {A B B' C P Q Q' R : Type*} [Category* A] [Category* B] [Category* B']
    [Category* C] [Category* P] [Category* Q] [Category* Q'] [Category* R]
    (s : ComparisonSquareData A B B' C P Q Q' R) (F : A) : Prop :=
  s.c₂.hom.app (s.L₁.obj F) ≫ s.R₂.map (s.c₁.hom.app F) ≫ s.sp.hom.app (s.K₀.obj F) =
    s.K₂.map (s.se.hom.app F) ≫ s.c₂'.hom.app (s.L₁'.obj F) ≫
      s.R₂'.map (s.c₁'.hom.app F)

noncomputable def comparisonSquareData {X' X Y' Y : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : ChosenCartesianSquare g' f' f g) :
    ComparisonSquareData
      (Sheaf Y.smallEtaleTopology D) (Sheaf Y'.smallEtaleTopology D)
      (Sheaf X.smallEtaleTopology D) (Sheaf X'.smallEtaleTopology D)
      (Sheaf (Scheme.ProEt.topology Y) D) (Sheaf (Scheme.ProEt.topology Y') D)
      (Sheaf (Scheme.ProEt.topology X) D) (Sheaf (Scheme.ProEt.topology X') D) where
  L₁ := etaleComparisonPullback D g
  L₂ := etaleComparisonPullback D f'
  L₁' := etaleComparisonPullback D f
  L₂' := etaleComparisonPullback D g'
  K₀ := comparisonCoefficientPullback D Y
  K₁ := comparisonCoefficientPullback D Y'
  K₁' := comparisonCoefficientPullback D X
  K₂ := comparisonCoefficientPullback D X'
  R₁ := proEtaleComparisonPullback D g
  R₂ := proEtaleComparisonPullback D f'
  R₁' := proEtaleComparisonPullback D f
  R₂' := proEtaleComparisonPullback D g'
  c₂ := comparisonCoefficientPullbackIso D f'
  c₁ := comparisonCoefficientPullbackIso D g
  c₂' := comparisonCoefficientPullbackIso D g'
  c₁' := comparisonCoefficientPullbackIso D f
  se := etaleComparisonSquare D sq
  sp := proEtaleComparisonSquare D sq

def ComparisonPullbackCoherent : Prop :=
  (∀ (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology D),
    (comparisonCoefficientPullbackIso D (𝟙 X)).hom.app F ≫
        (proEtaleComparisonId D X).hom.app ((comparisonCoefficientPullback D X).obj F) =
      (comparisonCoefficientPullback D X).map ((etaleComparisonId D X).hom.app F)) ∧
  (∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
      (F : Sheaf Z.smallEtaleTopology D),
    (comparisonCoefficientPullback D X).map ((etaleComparisonComp D f g).hom.app F) ≫
        (comparisonCoefficientPullbackIso D f).hom.app ((etaleComparisonPullback D g).obj F) ≫
        (proEtaleComparisonPullback D f).map ((comparisonCoefficientPullbackIso D g).hom.app F) =
      (comparisonCoefficientPullbackIso D (f ≫ g)).hom.app F ≫
        (proEtaleComparisonComp D f g).hom.app ((comparisonCoefficientPullback D Z).obj F)) ∧
  (∀ (X' X Y' Y : Scheme.{u}) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : ChosenCartesianSquare g' f' f g)
      (F : Sheaf Y.smallEtaleTopology D),
    ComparisonSquareComponent (comparisonSquareData D g' f' f g sq) F)
```

## Users

`tools/downstream.py` lists the following transitive importers. A repository-wide
whole-word search finds no use of `ComparisonPullbackCoherent` or
`comparison_pullback_coherent` outside this module. Consequently no other module
needs adaptation, and no other module is changed. All their statements have the
same meaning since the refactored predicate is definitionally the old predicate.
The holder column records the shared claims when this record was written.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence | U2 | Definition refactor and proof. |
| Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| Sheaf.AlgebraicGeometry.ComparisonDirectImage | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleFunctionsQuotientSections | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | C2 | Imports only; no use of the changed definition by name; unchanged. |
| Sheaf.Paper.ProEtaleLisseOrigin | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| TargetsCheck | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexInternalHom | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.AmbientCounterexample | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.AmbientCounterexampleCoproducts | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Comparison | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Comparison.Counterexample | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic | V2 | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.AlgClosedField | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Comparison | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ComparisonMonoidal | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Constructible | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.DualPerfect | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Duality | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Finiteness | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.FlatModel | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.HomComparison | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationConstructible | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationFiniteTor | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekBaseChange | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekComparison | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekIndependence | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerStarProjectionComparison | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.OpenCover | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormula | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormulaExtendScalars | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ScalarExtension | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Shift | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Stability | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitude | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitudeResidue | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.WeilComplex | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtension | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Additivity | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Adic | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobenius | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobeniusLift | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobeniusTrace | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicRange | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicSystem | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AffineLine | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AffineReduction | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Correspondence | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Curve | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Defs | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.FiniteModel | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.FixedPoints | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Frobenius | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.GlobalOperator | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Iterate | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.KernelPushforward | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.LocalFrobenius | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Localization | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Main | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ModelRestriction | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Pairing | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Perfectness | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperCurve | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperPushforward | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.PushforwardFibres | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.PushforwardStep | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.RelativeAffineLine | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceClass | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceFormulaHolds | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceMap | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.WeaklyContractibleCohomology | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.Statement | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Imports only; no use of the changed definition by name; unchanged. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Imports only; no use of the changed definition by name; unchanged. |

## Status

landed 20261015T224822-L-2950778 2026-10-15 (merge of deliver/U2/Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence)
