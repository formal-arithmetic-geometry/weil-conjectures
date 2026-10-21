# AlgebraicGeometry.Scheme.adicResidueComparisonData and the local lifting coefficient API

## Reason

Restore the quarantined item with its exact theorem statement. Four source-backed parts of
its proof need the original six coefficient definitions in their statements. Move those
definitions unchanged into a publicly imported companion to avoid an import cycle.
Its actual successor comparison uses the already proved adicFiniteExtendComp construction,
so the companion publicly imports Sheaf.Paper.AdicConstructibleFiniteReductions. The
original exported imports remain reachable. Every old declaration retains its full name,
visibility, universes, type and non-theorem body. No target or definition changes meaning.

The main file adds a proof transparency option. Two new files locally disable the overly
general hasSheafify_of_essentiallySmall instance to infer the standard coefficient-sized
derived localization. No global instance or axiom is registered.

## Old

The six definitions from the assigned quarantine archive, verbatim:

```lean
/-- The algebraic lift of comparison, specified on all operations and constants.
Source: Stacks Tags 00YV and 03D2
(blueprint: lem-sfb-adic-residue-lisse-perfect-lift). -/
def adicResidueComparisonData (X : Scheme.{u}) :=
  Classical.choice (CategoryTheory.ConstantCompletion.inverseImageData_exists
    (smallModelComparisonPullback.{u, v} X)
    (smallModelComparisonPushforward.{u, v} X) (smallModelProEtaleComparison.{u, v} X))

/-- Derived comparison with its canonical constant coefficient map.
Source: Stacks Tags 06YY and 099R
(blueprint: lem-sfb-adic-residue-lisse-perfect-lift). -/
def adicResidueComparison (X : Scheme.{u}) (R : Type (max v (u + 1))) [CommRing R] :=
  (CategoryTheory.ConstantCompletion.derivedPull (adicResidueComparisonData.{u, v} X)
    (smallModelComparisonPushforward.{u, v} X) (smallModelProEtaleComparison.{u, v} X)
    (CategoryTheory.ConstantCompletion.constantMap (adicResidueComparisonData.{u, v} X) R)).functor

/-- Completed constant realization of a complex of coefficient modules, termwise.
Source: Stacks Tag 09C6 (blueprint: lem-sfb-adic-residue-lisse-perfect-lift). -/
def adicResidueConstantPerfect (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) :
    CategoryTheory.ConstantCompletion.D
      (CategoryTheory.ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, v} X) A
        J) :=
  let F := SheafOfModules.strictPerfectConstantSheaf (coefficientProEtaleModelTopology.{u, v} X) A ⋙
    SheafOfModules.restrictScalars
      (CategoryTheory.constantModuleHomRingIso (coefficientProEtaleModelTopology.{u, v} X) A).inv ⋙
    CategoryTheory.ConstantCompletion.change
      (CategoryTheory.ConstantCompletion.coefficientMap (coefficientProEtaleModelTopology.{u, v}
        X) A J)
  (CategoryTheory.ConstantCompletion.Q
    (CategoryTheory.ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, v} X) A
      J)).obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)

/-- Cohomology in the standard localization used by the coefficient package.
Source: Stacks Tag 05RU (blueprint: lem-sfb-adic-residue-lisse-perfect-lift). -/
abbrev adicResidueCohomology {D : Type w} [SmallCategory D]
    {T : GrothendieckTopology D} (R : Sheaf T CommRingCat.{w}) (q : ℤ) :
    CategoryTheory.ConstantCompletion.D R ⥤ CategoryTheory.ConstantCompletion.Mod R :=
  @DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) q

/-- Exact restriction to the actual localized site, at the same standard localization.
Source: Stacks Tag 03DJ (blueprint: lem-sfb-adic-residue-lisse-perfect-lift). -/
def adicResidueRestriction {D : Type w} [SmallCategory D]
    {T : GrothendieckTopology D} (R : Sheaf T CommRingCat.{w}) (U : D) :
    CategoryTheory.ConstantCompletion.D R ⥤ CategoryTheory.ConstantCompletion.D (R.over U) :=
  letI := HasDerivedCategory.standard (CategoryTheory.ConstantCompletion.Mod R)
  letI := HasDerivedCategory.standard (CategoryTheory.ConstantCompletion.Mod (R.over U))
  CategoryTheory.ringedDerivedRestriction R U

/-- Cohomology of the existing total tensor with a module in degree zero.
With a K-flat first factor this is precisely the derived Tor test.
Source: Stacks Tags 06YS and 09C6
(blueprint: lem-sfb-adic-residue-lisse-perfect-lift). -/
def adicResidueTensorCohomology {D : Type w} [SmallCategory D]
    {T : GrothendieckTopology D} (R : Sheaf T CommRingCat.{w})
    (P : CategoryTheory.ConstantCompletion.Cx R)
    (N : CategoryTheory.ConstantCompletion.Mod R) (q : ℤ) :
    CategoryTheory.ConstantCompletion.Mod R :=
  (((CategoryTheory.ringedKoszulTensor R).obj P).obj
    ((HomologicalComplex.single (CategoryTheory.ConstantCompletion.Mod R)
      (ComplexShape.up ℤ) 0).obj N)).homology q
```

## New

These definitions are textually identical in AdicResidueLiftComparisons.lean. The assigned
module reexports them with public import Sheaf.Paper.AdicResidueLiftComparisons.
The companion additionally constructs adicResidueLocalProjection, AdicResidueLocalDerived,
adicResidueLocalReduction, adicResidueLocalReductionStep, adicResidueHomStep,
adicResidueHomTower, adicResidueHomSection and AdicResidueSliceWeaklyContractible.
No definition has admitted fields. Scalar reassociation is normalized by balancing;
the compatible section uses its inverse naturality square.
The new source lemmas have their complete signatures in their DAG Lean records.

## Users

The read-only downstream query with --allow-missing reports zero current importers and
zero uses of each moved name. Text searches of the live Lean trees and quarantine find
the six names only in the assigned archive. This is restoration: the unfinished DAG parent
lem-sfb-adic-stratified-perfect still depends on the item, and that edge and the unit route
are retained. No other group's module is adapted. All delivery consumers follow.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicResidueLissePerfectLift | C4 | Restore exact theorem; reexport unchanged definitions; complete combining proof. |
| Sheaf.Paper.AdicResidueLiftComparisons | C4, new | Own coefficient definitions and actual normalized Hom tower. |
| Sheaf.Paper.AdicResidueFiniteLocalModels | C4, new | State finite models on covering objects with restriction to sieve refinements. |
| Sheaf.Paper.AdicPerfectReductionHomML | C4, new | State ML for Hom from the fixed completed constant perfect source. |
| Sheaf.Paper.AdicCompleteReductionCone | C4, new | State quotient cone with actual scalar adjunction units. |
| Sheaf.Paper.AdicCompleteHomSections | C4, new | Prove compatible-section lifting from the normalized cone. |
| Sheaf.Paper.AdicCompleteResidueConservative | C4, new | State residue conservativity on the same slice. |

## Status

landed 20261021T022430-L-2846381 2026-10-21 (merge of deliver/C4/Sheaf.Paper.AdicResidueLissePerfectLift)
