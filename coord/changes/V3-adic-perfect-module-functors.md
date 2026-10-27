# adicPerfectLocalFunctor, adicPerfectQuotientFunctor, adicPerfectQuotientModuleStep

## Reason

Extract the existing functor definitions and their additive instances to the new module
`Sheaf.Paper.AdicPerfectModuleFunctors`. This lets the rank-one comparison theorem import
the definitions without creating an import cycle through the original comparison theorem.
The original module publicly imports the new module, preserving every existing user.
There is no mathematical definition or statement change, including for target statements.
The three public names, signatures, bodies and instances are preserved verbatim.

## Old

In `Sheaf.Paper.AdicPerfectModuleHom`:

```lean
def adicPerfectLocalFunctor (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) :
    ModuleCat.{max v (u + 1)} A ⥤
      Mod ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U) :=
  SheafOfModules.strictPerfectConstantSheaf
      (coefficientProEtaleModelTopology.{u, v} X) A ⋙
    SheafOfModules.restrictScalars
      (constantModuleHomRingIso (coefficientProEtaleModelTopology.{u, v} X) A).inv ⋙
    change (coefficientMap (coefficientProEtaleModelTopology.{u, v} X) A J) ⋙
    SheafOfModules.overFunctor _ U

instance (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) :
    (adicPerfectLocalFunctor X J U).Additive := by
  exact inferInstanceAs
    ((SheafOfModules.strictPerfectConstantSheaf
        (coefficientProEtaleModelTopology.{u, v} X) A ⋙
      SheafOfModules.restrictScalars
        (constantModuleHomRingIso (coefficientProEtaleModelTopology.{u, v} X) A).inv ⋙
      change (coefficientMap (coefficientProEtaleModelTopology.{u, v} X) A J) ⋙
      SheafOfModules.overFunctor _ U).Additive)

/-- The ordinary quotient realization on modules, with its actual scalar ring.
Source: Stacks Tag 09C6 (blueprint: lem-sfb-adic-perfect-module-hom). -/
def adicPerfectQuotientFunctor (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ) :
    ModuleCat.{max v (u + 1)} A ⥤
      Mod ((finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U) :=
  adicPerfectLocalFunctor X J U ⋙ change (adicResidueLocalProjection X J U n)

instance (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ) :
    (adicPerfectQuotientFunctor X J U n).Additive := by
  have := change_additive (adicResidueLocalProjection X J U n)
  unfold adicPerfectQuotientFunctor
  infer_instance

/-- The ordinary module balancing isomorphism at a successor level.
Source: Stacks Tags 06YY and 09C6 (blueprint: lem-sfb-adic-perfect-module-hom). -/
def adicPerfectQuotientModuleStep (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ) :
    adicPerfectQuotientFunctor X J U (n + 1) ⋙
        change (adicPerfectQuotientScalarStep X J U n) ≅
      adicPerfectQuotientFunctor X J U n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (adicPerfectLocalFunctor X J U)
      (adicFiniteChangeComp (adicResidueLocalProjection X J U (n + 1))
        (adicPerfectQuotientScalarStep X J U n) ≪≫
          eqToIso (congrArg change (adicPerfectQuotientScalarStep_comp X J U n)))
```

## New

In `Sheaf.Paper.AdicPerfectModuleFunctors`, reexported by the old module:

```lean
def adicPerfectLocalFunctor (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) :
    ModuleCat.{max v (u + 1)} A ⥤
      Mod ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U) :=
  SheafOfModules.strictPerfectConstantSheaf
      (coefficientProEtaleModelTopology.{u, v} X) A ⋙
    SheafOfModules.restrictScalars
      (constantModuleHomRingIso (coefficientProEtaleModelTopology.{u, v} X) A).inv ⋙
    change (coefficientMap (coefficientProEtaleModelTopology.{u, v} X) A J) ⋙
    SheafOfModules.overFunctor _ U

instance (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) :
    (adicPerfectLocalFunctor X J U).Additive := by
  exact inferInstanceAs
    ((SheafOfModules.strictPerfectConstantSheaf
        (coefficientProEtaleModelTopology.{u, v} X) A ⋙
      SheafOfModules.restrictScalars
        (constantModuleHomRingIso (coefficientProEtaleModelTopology.{u, v} X) A).inv ⋙
      change (coefficientMap (coefficientProEtaleModelTopology.{u, v} X) A J) ⋙
      SheafOfModules.overFunctor _ U).Additive)

/-- The ordinary quotient realization on modules, with its actual scalar ring.
Source: Stacks Tag 09C6 (blueprint: def-sfb-adic-perfect-module-functors). -/
def adicPerfectQuotientFunctor (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ) :
    ModuleCat.{max v (u + 1)} A ⥤
      Mod ((finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U) :=
  adicPerfectLocalFunctor X J U ⋙ change (adicResidueLocalProjection X J U n)

instance (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ) :
    (adicPerfectQuotientFunctor X J U n).Additive := by
  have := change_additive (adicResidueLocalProjection X J U n)
  unfold adicPerfectQuotientFunctor
  infer_instance

/-- The ordinary module balancing isomorphism at a successor level.
Source: Stacks Tags 06YY and 09C6 (blueprint: def-sfb-adic-perfect-module-functors). -/
def adicPerfectQuotientModuleStep (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ) :
    adicPerfectQuotientFunctor X J U (n + 1) ⋙
        change (adicPerfectQuotientScalarStep X J U n) ≅
      adicPerfectQuotientFunctor X J U n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (adicPerfectLocalFunctor X J U)
      (adicFiniteChangeComp (adicResidueLocalProjection X J U (n + 1))
        (adicPerfectQuotientScalarStep X J U n) ≪≫
          eqToIso (congrArg change (adicPerfectQuotientScalarStep_comp X J U n)))
```

## Users

The table includes the transitive downstream modules reported by `tools/downstream.py`
for the three moved names. Only `AdicPerfectHomCochains` directly imports the item;
no consumer needs adaptation. The other modules retain their import and definition paths.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicPerfectModuleHom | V3 | Definitions move to a publicly imported module; theorem signature unchanged. |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | unclaimed | Same declarations, signatures and bodies; reexported from the item. |
| Sheaf.Paper.AdicConstructibleLocalModels | unclaimed | Same declarations, signatures and bodies; reexported from the item. |
| Sheaf.Paper.AdicPerfectHomCochains | unclaimed | Direct importer; compiled unchanged against the extraction. |
| Sheaf.Paper.AdicPerfectHomCohomologyComparison | unclaimed | Same declarations, signatures and bodies; reexported from the item. |
| Sheaf.Paper.AdicPerfectModelHomCohomology | unclaimed | Same declarations, signatures and bodies; reexported from the item. |
| Sheaf.Paper.AdicPerfectReductionHomML | unclaimed | Same declarations, signatures and bodies; reexported from the item. |
| Sheaf.Paper.AdicResidueLissePerfectLift | unclaimed | Same declarations, signatures and bodies; reexported from the item. |
| Sheaf.Paper.AdicStratifiedPerfect | unclaimed | Same declarations, signatures and bodies; reexported from the item. |
| Sheaf.Paper.CompleteResidueLineInverse | A7 | Same declarations, signatures and bodies; reexported from the item. |
| Sheaf.Paper.GeneralLfpAdicInputWitness | unclaimed | Same declarations, signatures and bodies; reexported from the item. |
| Sheaf.Paper.IntegralCohomologicalAdicCriterion | unclaimed | Same declarations, signatures and bodies; reexported from the item. |
| Sheaf.Paper.IntegralHeartConstructibleModuleComplete | unclaimed | Same declarations, signatures and bodies; reexported from the item. |
| Sheaf.Paper.IntegralHeartProjectiveLocalModels | unclaimed | Same declarations, signatures and bodies; reexported from the item. |

## Status

landed 20261026T092913-L-3478464 2026-10-26 (merge of deliver/V3/Sheaf.Paper.AdicPerfectModuleHom)
