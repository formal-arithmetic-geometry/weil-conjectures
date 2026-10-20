# adicDatumReduction and its elaboration interfaces

## Reason

The inferred reduction type retains completedConstantDerived/completedConstantModules
metadata, while geometric pullback uses the proEtaleRingModules derived category.
Comparing competing Abelian and derived-category instances unfolds large choices.
An explicit return type retains the existing functor with the geometric category
interface. Explicit universe arguments and unfolding the selected definitions
before elaborating the existing counit and tensor-section terms prevent the same
problem in those constructors. No chosen object or normalization changes.

The public ProEtaleOperations import supplies the names in the explicit signature;
import_direction.py confirms acyclicity. The generic adicDatumSiteModulesAbelian helper leaves the site variable in
coefficient-universe proof applications, avoiding nested proof auxiliary constants
for the entire sheafification criterion. The shared adicDatumModulesAbelian
abbreviation specializes that same constructed Mathlib Abelian instance and selects the existing geometric Abelian structure, using the coefficient-universe
sheafification and locally-bijective proofs. Local preferences start at
adicDatumReduction, leaving the earlier coefficient-data inference context unchanged.
The other affected modules select this same Abelian structure and the geometric
proEtaleRingModules_hasDerivedCategory instance, whose value is the standard
localization. No global instance priority changes.

The sheafification criteria are Prop-valued, so proof irrelevance identifies their
proofs. The Abelian structure carries data, which is why a shared data abbreviation
is needed. Its body is the existing constructed Mathlib instance, with no new choice
from an unproved existence statement. Target signatures and meanings are unchanged;
the ordinary independent definition review still applies.

## Old

```lean
def adicDatumExtension :
    completedConstantDerived (completedConstantModules T R) ⥤
      completedConstantDerived (completedConstantModules T S) :=
  letI := HasDerivedCategory.standard (completedConstantModules T R)
  letI := HasDerivedCategory.standard (completedConstantModules T S)
  ((SheafOfModules.derivedChangeOfRingsIndependentCoefficients φ).choose_spec.choose_spec
    |>.choose_spec.choose_spec.2.2).choose
```

```lean
def adicDatumExtensionCounit :
    adicDatumQh T R ⋙ adicDatumExtension T φ ⟶
      (completedConstantExtension T φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        adicDatumQh T S :=
  letI := HasDerivedCategory.standard (completedConstantModules T R)
  letI := HasDerivedCategory.standard (completedConstantModules T S)
  ((SheafOfModules.derivedChangeOfRingsIndependentCoefficients φ).choose_spec.choose_spec
    |>.choose_spec.choose_spec.2.2).choose_spec.choose
```

```lean
def adicDatumTensorSection (M : completedConstantModules T R) (U : T.ProEtᵒᵖ)
    (s : S.obj.obj U) (m : M.val.obj U) :
    ((completedConstantExtension T φ).obj M).val.obj U :=
  letI := HasDerivedCategory.standard (completedConstantModules T R)
  letI := HasDerivedCategory.standard (completedConstantModules T S)
  letI : Module (R.obj.obj U) (S.obj.obj U) :=
    Module.compHom (S.obj.obj U) (φ.hom.app U).hom
  (eqToHom
    ((SheafOfModules.derivedChangeOfRingsIndependentCoefficients φ).choose_spec.choose M).symm)
      |>.val.app U
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((adicLisseForget T).obj S).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} φ M)).app U
          (s ⊗ₜ[R.obj.obj U] m))
```

```lean
def adicDatumReduction (n : ℕ) := adicDatumExtension T (adicDatumProjection T d n)
```

## New

```lean
abbrev adicDatumSiteModulesAbelian {B : Type (t + 1)} [Category.{t} B]
    [EssentiallySmall.{t + 1} B] (J : GrothendieckTopology B)
    (R : Sheaf J RingCat.{t + 1}) : Abelian (SheafOfModules.{t + 1} R) := inferInstance
```

```lean
abbrev adicDatumModulesAbelian (U : Scheme.{t})
    (R : Sheaf (ProEt.topology U) CommRingCat.{t + 1}) :
    Abelian (proEtaleRingModules U R) :=
  adicDatumSiteModulesAbelian (ProEt.topology U)
    ((sheafCompose (ProEt.topology U) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)

attribute [local instance 40000] adicDatumModulesAbelian
attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory
```

```lean
def adicDatumExtension :
    completedConstantDerived (completedConstantModules T R) ⥤
      completedConstantDerived (completedConstantModules T S) :=
  letI := HasDerivedCategory.standard (completedConstantModules T R)
  letI := HasDerivedCategory.standard (completedConstantModules T S)
  ((SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{t + 2, t + 1, t + 1, t}
      φ).choose_spec.choose_spec
    |>.choose_spec.choose_spec.2.2).choose
```

```lean
def adicDatumExtensionCounit :
    adicDatumQh T R ⋙ adicDatumExtension T φ ⟶
      (completedConstantExtension T φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        adicDatumQh T S := by
  letI := HasDerivedCategory.standard (completedConstantModules T R)
  letI := HasDerivedCategory.standard (completedConstantModules T S)
  unfold adicDatumQh adicDatumExtension completedConstantExtension
  exact ((SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{t + 2, t + 1, t + 1, t}
      φ).choose_spec.choose_spec
    |>.choose_spec.choose_spec.2.2).choose_spec.choose
```

```lean
def adicDatumTensorSection (M : completedConstantModules T R) (U : T.ProEtᵒᵖ)
    (s : S.obj.obj U) (m : M.val.obj U) :
    ((completedConstantExtension T φ).obj M).val.obj U := by
  letI := HasDerivedCategory.standard (completedConstantModules T R)
  letI := HasDerivedCategory.standard (completedConstantModules T S)
  letI : Module (R.obj.obj U) (S.obj.obj U) :=
    Module.compHom (S.obj.obj U) (φ.hom.app U).hom
  unfold completedConstantExtension
  exact (eqToHom
    ((SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{t + 2, t + 1, t + 1, t}
        φ).choose_spec.choose M).symm)
      |>.val.app U
    (((PresheafOfModules.sheafificationAdjunction.{t + 1}
      (𝟙 ((adicLisseForget T).obj S).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} φ M)).app U
          (s ⊗ₜ[R.obj.obj U] m))
```

```lean
def adicDatumReduction (n : ℕ) :
    DerivedCategory (proEtaleRingModules T (adicDatumRing T d)) ⥤
      DerivedCategory (proEtaleRingModules T
        ((adicLisseRingSystem T d.ideal).obj (op n))) :=
  adicDatumExtension T (adicDatumProjection T d n)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCoefficientDatumCompleted | unclaimed | Same data, explicit reduction interface and proof-instance priorities. |
| Sheaf.Paper.FiniteLevelRectangle | Q4 | Uses the explicit reduction interface in the mate cube. |
| Sheaf.Paper.FiniteReductionReconstructionCompleted | A2 | Existing reduction expressions retain the same type and value; original tested. |
| Sheaf.Paper.ProperBaseChangeFourArrows | unclaimed | Same maps, consistent local proof instances. |
| Sheaf.Paper.ProperBaseChangeFourCorners | unclaimed | Explicit comparison interface and consistent local proof instances. |
| Sheaf.Paper.FiniteReductionPullbackCoherence | new, Q4 | Uses the explicit reduction interface. |
| Sheaf.Paper.SequentialDerivedInverseLimitCompleted | unclaimed | Direct importer; original tested. |
| Sheaf.Paper.FiniteLevelRingedProEtaleBaseChange | unclaimed | Direct importer; original tested. |
| Sheaf.Paper.IntrinsicCompletionCompleted | unclaimed | Direct importer; original tested. |

The downstream.py --uses scan finds the first five existing modules above mentioning
adicDatumReduction. The other three existing modules are all direct importers. No
module held by another group is changed. The newer AdicCoefficientDatum is independent
of AdicCoefficientDatumCompleted, as checked by import_direction.py; no adaptation
of that separate API is needed. Compilation results are recorded in report.md.

## Status

landed 20261020T233213-L-905022 2026-10-20 (merge of deliver/Q4/Sheaf.Paper.FiniteLevelRectangle)
