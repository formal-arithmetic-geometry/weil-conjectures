# CategoryTheory.localizationModules and the localization-model interface

## Reason

The main theorem needs both natural currying and further-restriction comparisons.
These constructions must use the model definitions without importing the main theorem
and making an import cycle. Extract the existing public model interface, unchanged,
into `Sheaf.Paper.RingedLocalizationModels`, and publicly reexport it from the original
module. The old K-flat-model and product-localization theorems move with the interface;
their signatures stay identical. The existing coefficient K-flat subproof is exposed as
`localizationSliceCoefficient_kflat` and reused in the old K-flat-model proof.

Every existing definition below is textually identical before and after the move.
No target signature, mathematical definition or public visibility changes. No target's
meaning changes, so this layout change requires no new target statement review.

## Old

In `lean/Sheaf/Paper/RingedLocalizationRHomCalculus.lean`:

```lean
abbrev localizationModules (R : Sheaf J CommRingCat.{u}) :=
  ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

/-- The existing unbounded derived category, at its standard localization size.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationDerived (R : Sheaf J CommRingCat.{u}) :=
  @DerivedCategory (localizationModules R) _ _
    (HasDerivedCategory.standard (localizationModules R))

/-- The existing localization functor with the same size convention.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationQ (R : Sheaf J CommRingCat.{u}) :
    CochainComplex (localizationModules R) ℤ ⥤ localizationDerived R :=
  @DerivedCategory.Q (localizationModules R) _ _
    (HasDerivedCategory.standard (localizationModules R))

/-- The recorded derived internal Hom; this is only an explicit universe specialization.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationRHom (R : Sheaf J CommRingCat.{u}) :
    (localizationDerived R)ᵒᵖ × localizationDerived R ⥤ localizationDerived R :=
  @derivedInternalHom C _ J R (HasDerivedCategory.standard (localizationModules R))

/-- Termwise slice restriction using the recorded exact restriction functor.
Source: Stacks 08JB (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationComplexRestriction (R : Sheaf J CommRingCat.{u}) (U : C) :
    CochainComplex (localizationModules R) ℤ ⥤
      CochainComplex (localizationModules (R.over U)) ℤ :=
  (SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).mapHomologicalComplex (.up ℤ)

/-- The induced exact functor on derived categories, with explicit standard sizes.
Source: Stacks 08JB (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationDerivedRestriction (R : Sheaf J CommRingCat.{u}) (U : C) :
    localizationDerived R ⥤ localizationDerived (R.over U) :=
  haveI := ringedSite_overFunctor_additive J R U
  haveI := ringedSite_overFunctor_limits J R U
  haveI := ringedSite_overFunctor_colimits J R U
  @Functor.mapDerivedCategory
    (localizationModules R) _ _ (HasDerivedCategory.standard (localizationModules R))
    (localizationModules (R.over U)) _ _
    (HasDerivedCategory.standard (localizationModules (R.over U)))
    (SheafOfModules.overFunctor.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U) _ _ _

/-- A bounded complex with finite localization sums in every degree. The empty sum is allowed.
Source: Stacks 0996, localization specialization of 08J9
(blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
def IsBoundedLocalizationComplex (R : Sheaf J CommRingCat.{u})
    (P : CochainComplex (localizationModules R) ℤ) : Prop :=
  (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
    ∀ n : ℤ, ∃ (k : ℕ) (g : Fin k → (R.obj ⋙ forget CommRingCat.{u}).sections),
      Nonempty (P.X n ≅ ∐ (fun i : Fin k ↦ ringedSectionLocalization R (g i)))

/-- Ordinary tensor by a sheaf in degree zero: terms and differentials are tensorized.
Source: Stacks 0996, 08J9
(blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
def localizationTensorComplex (R : Sheaf J CommRingCat.{u}) (S : localizationModules R) :
    CochainComplex (localizationModules R) ℤ ⥤
      CochainComplex (localizationModules R) ℤ :=
  haveI := SheafOfModules.monoidalCategory R
  haveI := Classical.choice (SheafOfModules.tensorClosed R).1
  (@tensorLeft (localizationModules R) _
    (SheafOfModules.monoidalCategory R) S).mapHomologicalComplex
    (.up ℤ)

/-- The actual coefficient localization on the slice, using the recorded fraction presheaf.
Source: Stacks 0996 (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationSliceCoefficient (R : Sheaf J CommRingCat.{u}) (U : C)
    (f : R.obj.obj (op U)) : localizationModules (R.over U) :=
  ringedSectionLocalization (R.over U) (ringedSliceSection R U f)

/-- The ordinary localized complex P_f, including its tensor differential.
Source: Stacks 0996, 08J9
(blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationSliceComplex (R : Sheaf J CommRingCat.{u}) (U : C)
    (f : R.obj.obj (op U)) :
    CochainComplex (localizationModules R) ℤ ⥤
      CochainComplex (localizationModules (R.over U)) ℤ :=
  localizationComplexRestriction R U ⋙
    localizationTensorComplex (R.over U) (localizationSliceCoefficient R U f)

/-- The coefficient localization regarded as an object of the unbounded derived category.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationSliceDerivedCoefficient (R : Sheaf J CommRingCat.{u}) (U : C)
    (f : R.obj.obj (op U)) : localizationDerived (R.over U) :=
  (localizationQ (R.over U)).obj
    ((HomologicalComplex.single (localizationModules (R.over U)) (.up ℤ) 0).obj
      (localizationSliceCoefficient R U f))

/-- Further slice restriction on the same existing derived categories.
Source: Stacks 08JB (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationDerivedOverMap (R : Sheaf J CommRingCat.{u}) {U V : C} (a : V ⟶ U) :
    localizationDerived (R.over U) ⥤ localizationDerived (R.over V) :=
  haveI := ringedSite_overMap_additive J R a
  haveI := ringedSite_overMap_limits J R a
  haveI := ringedSite_overMap_colimits J R a
  @Functor.mapDerivedCategory
    (localizationModules (R.over U)) _ _
    (HasDerivedCategory.standard (localizationModules (R.over U)))
    (localizationModules (R.over V)) _ _
    (HasDerivedCategory.standard (localizationModules (R.over V)))
    (SheafOfModules.overMap.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) a) _ _ _

/-- The canonical relocalization comparison, induced by the sectionwise identity.
Source: Stacks 08JB, Modules on Sites 04IX
(blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
def localizationRestrictionCompIso (R : Sheaf J CommRingCat.{u}) {U V : C} (a : V ⟶ U) :
    localizationDerivedRestriction R U ⋙ localizationDerivedOverMap R a ≅
      localizationDerivedRestriction R V :=
  haveI := HasDerivedCategory.standard (localizationModules R)
  haveI := HasDerivedCategory.standard (localizationModules (R.over U))
  haveI := HasDerivedCategory.standard (SheafOfModules.{u}
    (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over U))
  haveI := HasDerivedCategory.standard (localizationModules (R.over V))
  haveI := HasDerivedCategory.standard (SheafOfModules.{u}
    (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over V))
  haveI := ringedSite_overFunctor_additive J R U
  haveI := ringedSite_overFunctor_limits J R U
  haveI := ringedSite_overFunctor_colimits J R U
  haveI := ringedSite_overFunctor_additive J R V
  haveI := ringedSite_overFunctor_limits J R V
  haveI := ringedSite_overFunctor_colimits J R V
  haveI := ringedSite_overMap_additive J R a
  haveI := ringedSite_overMap_limits J R a
  haveI := ringedSite_overMap_colimits J R a
  (@Functor.mapDerivedCategoryCompIso
    (localizationModules R) (localizationModules (R.over U)) (localizationModules (R.over V))
    _ _ _ _ _ _
    (HasDerivedCategory.standard (localizationModules R))
    (HasDerivedCategory.standard (localizationModules (R.over U)))
    (HasDerivedCategory.standard (localizationModules (R.over V)))
    (SheafOfModules.overFunctor.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U)
    (SheafOfModules.overMap.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) a) _ _ _ _ _ _).symm ≪≫
    @Functor.mapDerivedCategoryNatIso
      (localizationModules R) (localizationModules (R.over V)) _ _ _ _
      (HasDerivedCategory.standard (localizationModules R))
      (HasDerivedCategory.standard (localizationModules (R.over V))) _ _ _ _ _ _ _ _
      (SheafOfModules.overFunctorMap
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) a)
```

The two existing theorem signatures and the main signature are retained verbatim in
the new source files. The first two move to the models module; the main theorem stays.

## New

In `lean/Sheaf/Paper/RingedLocalizationRHomCalculus.lean`:

```lean
public import Sheaf.Paper.RingedLocalizationModels
```

In `lean/Sheaf/Paper/RingedLocalizationModels.lean`, the same definitions:

```lean
abbrev localizationModules (R : Sheaf J CommRingCat.{u}) :=
  ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

/-- The existing unbounded derived category, at its standard localization size.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationDerived (R : Sheaf J CommRingCat.{u}) :=
  @DerivedCategory (localizationModules R) _ _
    (HasDerivedCategory.standard (localizationModules R))

/-- The existing localization functor with the same size convention.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationQ (R : Sheaf J CommRingCat.{u}) :
    CochainComplex (localizationModules R) ℤ ⥤ localizationDerived R :=
  @DerivedCategory.Q (localizationModules R) _ _
    (HasDerivedCategory.standard (localizationModules R))

/-- The recorded derived internal Hom; this is only an explicit universe specialization.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationRHom (R : Sheaf J CommRingCat.{u}) :
    (localizationDerived R)ᵒᵖ × localizationDerived R ⥤ localizationDerived R :=
  @derivedInternalHom C _ J R (HasDerivedCategory.standard (localizationModules R))

/-- Termwise slice restriction using the recorded exact restriction functor.
Source: Stacks 08JB (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationComplexRestriction (R : Sheaf J CommRingCat.{u}) (U : C) :
    CochainComplex (localizationModules R) ℤ ⥤
      CochainComplex (localizationModules (R.over U)) ℤ :=
  (SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).mapHomologicalComplex (.up ℤ)

/-- The induced exact functor on derived categories, with explicit standard sizes.
Source: Stacks 08JB (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationDerivedRestriction (R : Sheaf J CommRingCat.{u}) (U : C) :
    localizationDerived R ⥤ localizationDerived (R.over U) :=
  haveI := ringedSite_overFunctor_additive J R U
  haveI := ringedSite_overFunctor_limits J R U
  haveI := ringedSite_overFunctor_colimits J R U
  @Functor.mapDerivedCategory
    (localizationModules R) _ _ (HasDerivedCategory.standard (localizationModules R))
    (localizationModules (R.over U)) _ _
    (HasDerivedCategory.standard (localizationModules (R.over U)))
    (SheafOfModules.overFunctor.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U) _ _ _

/-- A bounded complex with finite localization sums in every degree. The empty sum is allowed.
Source: Stacks 0996, localization specialization of 08J9
(blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
def IsBoundedLocalizationComplex (R : Sheaf J CommRingCat.{u})
    (P : CochainComplex (localizationModules R) ℤ) : Prop :=
  (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
    ∀ n : ℤ, ∃ (k : ℕ) (g : Fin k → (R.obj ⋙ forget CommRingCat.{u}).sections),
      Nonempty (P.X n ≅ ∐ (fun i : Fin k ↦ ringedSectionLocalization R (g i)))

/-- Ordinary tensor by a sheaf in degree zero: terms and differentials are tensorized.
Source: Stacks 0996, 08J9
(blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
def localizationTensorComplex (R : Sheaf J CommRingCat.{u}) (S : localizationModules R) :
    CochainComplex (localizationModules R) ℤ ⥤
      CochainComplex (localizationModules R) ℤ :=
  haveI := SheafOfModules.monoidalCategory R
  haveI := Classical.choice (SheafOfModules.tensorClosed R).1
  (@tensorLeft (localizationModules R) _
    (SheafOfModules.monoidalCategory R) S).mapHomologicalComplex
    (.up ℤ)

/-- The actual coefficient localization on the slice, using the recorded fraction presheaf.
Source: Stacks 0996 (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationSliceCoefficient (R : Sheaf J CommRingCat.{u}) (U : C)
    (f : R.obj.obj (op U)) : localizationModules (R.over U) :=
  ringedSectionLocalization (R.over U) (ringedSliceSection R U f)

/-- The ordinary localized complex P_f, including its tensor differential.
Source: Stacks 0996, 08J9
(blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationSliceComplex (R : Sheaf J CommRingCat.{u}) (U : C)
    (f : R.obj.obj (op U)) :
    CochainComplex (localizationModules R) ℤ ⥤
      CochainComplex (localizationModules (R.over U)) ℤ :=
  localizationComplexRestriction R U ⋙
    localizationTensorComplex (R.over U) (localizationSliceCoefficient R U f)

/-- The coefficient localization regarded as an object of the unbounded derived category.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationSliceDerivedCoefficient (R : Sheaf J CommRingCat.{u}) (U : C)
    (f : R.obj.obj (op U)) : localizationDerived (R.over U) :=
  (localizationQ (R.over U)).obj
    ((HomologicalComplex.single (localizationModules (R.over U)) (.up ℤ) 0).obj
      (localizationSliceCoefficient R U f))

/-- Further slice restriction on the same existing derived categories.
Source: Stacks 08JB (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationDerivedOverMap (R : Sheaf J CommRingCat.{u}) {U V : C} (a : V ⟶ U) :
    localizationDerived (R.over U) ⥤ localizationDerived (R.over V) :=
  haveI := ringedSite_overMap_additive J R a
  haveI := ringedSite_overMap_limits J R a
  haveI := ringedSite_overMap_colimits J R a
  @Functor.mapDerivedCategory
    (localizationModules (R.over U)) _ _
    (HasDerivedCategory.standard (localizationModules (R.over U)))
    (localizationModules (R.over V)) _ _
    (HasDerivedCategory.standard (localizationModules (R.over V)))
    (SheafOfModules.overMap.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) a) _ _ _

/-- The canonical relocalization comparison, induced by the sectionwise identity.
Source: Stacks 08JB, Modules on Sites 04IX
(blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
def localizationRestrictionCompIso (R : Sheaf J CommRingCat.{u}) {U V : C} (a : V ⟶ U) :
    localizationDerivedRestriction R U ⋙ localizationDerivedOverMap R a ≅
      localizationDerivedRestriction R V :=
  haveI := HasDerivedCategory.standard (localizationModules R)
  haveI := HasDerivedCategory.standard (localizationModules (R.over U))
  haveI := HasDerivedCategory.standard (SheafOfModules.{u}
    (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over U))
  haveI := HasDerivedCategory.standard (localizationModules (R.over V))
  haveI := HasDerivedCategory.standard (SheafOfModules.{u}
    (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over V))
  haveI := ringedSite_overFunctor_additive J R U
  haveI := ringedSite_overFunctor_limits J R U
  haveI := ringedSite_overFunctor_colimits J R U
  haveI := ringedSite_overFunctor_additive J R V
  haveI := ringedSite_overFunctor_limits J R V
  haveI := ringedSite_overFunctor_colimits J R V
  haveI := ringedSite_overMap_additive J R a
  haveI := ringedSite_overMap_limits J R a
  haveI := ringedSite_overMap_colimits J R a
  (@Functor.mapDerivedCategoryCompIso
    (localizationModules R) (localizationModules (R.over U)) (localizationModules (R.over V))
    _ _ _ _ _ _
    (HasDerivedCategory.standard (localizationModules R))
    (HasDerivedCategory.standard (localizationModules (R.over U)))
    (HasDerivedCategory.standard (localizationModules (R.over V)))
    (SheafOfModules.overFunctor.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U)
    (SheafOfModules.overMap.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) a) _ _ _ _ _ _).symm ≪≫
    @Functor.mapDerivedCategoryNatIso
      (localizationModules R) (localizationModules (R.over V)) _ _ _ _
      (HasDerivedCategory.standard (localizationModules R))
      (HasDerivedCategory.standard (localizationModules (R.over V))) _ _ _ _ _ _ _ _
      (SheafOfModules.overFunctorMap
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) a)
```

The new coefficient K-flat theorem extracts the old second conjunct's proof. Its only
consumer inside the old interface is `ringedLocalization_kflat_models`; the two new
currying constructions also use this certificate. No existing signature changes.

## Users

`python3 tools/downstream.py Sheaf.Paper.RingedLocalizationRHomCalculus` reports the
following full downstream set at the time of this delivery. These modules require no
edits. Original consumer compilation against the extracted interface is recorded in
report.md. The new support modules and their DAG records are included in this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.RingedKoszulCompletionReflector | unassigned in queue snapshot; no edit | Same declarations, definitions, visibility and signatures through the public reexport; no adaptation. |
| Sheaf.CategoryTheory.RingedSiteCompleteElementMul | unassigned in queue snapshot; no edit | Same declarations, definitions, visibility and signatures through the public reexport; no adaptation. |
| Sheaf.CategoryTheory.RingedSiteCompleteElementsIdeal | unassigned in queue snapshot; no edit | Same declarations, definitions, visibility and signatures through the public reexport; no adaptation. |
| Sheaf.Paper.ExtendedCechCompletionModel | unassigned in queue snapshot; no edit | Same declarations, definitions, visibility and signatures through the public reexport; no adaptation. |
| Sheaf.Paper.FlatRingedIdealCompleteEquivalence | unassigned in queue snapshot; no edit | Same declarations, definitions, visibility and signatures through the public reexport; no adaptation. |
| Sheaf.Paper.RestrictionLocalCompleteness | unassigned in queue snapshot; no edit | Same declarations, definitions, visibility and signatures through the public reexport; no adaptation. |

## Status

landed 20261018T101338-L-3972963 2026-10-18 (merge of deliver/W3/Sheaf.Paper.RingedLocalizationRHomCalculus)
