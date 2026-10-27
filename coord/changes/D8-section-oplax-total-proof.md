# SectionTotalOplaxComparisonData: canonical tensor caches and explicit conjugation

## Reason

The proof of `section_oplax_total_comparison` must compare the specified tensor maps
on every coproduct injection. The original cochain instances and the five-factor
isomorphism composition cause repeated expansion of large monoidal structures.
Retain the canonical structures, cache their existing tensor-existence properties,
and give the conjugation an explicit record with its two maps and proved inverse laws.
No mathematical data, hypothesis, conclusion or target declaration changes.
The unclaimed data module is adapted; no adopted `WeilConjectures` source is edited.

The named ordinary monoidal alias remains defined, but its global instance registration
is removed so inference uses the canonical ordinary structure. The four signed cochain
aliases retain the canonical structures as explicitly reducible definitions. The six iterated-tensor
properties and two cochain-tensor properties are existing propositions proved by
instance inference. `totalTensorComparison` records the cochain type of the existing
uniquely normalized comparison, without choosing any new object.

`totalInternalOplax_eq` exports the already proved equality of the actual adjunction-mate
structure and the canonical composite. `sectionConjugationIso` explicitly stores the
forward and reverse paths; its two inverse laws and equality to the original composite
are fully proved. `conjugatedInternalTotalIso` uses that record and the explicitly typed
comparison. The section tensor isomorphism explicitly stores the cochain oplax map and
its lax inverse, with the two existing monoidal inverse laws. Its complete isomorphism
is equal to the original asIso comparison by Iso.ext and rfl. The actual internal tensor
and all unit constructors are retained. The three termwise functor aliases have explicit
types and reducible bodies equal to their original mapHomologicalComplex constructions.

The unchanged `TotalMapAgreement` definition is not reproduced below.
The two explicit module arguments in `SectionTotalNormalization` are recorded separately
in D8-total-normalization-module-arguments.md, with equality of the complete proposition. Any target whose
meaning depends on the modified data is reopened for the independent statement review.
The preservation checks concern the complete original structures and maps, not only
selected forward components. Validation status is recorded in `report.md`.

## Old

The original data module, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Sheaf.Paper.ProEtaleSectionModuleFunctors
public import Sheaf.Paper.SectionOrdinaryOplaxNormalization
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex

/-! # The actual internal total oplax arrow in section modules

Source: Stacks Project, Cohomology on Sites, Tag 07A4, displayed total comparison;
Modules on Sites, Tag 03EL (blueprint: def-pd-section-total-oplax-comparison-data).

All tensors are relative to the pulled-back coefficient ring. The totalization is the
existing signed direct-sum total, including its infinite degreewise sums. The helpers
name existing functors and canonical comparisons; the final proposition records their
specified-map equalities before and after homotopy quotient and localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
/-- The existing ordinary section tensor with its instance arguments retained.
Source: Stacks 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
instance totalSectionOrdinaryMonoidal (X : Scheme.{u}) :
    MonoidalCategory (modules Λ X) := inferInstance

/-- The existing graded tensor availability, retained as a compact instance.
Source: Stacks 07A4 (blueprint: def-pd-section-total-oplax-comparison-data). -/
instance totalInternalGraded (X : Scheme.{u})
    (P Q : GradedObject ℤ (internalModules Λ X)) : GradedObject.HasTensor P Q := inferInstance

/-- The existing graded tensor availability for section modules.
Source: Stacks 07A4 (blueprint: def-pd-section-total-oplax-comparison-data). -/
instance totalSectionGraded (X : Scheme.{u})
    (P Q : GradedObject ℤ (modules Λ X)) : GradedObject.HasTensor P Q := inferInstance

/-- The existing signed cochain tensor structure on internal modules.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
instance totalInternalMonoidal (X : Scheme.{u}) :
    MonoidalCategory (CochainComplex (internalModules Λ X) ℤ) := inferInstance

/-- The existing signed cochain tensor structure on section modules.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
instance totalSectionMonoidal (X : Scheme.{u}) :
    MonoidalCategory (CochainComplex (modules Λ X) ℤ) := inferInstance

/-- The existing internal cochain tensor data, with the same chosen structure.
Source: Stacks 07A4 (blueprint: def-pd-section-total-oplax-comparison-data). -/
@[instance_reducible] instance (priority := 3000) totalInternalMonoidalStruct
    (X : Scheme.{u}) : MonoidalCategoryStruct (CochainComplex (internalModules Λ X) ℤ) :=
  (totalInternalMonoidal Λ X).toMonoidalCategoryStruct

/-- The existing section cochain tensor data, with the same chosen structure.
Source: Stacks 07A4 (blueprint: def-pd-section-total-oplax-comparison-data). -/
@[instance_reducible] instance (priority := 3000) totalSectionMonoidalStruct
    (X : Scheme.{u}) : MonoidalCategoryStruct (CochainComplex (modules Λ X) ℤ) :=
  (totalSectionMonoidal Λ X).toMonoidalCategoryStruct

/-- The actual internal pullback applied termwise.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
abbrev totalInternalPull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (CondensedRing.upperStar Λ f).mapHomologicalComplex (.up ℤ)
/-- The specified ringed pullback applied termwise.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
abbrev totalSectionPull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (pullback Λ f).mapHomologicalComplex (.up ℤ)
/-- The fixed internal-section equivalence applied termwise.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
abbrev totalSectionEquivalence (X : Scheme.{u}) :=
  (equivalence Λ X).functor.mapHomologicalComplex (.up ℤ)
/-- The termwise lift of the fixed adjunction-mate operation comparison.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
@[irreducible] def termwisePullComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (internalModules Λ Y) ℤ) :
    (totalSectionEquivalence Λ X).obj ((totalInternalPull Λ f).obj P) ≅
      (totalSectionPull Λ f).obj ((totalSectionEquivalence Λ Y).obj P) :=
  (NatIso.mapHomologicalComplex (pullComparison Λ f) (.up ℤ)).app P

/-- The total of the actual internal adjunction-mate oplax map. Its inverse is the
summed lax map. The existing mapBifunctorComparison uses the canonical left-adjoint
coproduct comparison, and is the forward map of mapCochainComplexμIso.symm.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
@[irreducible] def actualInternalTotalIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (internalModules Λ Y) ℤ) :
    (totalInternalPull Λ f).obj (P ⊗ Q) ≅
      (totalInternalPull Λ f).obj P ⊗ (totalInternalPull Λ f).obj Q :=
  letI := CondensedRing.monoidal_upperStar Λ f
  asIso (HomologicalComplex.mapBifunctorComparison
    (Functor.OplaxMonoidal.δNatTrans (CondensedRing.upperStar Λ f)) (.up ℤ) P Q)

/-- The signed total of the specified ringed adjunction-mate tensor map. Its inverse
is the sum of the ordinary inverse maps, the construction used by the ringed
cochain comparison of lem-pur-cochain-pullback-tensor-coherence.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
@[irreducible] def sectionTotalIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (modules Λ Y) ℤ) :
    (totalSectionPull Λ f).obj (P ⊗ Q) ≅
      (totalSectionPull Λ f).obj P ⊗ (totalSectionPull Λ f).obj Q :=
  asIso (HomologicalComplex.mapBifunctorComparison
    (Functor.OplaxMonoidal.δNatTrans (pullback Λ f)) (.up ℤ) P Q)


set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] totalComparison ordinaryTensorComparison ordinaryUnitComparison

/-- Conjugate the actual internal total by the fixed operation and signed-total
comparisons. Both the source and target transports are explicit.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
@[irreducible] def conjugatedInternalTotalIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (internalModules Λ Y) ℤ) :
    (totalSectionPull Λ f).obj
        ((totalSectionEquivalence Λ Y).obj P ⊗ (totalSectionEquivalence Λ Y).obj Q) ≅
      (totalSectionPull Λ f).obj ((totalSectionEquivalence Λ Y).obj P) ⊗
        (totalSectionPull Λ f).obj ((totalSectionEquivalence Λ Y).obj Q) :=
  (totalSectionPull Λ f).mapIso (totalComparison Λ Y P Q).symm ≪≫
    (termwisePullComparison Λ f (P ⊗ Q)).symm ≪≫
    (totalSectionEquivalence Λ X).mapIso (actualInternalTotalIso Λ f P Q) ≪≫
    totalComparison Λ X ((totalInternalPull Λ f).obj P) ((totalInternalPull Λ f).obj Q) ≪≫
    tensorIso (termwisePullComparison Λ f P) (termwisePullComparison Λ f Q)

/-- The fixed equivalence on the ring complex in degree zero.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
@[irreducible] def totalUnitComparison (X : Scheme.{u}) :
    (totalSectionEquivalence Λ X).obj (𝟙_ (CochainComplex (internalModules Λ X) ℤ)) ≅
      𝟙_ (CochainComplex (modules Λ X) ℤ) :=
  (HomologicalComplex.singleMapHomologicalComplex (equivalence Λ X).functor (.up ℤ) 0).app
      (𝟙_ (internalModules Λ X)) ≪≫
    (HomologicalComplex.single (modules Λ X) (.up ℤ) 0).mapIso (ordinaryUnitComparison Λ X)

/-- The total internal unit, induced by the specified ordinary unit in degree zero.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
@[irreducible] def actualInternalTotalUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (totalInternalPull Λ f).obj (𝟙_ (CochainComplex (internalModules Λ Y) ℤ)) ⟶
      𝟙_ (CochainComplex (internalModules Λ X) ℤ) :=
  (HomologicalComplex.singleMapHomologicalComplex (CondensedRing.upperStar Λ f)
    (.up ℤ) 0).hom.app (𝟙_ (internalModules Λ Y)) ≫
    (HomologicalComplex.single (internalModules Λ X) (.up ℤ) 0).map
      (normalizationInternalUnit Λ f)

/-- The ringed total unit, induced by ordinary scalar multiplication in degree zero.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
@[irreducible] def sectionTotalUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (totalSectionPull Λ f).obj (𝟙_ (CochainComplex (modules Λ Y) ℤ)) ⟶
      𝟙_ (CochainComplex (modules Λ X) ℤ) :=
  (HomologicalComplex.singleMapHomologicalComplex (pullback Λ f) (.up ℤ) 0).hom.app
      (𝟙_ (modules Λ Y)) ≫
    (HomologicalComplex.single (modules Λ X) (.up ℤ) 0).map (normalizationSectionUnit Λ f)

/-- Conjugate the actual internal unit by the same fixed operation comparisons.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
def conjugatedInternalTotalUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (totalSectionPull Λ f).obj (𝟙_ (CochainComplex (modules Λ Y) ℤ)) ⟶
      𝟙_ (CochainComplex (modules Λ X) ℤ) :=
  (totalSectionPull Λ f).map (totalUnitComparison Λ Y).inv ≫
    (termwisePullComparison Λ f (𝟙_ (CochainComplex (internalModules Λ Y) ℤ))).inv ≫
    (totalSectionEquivalence Λ X).map (actualInternalTotalUnit Λ f) ≫
    (totalUnitComparison Λ X).hom

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
```

## New

The modified data module, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Sheaf.Paper.ProEtaleSectionModuleFunctors
public import Sheaf.Paper.SectionOrdinaryOplaxNormalization
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import all Sheaf.Paper.ProEtaleSectionModuleFunctors

/-! # The actual internal total oplax arrow in section modules

Source: Stacks Project, Cohomology on Sites, Tag 07A4, displayed total comparison;
Modules on Sites, Tag 03EL (blueprint: def-pd-section-total-oplax-comparison-data).

All tensors are relative to the pulled-back coefficient ring. The totalization is the
existing signed direct-sum total, including its infinite degreewise sums. The helpers
name existing functors and canonical comparisons; the final proposition records their
specified-map equalities before and after homotopy quotient and localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
/-- The existing ordinary section tensor with its instance arguments retained.
Source: Stacks 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
instance totalSectionOrdinaryMonoidal (X : Scheme.{u}) :
    MonoidalCategory (modules Λ X) := inferInstance

-- Use the canonical ordinary structure when constructing the cochain caches below.
attribute [-instance] totalSectionOrdinaryMonoidal

/-- The existing graded tensor availability, retained as a compact instance.
Source: Stacks 07A4 (blueprint: def-pd-section-total-oplax-comparison-data). -/
instance totalInternalGraded (X : Scheme.{u})
    (P Q : GradedObject ℤ (internalModules Λ X)) : GradedObject.HasTensor P Q := inferInstance

/-- The existing graded tensor availability for section modules.
Source: Stacks 07A4 (blueprint: def-pd-section-total-oplax-comparison-data). -/
instance totalSectionGraded (X : Scheme.{u})
    (P Q : GradedObject ℤ (modules Λ X)) : GradedObject.HasTensor P Q := inferInstance

/-- The existing canonical iterated tensor property, cached for termwise comparisons.
Source: Stacks 07A4 (blueprint: def-pd-section-total-oplax-comparison-data).
Proof: the ordinary tensor preserves the coproducts defining every graded tensor. -/
instance totalInternalGoodLeft (X : Scheme.{u})
    (P Q H : GradedObject ℤ (internalModules Λ X)) :
    GradedObject.HasGoodTensor₁₂Tensor P Q H := inferInstance

/-- The existing canonical iterated tensor property, cached for termwise comparisons.
Source: Stacks 07A4 (blueprint: def-pd-section-total-oplax-comparison-data).
Proof: the ordinary tensor preserves the coproducts defining every graded tensor. -/
instance totalInternalGoodRight (X : Scheme.{u})
    (P Q H : GradedObject ℤ (internalModules Λ X)) :
    GradedObject.HasGoodTensorTensor₂₃ P Q H := inferInstance

/-- The existing canonical iterated tensor property, cached for termwise comparisons.
Source: Stacks 07A4 (blueprint: def-pd-section-total-oplax-comparison-data).
Proof: the ordinary tensor preserves the coproducts defining every graded tensor. -/
instance totalInternalTensorFour (X : Scheme.{u})
    (P Q H K : GradedObject ℤ (internalModules Λ X)) :
    GradedObject.HasTensor₄ObjExt P Q H K := inferInstance

/-- The existing canonical iterated tensor property, cached for termwise comparisons.
Source: Stacks 07A4 (blueprint: def-pd-section-total-oplax-comparison-data).
Proof: the ordinary tensor preserves the coproducts defining every graded tensor. -/
instance totalSectionGoodLeft (X : Scheme.{u})
    (P Q H : GradedObject ℤ (modules Λ X)) :
    GradedObject.HasGoodTensor₁₂Tensor P Q H := inferInstance

/-- The existing canonical iterated tensor property, cached for termwise comparisons.
Source: Stacks 07A4 (blueprint: def-pd-section-total-oplax-comparison-data).
Proof: the ordinary tensor preserves the coproducts defining every graded tensor. -/
instance totalSectionGoodRight (X : Scheme.{u})
    (P Q H : GradedObject ℤ (modules Λ X)) :
    GradedObject.HasGoodTensorTensor₂₃ P Q H := inferInstance

/-- The existing canonical iterated tensor property, cached for termwise comparisons.
Source: Stacks 07A4 (blueprint: def-pd-section-total-oplax-comparison-data).
Proof: the ordinary tensor preserves the coproducts defining every graded tensor. -/
instance totalSectionTensorFour (X : Scheme.{u})
    (P Q H K : GradedObject ℤ (modules Λ X)) :
    GradedObject.HasTensor₄ObjExt P Q H K := inferInstance

/-- The existing canonical cochain tensor availability, retained without repeating
instance search through the termwise functors.
Source: Stacks 07A4 (blueprint: def-pd-section-total-oplax-comparison-data).
Proof: the graded coproducts defining the cochain tensor already exist. -/
instance (priority := 4000) totalInternalHasTensor (X : Scheme.{u})
    (P Q : CochainComplex (internalModules Λ X) ℤ) :
    HomologicalComplex.HasTensor P Q := inferInstance

/-- The existing canonical cochain tensor availability for section modules.
Source: Stacks 07A4 (blueprint: def-pd-section-total-oplax-comparison-data).
Proof: the graded coproducts defining the cochain tensor already exist. -/
instance (priority := 4000) totalSectionHasTensor (X : Scheme.{u})
    (P Q : CochainComplex (modules Λ X) ℤ) :
    HomologicalComplex.HasTensor P Q := inferInstance

/-- The existing signed cochain tensor structure on internal modules.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
@[reducible] def totalInternalMonoidal (X : Scheme.{u}) :
    MonoidalCategory (CochainComplex (internalModules Λ X) ℤ) :=
  HomologicalComplex.monoidalCategory (internalModules Λ X) (.up ℤ)

attribute [instance] totalInternalMonoidal

/-- The existing signed cochain tensor structure on section modules.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
@[reducible] def totalSectionMonoidal (X : Scheme.{u}) :
    MonoidalCategory (CochainComplex (modules Λ X) ℤ) :=
  HomologicalComplex.monoidalCategory (modules Λ X) (.up ℤ)

attribute [instance] totalSectionMonoidal

/-- The existing internal cochain tensor data, with the same chosen structure.
Source: Stacks 07A4 (blueprint: def-pd-section-total-oplax-comparison-data). -/
@[reducible] def totalInternalMonoidalStruct
    (X : Scheme.{u}) : MonoidalCategoryStruct (CochainComplex (internalModules Λ X) ℤ) :=
  HomologicalComplex.monoidalCategoryStruct (internalModules Λ X) (.up ℤ)

attribute [instance 3000] totalInternalMonoidalStruct

/-- The existing section cochain tensor data, with the same chosen structure.
Source: Stacks 07A4 (blueprint: def-pd-section-total-oplax-comparison-data). -/
@[reducible] def totalSectionMonoidalStruct
    (X : Scheme.{u}) : MonoidalCategoryStruct (CochainComplex (modules Λ X) ℤ) :=
  HomologicalComplex.monoidalCategoryStruct (modules Λ X) (.up ℤ)

attribute [instance 3000] totalSectionMonoidalStruct

/-- The actual mate oplax structure agrees with the canonical composite structure.
Source: the uniquely normalized direct image and its adjunction mate, Stacks 03EL.
Proof: the direct-image pairing is uniquely normalized on balanced generators; the
adjunction bijection transports its equality to equality of the oplax structures.
(blueprint: def-pd-section-total-oplax-comparison-data). -/
theorem totalInternalOplax_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    internalPullOplax Λ f = (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal :=
  internalPullOplax_eq_canonical Λ f

/-- The actual internal pullback applied termwise.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
@[reducible] def totalInternalPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CochainComplex (internalModules Λ Y) ℤ ⥤ CochainComplex (internalModules Λ X) ℤ :=
  (CondensedRing.upperStar Λ f).mapHomologicalComplex (.up ℤ)
/-- The specified ringed pullback applied termwise.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
@[reducible] def totalSectionPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CochainComplex (modules Λ Y) ℤ ⥤ CochainComplex (modules Λ X) ℤ :=
  (pullback Λ f).mapHomologicalComplex (.up ℤ)
/-- The fixed internal-section equivalence applied termwise.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
@[reducible] def totalSectionEquivalence (X : Scheme.{u}) :
    CochainComplex (internalModules Λ X) ℤ ⥤ CochainComplex (modules Λ X) ℤ :=
  (equivalence Λ X).functor.mapHomologicalComplex (.up ℤ)
/-- The specified total comparison, with its cochain tensor type recorded explicitly.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data).
This is the existing uniquely normalized comparison, with no new choice of data. -/
@[irreducible] def totalTensorComparison (X : Scheme.{u})
    (P Q : CochainComplex (internalModules Λ X) ℤ) :
    (totalSectionEquivalence Λ X).obj (P ⊗ Q) ≅
      (totalSectionEquivalence Λ X).obj P ⊗ (totalSectionEquivalence Λ X).obj Q :=
  totalComparison Λ X P Q

/-- The termwise lift of the fixed adjunction-mate operation comparison.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
@[irreducible] def termwisePullComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (internalModules Λ Y) ℤ) :
    (totalSectionEquivalence Λ X).obj ((totalInternalPull Λ f).obj P) ≅
      (totalSectionPull Λ f).obj ((totalSectionEquivalence Λ Y).obj P) :=
  (NatIso.mapHomologicalComplex (pullComparison Λ f) (.up ℤ)).app P

/-- The total of the actual internal adjunction-mate oplax map. Its inverse is the
summed lax map. The existing mapBifunctorComparison uses the canonical left-adjoint
coproduct comparison, and is the forward map of mapCochainComplexμIso.symm.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
@[irreducible] def actualInternalTotalIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (internalModules Λ Y) ℤ) :
    (totalInternalPull Λ f).obj (P ⊗ Q) ≅
      (totalInternalPull Λ f).obj P ⊗ (totalInternalPull Λ f).obj Q :=
  letI := CondensedRing.monoidal_upperStar Λ f
  asIso (HomologicalComplex.mapBifunctorComparison
    (Functor.OplaxMonoidal.δNatTrans (CondensedRing.upperStar Λ f)) (.up ℤ) P Q)

/-- The signed total of the specified ringed adjunction-mate tensor map. Its inverse
is the sum of the ordinary inverse maps, the construction used by the ringed
cochain comparison of lem-pur-cochain-pullback-tensor-coherence.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
@[irreducible] def sectionTotalIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (modules Λ Y) ℤ) :
    (totalSectionPull Λ f).obj (P ⊗ Q) ≅
      (totalSectionPull Λ f).obj P ⊗ (totalSectionPull Λ f).obj Q where
  hom := Functor.OplaxMonoidal.δ (totalSectionPull Λ f) P Q
  inv := Functor.LaxMonoidal.μ (totalSectionPull Λ f) P Q
  hom_inv_id := Functor.Monoidal.δ_μ (totalSectionPull Λ f) P Q
  inv_hom_id := Functor.Monoidal.μ_δ (totalSectionPull Λ f) P Q


set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] totalComparison ordinaryTensorComparison ordinaryUnitComparison

section ExplicitConjugation

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  (F : A ⥤ B) (G : C ⥤ B) {x y : A} {u v : C} {w t : B}
  (p : x ≅ y) (r : G.obj u ≅ F.obj x) (i : u ≅ v) (c : G.obj v ≅ w) (e : w ≅ t)

/-- The forward and reverse conjugation paths are inverse.
Source: the isomorphism laws, applied to the five factors of the total conjugation.
Proof: cancel e, c, G(i), r and F(p), in that order, using functoriality.
(blueprint: def-pd-section-total-oplax-comparison-data). -/
theorem sectionConjugation_hom_inv_id :
    (F.map p.inv ≫ r.inv ≫ G.map i.hom ≫ c.hom ≫ e.hom) ≫
      (e.inv ≫ c.inv ≫ G.map i.inv ≫ r.hom ≫ F.map p.hom) = 𝟙 _ := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← G.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_assoc, ← F.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id]

/-- The reverse and forward conjugation paths are inverse.
Source: the isomorphism laws, applied to the five factors of the total conjugation.
Proof: cancel F(p), r, G(i), c and e, in that order, using functoriality.
(blueprint: def-pd-section-total-oplax-comparison-data). -/
theorem sectionConjugation_inv_hom_id :
    (e.inv ≫ c.inv ≫ G.map i.inv ≫ r.hom ≫ F.map p.hom) ≫
      (F.map p.inv ≫ r.inv ≫ G.map i.hom ≫ c.hom ≫ e.hom) = 𝟙 _ := by
  simp only [Category.assoc, ← F.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.hom_inv_id_assoc, ← G.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_assoc, Iso.inv_hom_id]

/-- The same five-factor isomorphism with its two maps stored explicitly.
Source: the specified total conjugation in Stacks 07A4 and 03EL.
(blueprint: def-pd-section-total-oplax-comparison-data). -/
def sectionConjugationIso : F.obj y ≅ t where
  hom := F.map p.inv ≫ r.inv ≫ G.map i.hom ≫ c.hom ≫ e.hom
  inv := e.inv ≫ c.inv ≫ G.map i.inv ≫ r.hom ≫ F.map p.hom
  hom_inv_id := sectionConjugation_hom_inv_id F G p r i c e
  inv_hom_id := sectionConjugation_inv_hom_id F G p r i c e

/-- Equality with the original five-factor isomorphism composition.
Source: Stacks 07A4 and 03EL, the specified tensor comparison transport.
Proof: the forward maps are identical; an isomorphism is determined by its forward map.
(blueprint: def-pd-section-total-oplax-comparison-data). -/
theorem sectionConjugationIso_eq :
    sectionConjugationIso F G p r i c e =
      F.mapIso p.symm ≪≫ r.symm ≪≫ G.mapIso i ≪≫ c ≪≫ e := by
  apply Iso.ext
  rfl

end ExplicitConjugation

/-- Conjugate the actual internal total by the fixed operation and signed-total
comparisons. Both the source and target transports are explicit.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
@[irreducible] def conjugatedInternalTotalIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (internalModules Λ Y) ℤ) :
    (totalSectionPull Λ f).obj
        ((totalSectionEquivalence Λ Y).obj P ⊗ (totalSectionEquivalence Λ Y).obj Q) ≅
      (totalSectionPull Λ f).obj ((totalSectionEquivalence Λ Y).obj P) ⊗
        (totalSectionPull Λ f).obj ((totalSectionEquivalence Λ Y).obj Q) :=
  sectionConjugationIso (totalSectionPull Λ f) (totalSectionEquivalence Λ X)
    (totalTensorComparison Λ Y P Q) (termwisePullComparison Λ f (P ⊗ Q))
    (actualInternalTotalIso Λ f P Q)
    (totalTensorComparison Λ X ((totalInternalPull Λ f).obj P) ((totalInternalPull Λ f).obj Q))
    (tensorIso (termwisePullComparison Λ f P) (termwisePullComparison Λ f Q))

/-- The fixed equivalence on the ring complex in degree zero.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
@[irreducible] def totalUnitComparison (X : Scheme.{u}) :
    (totalSectionEquivalence Λ X).obj (𝟙_ (CochainComplex (internalModules Λ X) ℤ)) ≅
      𝟙_ (CochainComplex (modules Λ X) ℤ) :=
  (HomologicalComplex.singleMapHomologicalComplex (equivalence Λ X).functor (.up ℤ) 0).app
      (𝟙_ (internalModules Λ X)) ≪≫
    (HomologicalComplex.single (modules Λ X) (.up ℤ) 0).mapIso (ordinaryUnitComparison Λ X)

/-- The total internal unit, induced by the specified ordinary unit in degree zero.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
@[irreducible] def actualInternalTotalUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (totalInternalPull Λ f).obj (𝟙_ (CochainComplex (internalModules Λ Y) ℤ)) ⟶
      𝟙_ (CochainComplex (internalModules Λ X) ℤ) :=
  (HomologicalComplex.singleMapHomologicalComplex (CondensedRing.upperStar Λ f)
    (.up ℤ) 0).hom.app (𝟙_ (internalModules Λ Y)) ≫
    (HomologicalComplex.single (internalModules Λ X) (.up ℤ) 0).map
      (normalizationInternalUnit Λ f)

/-- The ringed total unit, induced by ordinary scalar multiplication in degree zero.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
@[irreducible] def sectionTotalUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (totalSectionPull Λ f).obj (𝟙_ (CochainComplex (modules Λ Y) ℤ)) ⟶
      𝟙_ (CochainComplex (modules Λ X) ℤ) :=
  (HomologicalComplex.singleMapHomologicalComplex (pullback Λ f) (.up ℤ) 0).hom.app
      (𝟙_ (modules Λ Y)) ≫
    (HomologicalComplex.single (modules Λ X) (.up ℤ) 0).map (normalizationSectionUnit Λ f)

/-- Conjugate the actual internal unit by the same fixed operation comparisons.
Source: Stacks 07A4 and 03EL (blueprint: def-pd-section-total-oplax-comparison-data). -/
def conjugatedInternalTotalUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (totalSectionPull Λ f).obj (𝟙_ (CochainComplex (modules Λ Y) ℤ)) ⟶
      𝟙_ (CochainComplex (modules Λ X) ℤ) :=
  (totalSectionPull Λ f).map (totalUnitComparison Λ Y).inv ≫
    (termwisePullComparison Λ f (𝟙_ (CochainComplex (internalModules Λ Y) ℤ))).inv ≫
    (totalSectionEquivalence Λ X).map (actualInternalTotalUnit Λ f) ≫
    (totalUnitComparison Λ X).hom

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
```

## Users

Inventory: `tools/downstream.py Sheaf.Paper.SectionTotalOplaxComparisonData
Sheaf.Paper.SectionOplaxTotalComparison --names`. This includes every transitive
importer, even when it does not mention a changed declaration explicitly. Claim holders
are read from the current `coord/claims/<module>.lock` records. No forced adaptation of a
module held by another group is proposed.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.SectionTotalOplaxComparisonData` | unclaimed | Definition and instance implementation changed; preservation checks required. |
| `Sheaf.Paper.SectionOplaxTotalComparison` | D8 | Unchanged proposition and signature; proof supplied. |
| `Sheaf.AlgebraicGeometry.FieldScalarProjectionMateCoherence` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.CanonicalCoefficientTensorNormalization` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.CountableNormProjectionCriterion` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.FilteredFlatTensorCohomology` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.FlatScalarGeometricCoherence` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.FlatScalarUnitNormalization` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.IntegralReductionUnderlyingDirectImage` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.InternalCanonicalTensorPullRouteModel` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.InternalOplaxResolvingComponents` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.InternalScalarMateProjection` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.InternalScalarProjectionMate` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.InternalScalarPullRouteModel` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.InternalScalarPullTensorCounit` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.InternalScalarPullbackNormalization` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.InternalScalarRegularPullCounit` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.InternalScalarTensorPullNormalization` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.InternalTensorPullRouteModel` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.ModuleRingedToposDerivedComparison` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.NormalizedScalarRestrictionPush` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.NormalizedScalarSectionFamily` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.RestrictedCoefficientPullbackData` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.ScalarChangeDirectImageUnit` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.ScalarGeometricExchangeRectangle` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.SectionDerivedRepresentativeSquare` | U3 | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.SectionDerivedTensorNormalization` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.SectionResolutionConjugationIdentities` | G6 | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.SectionResolvingOplaxConstraintData` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.SectionResolvingOplaxConstraintDiagrams` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.SectionResolvingOplaxInternalConjugation` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.SectionResolvingOplaxModelEdges` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.SectionResolvingOplaxUnitModels` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.SectionScalarComputationTransport` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.SectionTensorConjugateComputation` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.SectionTensorNormalizationTransport` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.Paper.SectionTensorRightComputation` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.SixFunctors.ProEtale.IntegralDirectImageLimits` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.SixFunctors.ProEtale.IntegralDirectImageReductionCone` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |
| `Sheaf.SixFunctors.ProEtale.IntegralDirectImageReductionTower` | unclaimed | Canonical data unchanged; no source adaptation currently required. Explicit constructors and constraint instances checked at direct consumers. |

## Status

landed 20261026T102357-L-347171 2026-10-26 (merge of deliver/D8/Sheaf.Paper.SectionOplaxTotalComparison)
