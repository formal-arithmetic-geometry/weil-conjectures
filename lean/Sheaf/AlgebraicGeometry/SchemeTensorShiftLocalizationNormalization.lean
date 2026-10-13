/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShift
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex

/-! # Normalizing tensor-shift composites through localization
Source: Stacks Project, Tag 06YH, K-flat total tensor localization.
(blueprint: lem-sc-scheme-tensor-shift-localization-normalization).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

variable (X : Scheme.{u})

noncomputable local instance :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance :
    SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.sheaf
local instance : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
noncomputable local instance :
    MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
local instance : IsGrothendieckAbelian.{u}
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
local instance : HasColimitsOfSize.{0, 0}
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := hasColimitsOfSizeShrink.{0, 0, u, u} _
local instance : Abelian.HasFunctorialFlatResolution
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  schemeModule_hasFunctorialFlatResolution X
variable [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

local instance : DerivedCategory.Qh.HasDerivedMonoidalCategory
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :=
  DerivedCategory.hasDerivedMonoidalCategory _

open Functor.LaxMonoidal in
/-- The comparison from a translated derived triple tensor to its total tensor representative.
Source: Stacks Project, Tag 06YH.
(blueprint: lem-sc-scheme-tensor-shift-localization-normalization). -/
noncomputable def schemeTensorShiftSourceComparison
    (P T U : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    (DerivedCategory.Q.obj P⟦(1 : ℤ)⟧ ⊗ DerivedCategory.Q.obj T) ⊗
        DerivedCategory.Q.obj U ⟶ DerivedCategory.Q.obj ((P⟦(1 : ℤ)⟧ ⊗ T) ⊗ U) :=
  (((DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app P) ▷ DerivedCategory.Q.obj T) ▷
      DerivedCategory.Q.obj U ≫
    (μ DerivedCategory.Q (P⟦(1 : ℤ)⟧) T) ▷ DerivedCategory.Q.obj U ≫
    μ DerivedCategory.Q (P⟦(1 : ℤ)⟧ ⊗ T) U

open Functor.LaxMonoidal in
/-- The comparison from the translated right-associated derived tensor to localization.
Source: Stacks Project, Tag 06YH.
(blueprint: lem-sc-scheme-tensor-shift-localization-normalization). -/
noncomputable def schemeTensorShiftTargetComparison
    (P T U : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    (DerivedCategory.Q.obj P ⊗ (DerivedCategory.Q.obj T ⊗ DerivedCategory.Q.obj U))⟦(1 : ℤ)⟧ ⟶
      DerivedCategory.Q.obj ((P ⊗ (T ⊗ U))⟦(1 : ℤ)⟧) :=
  (DerivedCategory.Q.obj P ◁ μ DerivedCategory.Q T U ≫
    μ DerivedCategory.Q P (T ⊗ U))⟦(1 : ℤ)⟧' ≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app (P ⊗ (T ⊗ U))

/-- Each route through shift and reassociation separately normalizes to its complex route.
This does not assert that the two complex routes, or the two derived routes, agree.
Source: Stacks Project, Tag 06YH, localization step of
lem-sc-scheme-canonical-tensor-shift-associator-kflat-one.
(blueprint: lem-sc-scheme-tensor-shift-localization-normalization).

Proof. The tensor comparison of Q is invertible when either factor is K-flat.
Sheaf K-flatness implies the upstream two-sided condition: the defining acyclicity
condition gives preservation on the right, and symmetry gives preservation on the
left; the cone criterion gives preservation of quasi-isomorphisms. Apply this to
P and T. The target comparison is a composition of shifted invertible tensor
comparisons and the inverse localization shift comparison, hence is invertible.
For the first formula, apply the lax monoidal associativity identity to the
translated source, followed by the first-variable localization shift square for
P and T tensor U. Naturality moves the inner tensor comparison through the shift.
For the second formula, apply that shift square first to P,T and then to P tensor T,U,
using K-flatness of the tensor of K-flat complexes. Apply lax monoidal associativity
at P,T,U and naturality of the localization shift isomorphism. Functoriality combines
the resulting localized maps into the displayed composites. No equality between
these composites is used in either normalization. All comparisons are the ones
used by IndependentTensorShift.commShift₂CurriedTensor, transported from quotient
followed by Qh to Q via quotientCompQhIso. For zero factors and the empty scheme
these formulas are the unique maps between zero objects; they do not require
nonzero scalars or characteristic assumptions. -/
theorem schemeTensorShift_localization_normalization
    (P T U : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := X.sheaf) P)
    (hT : CochainComplex.IsKFlat (R := X.sheaf) T)
    (hU : CochainComplex.IsKFlat (R := X.sheaf) U) :
    letI := schemeCanonicalTensorShift X
    letI : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
      fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
    let A := DerivedCategory.Q.obj P
    let K := DerivedCategory.Q.obj T
    let M := DerivedCategory.Q.obj U
    let c := schemeTensorShiftTargetComparison X P T U
    let v := schemeTensorShiftSourceComparison X P T U
    IsIso c ∧
      ((α_ (A⟦(1 : ℤ)⟧) K M).hom ≫
          ((tensorRight (K ⊗ M)).commShiftIso (1 : ℤ)).hom.app A) ≫ c =
        v ≫ DerivedCategory.Q.map ((α_ (P⟦(1 : ℤ)⟧) T U).hom ≫
          (CochainComplex.mapBifunctorShift₁Iso P (T ⊗ U)
            (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) 1).hom) ∧
      ((((tensorRight K).commShiftIso (1 : ℤ)).hom.app A) ▷ M ≫
          ((tensorRight M).commShiftIso (1 : ℤ)).hom.app (A ⊗ K) ≫
          (α_ A K M).hom⟦(1 : ℤ)⟧') ≫ c =
        v ≫ DerivedCategory.Q.map
          ((CochainComplex.mapBifunctorShift₁Iso P T
            (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) 1).hom ▷ U ≫
          (CochainComplex.mapBifunctorShift₁Iso (P ⊗ T) U
            (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) 1).hom ≫
          (α_ P T U).hom⟦(1 : ℤ)⟧') := by sorry

end AlgebraicGeometry
