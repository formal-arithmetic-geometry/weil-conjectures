/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectPackageOnSiteSupplement
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
public import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Strict-perfect models with independent site and coefficient universes

Source: Stacks Project, Tag 08G5; Weil blueprint, order 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).
The recorded general-site degreewise package is reused. The recorded small-site
local-perfectness and representation interfaces fix coefficients at the site-object
universe; these forms also allow independently larger coefficients.

## Main definitions

- `IsLocallyStrictPerfectComplexOfUniverses`
- `IsPerfectOnRingedSiteOfUniverses`
- `StrictPerfectCoefficientRepresentationOfUniverses`
-/

@[expose] public section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe uC vC r w
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}

variable [HasSheafify J AddCommGrpCat.{max uC vC r}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max uC vC r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]

end SheafOfModules

noncomputable section

universe c v s
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{s} C]
  (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{s}] [HasSheafify J AddCommGrpCat.{s}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{s}]

/-- Additivity of the constant module functor at independent sizes.
Source: Stacks 03CY (blueprint: def-weil-pbc-strict-perfect-coefficient-package).
Proof: sums are pointwise in the constant presheaf, and module sheafification is additive. -/
@[instance] theorem scalarPerfectConstantFunctor_additive (R : Type s) [CommRing R] :
    (scalarPerfectConstantFunctor J R).Additive := by
  let := (scalarPerfectRingUnit_locallyBijective J R).1
  let := (scalarPerfectRingUnit_locallyBijective J R).2
  have : (scalarPerfectConstantPresheaf (C := C) R).Additive := by
    constructor
    intro M N f g
    apply PresheafOfModules.hom_ext
    intro U
    rfl
  have : (PresheafOfModules.sheafification (scalarPerfectRingUnit J R)).Additive :=
    (PresheafOfModules.sheafificationAdjunction _).left_adjoint_additive
  unfold scalarPerfectConstantFunctor
  infer_instance

set_option linter.unusedSectionVars false in
/-- Ordinary scalar extension is additive even for a nonflat coefficient map.
Source: Stacks 03EK (blueprint: def-weil-pbc-strict-perfect-coefficient-package).
Proof: sectionwise tensor maps preserve addition; additive sheafification preserves
this equality. This does not assert preservation of kernels or exact sequences. -/
@[instance] theorem scalarPerfectExtensionFunctor_additive
    {A B : Sheaf J CommRingCat.{s}} (φ : A ⟶ B) :
    (scalarPerfectExtensionFunctor J φ).Additive := by
  have : (PresheafOfModules.sheafification
      (R := scalarPerfectRingUnderlying J B) (𝟙 _)).Additive :=
    (PresheafOfModules.sheafificationAdjunction _).left_adjoint_additive
  constructor
  intro M N f g
  change (PresheafOfModules.sheafification
      (R := scalarPerfectRingUnderlying J B) (𝟙 _)).map _ =
    (PresheafOfModules.sheafification
      (R := scalarPerfectRingUnderlying J B) (𝟙 _)).map _ +
    (PresheafOfModules.sheafification
      (R := scalarPerfectRingUnderlying J B) (𝟙 _)).map _
  rw [← (PresheafOfModules.sheafification
    (R := scalarPerfectRingUnderlying J B) (𝟙 _)).map_add]
  congr 1
  apply PresheafOfModules.hom_ext
  intro U
  have : (ModuleCat.extendScalars (φ.hom.app U).hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).left_adjoint_additive
  exact (ModuleCat.extendScalars (φ.hom.app U).hom).map_add
    (f := f.val.app U) (g := g.val.app U)

/-- Constant scalar extension is additive; no flatness is involved.
Source: Stacks 03CY, 03EK and 0GMW
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).
Proof: constant presheaves preserve sums of linear maps componentwise; their module
sheafification is additive. Sectionwise scalar extension is additive on pure tensors,
and target module sheafification preserves this equality. Compose these functors. -/
@[instance] theorem scalarPerfectFunctor_additive (R : Type s) [CommRing R]
    {B : Sheaf J CommRingCat.{s}} (φ : scalarPerfectRing J R ⟶ B) :
    (scalarPerfectFunctor J R φ).Additive := by
  unfold scalarPerfectFunctor
  infer_instance

variable [∀ U : C, EssentiallySmall.{s} (Over U)]
  [∀ U : C, HasSheafify (J.over U) CommRingCat.{s}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{s}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{s}]

end SheafOfModules
