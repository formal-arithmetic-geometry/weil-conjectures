/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-! # Tensor complexes with independent site universes

Source: Stacks Project, Modules on Sites, Section 03EK.
(blueprint: def-pur-sheaf-tensor-product)

The tensor is the existing localization tensor, with no restriction equating
site object, site morphism, and coefficient universes.
-/

@[expose] public section

universe uC vC w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules
set_option autoImplicit false
variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (R : Sheaf J CommRingCat.{w})

/-- Tensoring preserves local equivalences on any essentially small site.
Source: Stacks 03EK (blueprint: def-pur-sheaf-tensor-product).
Proof: replace the site by its small model in universe w. The tensor and
sheafification universal properties commute with this equivalence. On the
small model local tensoring preserves local equivalences, and transport back
preserves this assertion. -/
@[instance]
theorem cochainTensorLocalizationIsMonoidal :
    (J.W.inverseImage (PresheafOfModules.toPresheaf.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).IsMonoidal := sorry

/-- The existing localization tensor, with independent site sizes.
Source: Stacks 03EK (blueprint: def-pur-sheaf-tensor-product). -/
noncomputable instance cochainModulesMonoidal :
    MonoidalCategory (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  @monoidalCategory.{vC, uC, w} C _ J _ R _ _ (cochainTensorLocalizationIsMonoidal R)

/-- The existing symmetric structure of the localization tensor.
Source: Stacks 03EK (blueprint: def-pur-sheaf-tensor-product). -/
noncomputable instance cochainModulesSymmetric :
    SymmetricCategory (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  @symmetricCategory.{vC, uC, w} C _ J _ R _ _ (cochainTensorLocalizationIsMonoidal R)

/-- The sheaf tensor is additive in each variable, independently of site sizes.
Source: Stacks 03EK (blueprint: def-pur-sheaf-tensor-product).
Proof: additivity holds sectionwise on pure tensors and descends through the
additive sheafification functor; the localization tensor has those same maps. -/
@[instance]
theorem cochainModulesPreadditive :
    MonoidalPreadditive (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) := sorry

/-- Left tensoring preserves the coproducts used in unbounded total tensor.
Source: Stacks 03EK (blueprint: def-pur-sheaf-tensor-product).
Proof: bilinear maps out of a direct sum are families of bilinear maps.
The tensor universal property and sheafification adjunction identify the
coproduct comparison with this bijection, so it is invertible. -/
@[instance]
theorem cochainTensorLeftPreservesColimits
    (M : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) := sorry

/-- Right tensoring preserves the coproducts used in unbounded total tensor.
Source: Stacks 03EK (blueprint: def-pur-sheaf-tensor-product).
Proof: conjugate left tensoring by the existing symmetric braiding. -/
@[instance]
theorem cochainTensorRightPreservesColimits
    (M : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    PreservesColimitsOfSize.{0, 0} (tensorRight M) := sorry

end SheafOfModules
