/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-!
# Scalar extension along an isomorphism of ring sheaves

Source: Stacks Project, Modules on Sites, Tags 03CZ, 03EK and 03CY
(blueprint: lem-weil-sheaf-scalar-extension-ring-iso).

The transported module functor is the existing restriction of scalars along the inverse.
The tensor convention in the existing change-of-rings construction puts the scalar first:
`s ⊗ x` represents the node's `x ⊗ s` under tensor symmetry.
-/

@[expose] public section

universe uC vC r m

open CategoryTheory
open scoped ChangeOfRings

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max r m}]
  [HasWeakSheafify J AddCommGrpCat.{max r m}]
  {R S : Sheaf J CommRingCat.{r}}

/-- The canonical sheafification-unit image of a local scalar-extension pure tensor.
Source: Stacks, Tags 03EK and 03CY
(blueprint: lem-weil-sheaf-scalar-extension-ring-iso).
This is `eta(x ⊗ s)` in the node's factor order, with no choice of a sectionwise inverse. -/
noncomputable def scalarExtensionRingIsoTmul (a : R ⟶ S)
    (M : ringedSiteModules.{max r m}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (x : M.val.obj U) (s : S.obj.obj U) :
    (changeOfRingsOfUniverses a M).val.obj U :=
  letI := siteTensor_identity_locallyInjective
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
  letI := siteTensor_identity_locallySurjective
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
  (((PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).unit.app
      (changeOfRingsPresheafOfUniverses a M)).app U)
        (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x)

/-- Scalar extension along a ring-sheaf isomorphism is naturally the original abelian
sheaf with action transported along its inverse, with both specified section formulas.
Source: Stacks, Tags 03CZ, 03EK and 03CY
(blueprint: lem-weil-sheaf-scalar-extension-ring-iso).

Proof: (1) restriction of scalars along `c.inv` retains the abelian sheaf and all maps;
its action is `s • x = c.inv(s) • x`, compatible with restrictions by naturality of
`c.inv` (def-weil-sheaf-of-modules-category). (2) The balanced map on local tensors
sends `s ⊗ x` to `c.inv(s) • x`; the tensor universal property makes it linear
(def-weil-pbc-module-tensor-product). (3) The maps commute with restrictions since
`c.inv` is natural (def-pur-sheaf-tensor-product). (4) The inverse before sheafification
sends `x` to `1 ⊗ x`; balancing and the inverse identities of `c` show that both
composites are identities, first on pure tensors and then by tensor generation.
(5) The module-sheafification universal property extends the forward map uniquely;
compose the inverse with the unit. One inverse identity holds directly, and the other
follows by uniqueness after precomposition with the unit
(def-weil-presheaf-modules-sheafification). These give the two displayed formulas.
(6) For `h : M ⟶ N`, both naturality composites take `s ⊗ x` to
`c.inv(s) • h(x) = h(c.inv(s) • x)`. Tensor generation and the same sheafification
uniqueness give naturality, without assuming sections of a sheafified tensor are pure. -/
theorem exists_scalarExtensionRingIso (c : R ≅ S) :
    ∃ theta : ∀ M : ringedSiteModules.{max r m}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R),
      changeOfRingsOfUniverses c.hom M ≅
        (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map c.inv)).obj M,
      (∀ (M : ringedSiteModules.{max r m}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
        (U : Cᵒᵖ) (x : M.val.obj U) (s : S.obj.obj U),
        (theta M).hom.val.app U (scalarExtensionRingIsoTmul c.hom M U x s) =
          (c.inv.hom.app U) s • x) ∧
      (∀ (M : ringedSiteModules.{max r m}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
        (U : Cᵒᵖ) (x : M.val.obj U),
        (theta M).inv.val.app U x = scalarExtensionRingIsoTmul c.hom M U x 1) ∧
      (∀ (M N : ringedSiteModules.{max r m}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (h : M ⟶ N),
        changeOfRingsHomOfUniverses c.hom M h ≫ (theta N).hom =
          (theta M).hom ≫
            (restrictScalars
              ((sheafCompose J (forget₂ CommRingCat RingCat)).map c.inv)).map h) := by
  sorry

end SheafOfModules
