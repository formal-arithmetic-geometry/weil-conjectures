/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
import Sheaf.AlgebraicGeometry.ScalarCohomologyExtCoefficientNaturality
import Sheaf.AlgebraicGeometry.ScalarExtCupInverseImage
import Sheaf.AlgebraicGeometry.ScalarPullbackTensorCoefficient

/-! # ScalarCupPullbackNaturality

Source: Stacks Project, Cohomology, Tags 01F7, 07MB and 0FKV.
-/

@[expose] public section

universe w
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
/-- Pullback carries a scalar cup product to the cup of the pulled-back classes.
Source: Stacks Project, Cohomology, Tags 01FD, 07MB and 0FKV; Modules, Tag 01CD.
(blueprint: lem-sc-scalar-cup-pullback-naturality).

Proof: Work with sheaves of k-vector spaces via scalarCohomologyExtEquiv. The inverse
image is exact over k, and the inverse image of the constant unit is identified
with the constant unit by scalarInverseUnitIso. Inverse image is compatible with
sheaf tensor: on presheaves its tensor comparison sends a pair of pulled-back
sections to their pure tensor, and sheafification extends this comparison. Exact
inverse image therefore carries the Yoneda tensor pairing defining scalarExtCup
to the tensor pairing of the images, with the same unit identification. This can
also be computed by the resolution diagram of Tag 01FD and the signed total
complex pairing of Tag 07MB; inverse image does not change the two degrees.
The remaining coefficient square compares scalarPullbackCoefficient for F tensor G
followed by the scalar image of the module tensor-pullback comparison, against the
tensor of scalarPullbackCoefficient for F and G followed by scalarTensorCoefficient
on Y. Under the inverse-image adjunction, evaluate this square on pure tensor
sections s tensor r. The defining adjunction formula for scalarPullbackCoefficient
and the normalization in module_pullback_tensor show that both routes give the
tensor of the two module pullback-unit sections. Tensor sections generate before
sheafification, so its universal property proves the square. Tag 0FKV identifies
the tensor pairing after augmentation with the ordinary tensor cup product.
Naturality of the resolution comparison under the final coefficient map follows
by evaluation at 1, as the comparison maps are O-linear. Consequently the image
under scalarCohomologyExtEquiv of the left side is the pairing of the two images
on the right. Injectivity of this equivalence proves the assertion. Empty schemes,
zero coefficients and degree zero satisfy the same section identities.
-/
theorem scalarCup_pullback_naturality
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (t : Y ⟶ X) (ht : t ≫ f = g) (F G : X.Modules)
    (p q : ℕ) (a : scalarCohomology f F p) (b : scalarCohomology f G q) :
    scalarCohomologyMap g ((Classical.choose (module_pullback_tensor t)) F G).hom
        (p + q) (scalarCohomologyPullback f g t ht (@id X.Modules (F ⊗ G)) (p + q)
          (scalarCohomologyCup f F G p q a b)) =
      scalarCohomologyCup g ((tensorPullback t).obj F) ((tensorPullback t).obj G) p q
        (scalarCohomologyPullback f g t ht F p a)
        (scalarCohomologyPullback f g t ht G q b) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  let : MonoidalCategory (KSheaf X k) := Sheaf.monoidalCategory _ _
  let : MonoidalCategory (KSheaf Y k) := Sheaf.monoidalCategory _ _
  let : HasExt.{w + 1} (KSheaf X k) := HasExt.standard (KSheaf X k)
  let : HasExt.{w + 1} (KSheaf Y k) := HasExt.standard (KSheaf Y k)
  apply (scalarCohomologyExtEquiv g _ (p + q)).injective
  rw [scalarCohomologyExtEquiv_map]
  unfold scalarCohomologyPullback scalarCohomologyCup
  simp only [id_eq, AddEquiv.apply_symm_apply]
  rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
  simp only [Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀, Category.assoc]
  erw [scalarPullbackCoefficient_tensor f g t ht F G]
  have h := scalarExtCup_inverseImage t (scalarSheaf f F) (scalarSheaf f G)
    (scalarSheaf g ((tensorPullback t).obj F)) (scalarSheaf g ((tensorPullback t).obj G))
    (scalarPullbackCoefficient f g t ht F) (scalarPullbackCoefficient f g t ht G) p q
    (scalarCohomologyExtEquiv f F p a) (scalarCohomologyExtEquiv f G q b)
  have h' := congrArg
    (fun c : Abelian.Ext.{w + 1} (𝟙_ (KSheaf Y k))
        (scalarSheaf g ((tensorPullback t).obj F) ⊗
          scalarSheaf g ((tensorPullback t).obj G)) (p + q) ↦
      c.comp (Abelian.Ext.mk₀ (scalarTensorCoefficient g ((tensorPullback t).obj F)
        ((tensorPullback t).obj G))) (add_zero (p + q))) h
  simpa only [Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀, Category.assoc] using h'

end
end AlgebraicGeometry.Scheme.Modules
