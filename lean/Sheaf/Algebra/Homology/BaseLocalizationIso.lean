/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Sheaf.Algebra.Homology.RingTensorCohomology
public import Sheaf.Algebra.Homology.BaseLocalizationMap
/-! # Localizing the base and second factor of a derived tensor

Source: Stacks Project, perfect.tex, Tag 0DJ8, localization of the base and
second coefficient ring; More on Algebra, Tag 06Y6.
(blueprint: lem-pc-base-localization-iso).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped TensorProduct ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology

variable (R A B Rp D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing Rp] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra R Rp] [Algebra Rp A] [Algebra Rp B]
  [tRpA : IsScalarTower R Rp A] [tRpB : IsScalarTower R Rp B]
  [Algebra (A ⊗[R] B) D] [Algebra (A ⊗[Rp] B) D]
  [Algebra A D] [Algebra B D]
  [tAD : IsScalarTower A (A ⊗[R] B) D]
  [tBD : IsScalarTower B (A ⊗[R] B) D]
  [tApD : IsScalarTower A (A ⊗[Rp] B) D]
  [tBpD : IsScalarTower B (A ⊗[Rp] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Rp)]

include tRpA tRpB tAD tBD tApD tBpD in
/-- The canonical map is invertible after extension to D.
Source: Stacks Project, Tag 0DJ8, affine localization identity; Tag 06Y6.
(blueprint: lem-pc-base-localization-iso).

Proof: choose a K-flat Rp-resolution P of the underlying Rp-complex of Q.
Its restriction to R is K-flat: for an acyclic R-complex F, exact localization
Rp tensor_R F is acyclic, and tensor associativity identifies its tensor with
P with F tensor_R P. Both universal derived counits are invertible on these
K-flat complexes. Naturality with respect to the resolution augmentation,
which is a quasi-isomorphism both before and after restriction, therefore
shows that the universal lift defining baseLocalizationDerivedMap is
invertible at Q. Its counit equation identifies it with the pure-tensor
localization identity. Naturality for multiplication by a in A and
cohomologyIso_smul show that the cohomology map intertwines the two A-actions;
B-linearity is built in. The algebra isomorphism A tensor_Rp B = A tensor_R B
fixes pure tensors, so the cohomology map is an isomorphism after transporting
this tensor-algebra action. The maps to D agree on A and B by the scalar-tower
hypotheses. Extend the transported isomorphism to D. Tensor induction gives
the displayed generator equation and its uniqueness. For the identity
localization the universal lift is the unique model comparison. If S contains
zero, Rp, A, B and D are zero rings and the conclusion is the unique zero-module
isomorphism. No flatness of D or boundedness of Q is used. -/
theorem exists_baseLocalization_iso (S : Submonoid R) [IsLocalization S Rp] (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel Rp A B Q D) :
    ∃ e : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ≅
      (ModuleCat.extendScalars (algebraMap (A ⊗[Rp] B) D)).obj (K.cohomology i),
      IsBaseLocalizationMap R Rp B A D S Q L K i e.hom := by
  sorry

end RingTensorCohomology
