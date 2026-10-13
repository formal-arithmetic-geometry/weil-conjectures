/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.BaseLocalizationMap

/-! # B-linear invertibility of base localization

Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-base-localization-cohomology-is-iso).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Functor
open scoped TensorProduct ChangeOfRings
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace RingTensorCohomology

variable (R Rp B A D : Type u)
  [CommRing R] [CommRing Rp] [CommRing B] [CommRing A] [CommRing D]
  [Algebra R Rp] [Algebra R B] [Algebra Rp B] [IsScalarTower R Rp B]
  [Algebra R A] [Algebra Rp A] [IsScalarTower R Rp A]
  [Algebra (A ⊗[R] B) D] [Algebra (A ⊗[Rp] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Rp)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

/-- The canonical base-localization map is an isomorphism on B-linear cohomology.
Source: Stacks Project, Tag 06Y6, lemma-derived-base-change; Tag 0DJ8.
(blueprint: lem-pc-base-localization-cohomology-is-iso).

Proof: choose a K-flat Rp-resolution P of the restricted input Q. Restriction to R
preserves K-flatness: tensor an acyclic R-complex with Rp, use exactness of localization,
and identify its tensor with P by associativity. Apply the K-flat counit theorem to
both universal derived functors on P. The counit equation for the universal lift,
and the ordinary localization tensor isomorphism, then make the lift on P invertible.
The augmentation P to Q is a quasi-isomorphism over both bases; naturality transports
invertibility to Q. Apply the B-homology functor and conjugate by the two model
cohomology isomorphisms. This is exactly baseLocalizationCohomologyMap. Identity
localization gives model transport; when S contains zero, both cohomologies are zero.
No algebra structures on D over A or B, and no flatness of D, are needed. -/
theorem baseLocalizationCohomologyMap_isIso
    (S : Submonoid R) [IsLocalization S Rp]
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel Rp A B Q D) (i : ℤ) :
    IsIso (baseLocalizationCohomologyMap R Rp B A D S Q L K i) := by sorry

end RingTensorCohomology
