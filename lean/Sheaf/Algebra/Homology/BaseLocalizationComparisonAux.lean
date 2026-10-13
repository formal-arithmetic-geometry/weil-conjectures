/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Sheaf.Algebra.Homology.RingTensorCohomology
public import Sheaf.Algebra.Homology.BaseLocalizationMap

/-! Generator calculation for base localization comparison.

Source: Stacks Project, perfect.tex, Tags 0DJ8 and 06Y6.
(blueprint: lem-pc-base-localization-comparison-aux).
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
/-- The base-localization comparison identity on extension generators.
Source: Stacks Project, perfect.tex, Tags 0DJ8 and 06Y6.
(blueprint: lem-pc-base-localization-comparison-aux).

Proof: expand the two localized comparisons using their `localized_eq`
identities and the comparison equations of the two models.  The universal
counit equation for `baseLocalizationDerivedMap` gives the corresponding
ordinary square.  Evaluating in each degree on `1 tensor x`, the ordinary
identification is fixed by the displayed formula for `tau`; the resulting
value is the canonical B-linear base-localization cohomology map.  This is
exactly the generator calculation needed for the extension-of-scalars
extensionality argument in `baseLocalization_comparison`.
-/
theorem baseLocalization_comparison_aux (S : Submonoid R) [IsLocalization S Rp]
    (i : ℤ) (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel Rp A B Q D)
    (τ : ((ModuleCat.extendScalars ((algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj Q ≅
            ((ModuleCat.extendScalars ((algebraMap (A ⊗[Rp] B) D).comp
              (algebraMap A (A ⊗[Rp] B)))).mapHomologicalComplex (.up ℤ)).obj Q)
    (hτ : ∀ (j : ℤ) (d : D) (x : Q.X j),
            τ.hom.f j (d ⊗ₜ[A,(algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B))] x) =
              d ⊗ₜ[A,(algebraMap (A ⊗[Rp] B) D).comp
                (algebraMap A (A ⊗[Rp] B))] x) :
    ∀ x : L.cohomology i,
      (L.localizedComparison i ≫ HomologicalComplex.homologyMap τ.hom i)
          ((1 : D) ⊗ₜ[A ⊗[R] B,algebraMap (A ⊗[R] B) D] x) =
        K.localizedComparison i
          ((1 : D) ⊗ₜ[A ⊗[Rp] B,algebraMap (A ⊗[Rp] B) D]
            (baseLocalizationCohomologyMap R Rp B A D S Q L K i x)) := by
  sorry

end RingTensorCohomology
