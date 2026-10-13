/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.SecondLocalizationMap
/-! # Comparison for second localization
Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-second-localization-comparison). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
open scoped TensorProduct ChangeOfRings
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace RingTensorCohomology

variable (R A B Bp D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing Bp] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra B Bp] [Algebra R Bp]
  [tRB : IsScalarTower R B Bp]
  [Algebra (A ⊗[R] B) D] [Algebra (A ⊗[R] Bp) D]
  [Algebra A D] [Algebra B D] [Algebra Bp D]
  [tAD : IsScalarTower A (A ⊗[R] B) D]
  [tBD : IsScalarTower B (A ⊗[R] B) D]
  [tApD : IsScalarTower A (A ⊗[R] Bp) D]
  [tBpD : IsScalarTower Bp (A ⊗[R] Bp) D]
  [tBBpD : IsScalarTower B Bp D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Bp)]

include tRB tAD tBD tApD tBpD tBBpD in
/-- The localized comparison commutes with the characterized coefficient map.
Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-second-localization-comparison).

Proof: the defining leftDerivedLift factorization identifies the composite of
secondLocalizationDerivedMap with the target counit with the source counit
extended to Bp, followed by the ordinary associator. Apply cohomology, exact
flat homology base change, and cohomologyIso. Substitute comparison_eq for the
two models. The ordinary associators and ordinaryToLocalized send b tensor x
to its coefficient image tensor x; their composite to D agrees termwise.
Use localized_eq and transpose by the extension/restriction adjunction.
The generator formula for e gives the claimed D-linear square. Every tau in
the statement equals the ordinary identification because pure tensors generate
in each degree. The proof works for zero complexes and zero D, and does not
require flatness of D. -/
theorem secondLocalization_comparison (hflat : (algebraMap B Bp).Flat) (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D)
    (e : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ≅
      (ModuleCat.extendScalars (algebraMap (A ⊗[R] Bp) D)).obj (K.cohomology i))
    (he : IsSecondLocalizationMap R A B Bp D hflat Q L K i e.hom)
          (τ : ((ModuleCat.extendScalars ((algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj Q ≅
            ((ModuleCat.extendScalars ((algebraMap (A ⊗[R] Bp) D).comp
              (algebraMap A (A ⊗[R] Bp)))).mapHomologicalComplex (.up ℤ)).obj Q)
    (hτ : ∀ (j : ℤ) (d : D) (x : Q.X j),
            τ.hom.f j (d ⊗ₜ[A,(algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B))] x) =
              d ⊗ₜ[A,(algebraMap (A ⊗[R] Bp) D).comp
                (algebraMap A (A ⊗[R] Bp))] x) :
    L.localizedComparison i ≫ HomologicalComplex.homologyMap τ.hom i =
            e.hom ≫ K.localizedComparison i := by
  sorry

end RingTensorCohomology
