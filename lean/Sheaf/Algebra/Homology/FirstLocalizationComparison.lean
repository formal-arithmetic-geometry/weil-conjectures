/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.FirstLocalizationMap
/-! # Comparison square for the characterized localization map

Source: Stacks Project, Tag 06Y6; Tag 0DJ8.
(blueprint: lem-pc-first-localization-comparison). -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped TensorProduct ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology

variable (R A B Aq D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing Aq] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra A Aq] [Algebra R Aq]
  [tRA : IsScalarTower R A Aq]
  [Algebra (A ⊗[R] B) D] [Algebra (Aq ⊗[R] B) D]
  [Algebra A D] [Algebra B D] [Algebra Aq D]
  [tAD : IsScalarTower A (A ⊗[R] B) D]
  [tBD : IsScalarTower B (A ⊗[R] B) D]
  [tAqD : IsScalarTower Aq (Aq ⊗[R] B) D]
  [tBqD : IsScalarTower B (Aq ⊗[R] B) D]
  [tAAqD : IsScalarTower A Aq D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

include tAD tBD tAqD tBqD tAAqD in
/-- Comparison square for the characterized localization map.
Source: Stacks Project, Tag 06Y6; Tag 0DJ8, affine localization identity.
(blueprint: lem-pc-first-localization-comparison).

Proof: apply naturality of the universal derived-functor counit to the
localization unit. The ordinary tensor associativity maps commute with that unit:
on b tensor x both routes give (1 tensor b) tensor (1 tensor x).
The same calculation after extension to D gives d tensor (1 tensor x).
Use comparison_eq on both models, then localized_eq and the extension/restriction
adjunction to obtain the D-linear equality on generators. Tensor induction proves
it on every element. Any tau with the given formula equals the associativity map,
by tensor induction termwise. No flatness of D is needed. For zero complexes or
zero D all maps are the unique zero map. -/
theorem firstLocalization_comparison (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D)
    (e : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ≅
      (ModuleCat.extendScalars (algebraMap (Aq ⊗[R] B) D)).obj (K.cohomology i))
    (he : IsFirstLocalizationMap R A Aq B D Q L K i e.hom)
    (τ : ((ModuleCat.extendScalars ((algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj Q ≅
            ((ModuleCat.extendScalars ((algebraMap (Aq ⊗[R] B) D).comp
              (algebraMap Aq (Aq ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj
                ((extend A Aq).obj Q))
    (hτ : ∀ (j : ℤ) (d : D) (x : Q.X j),
            τ.hom.f j (d ⊗ₜ[A,(algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B))] x) =
              d ⊗ₜ[Aq,(algebraMap (Aq ⊗[R] B) D).comp
                (algebraMap Aq (Aq ⊗[R] B))] ((1 : Aq) ⊗ₜ[A,algebraMap A Aq] x)) :
          L.localizedComparison i ≫ HomologicalComplex.homologyMap τ.hom i =
            e.hom ≫ K.localizedComparison i := by
  sorry

end RingTensorCohomology
