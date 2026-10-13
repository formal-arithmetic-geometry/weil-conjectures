/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.SecondLocalizationMap
/-! # Ordinary comparison for second localization
Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-second-localization-ordinary-B-square). -/

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
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Bp)]

include tRB in
/-- The B-linear ordinary counit square, before forgetting module structures.
Source: Stacks Project, Tag 06Y6, lemma-derived-base-change; Tag 0DJ8.
(blueprint: lem-pc-second-localization-ordinary-B-square).

Proof: install the target model's universal left-derived-functor instance.
The defining leftDerivedLift factorization of secondLocalizationDerivedMap
identifies its composite with K.counit with L.counit extended to Bp and the
ordinary scalar-extension associator. Evaluate at the restriction of Q to R,
apply degree-i homology, and use the defining localization factorization of
flatDerivedHomologyIso to commute the flat extension with homology. Transpose
along extension/restriction of scalars B to Bp: the unit sends x to 1 tensor x.
Substitute the two comparison_eq identities and cancel the cohomologyIso maps.
The ordinary associator sends b tensor x to image(b) tensor x; the given hφ
identifies its transpose, conjugated by ordinaryIso, with φB, by tensor
induction after precomposing with L.ordinaryIso. Naturality of the homology
factorization maps and of mapHomologyIso for restriction to B completes the
B-linear identity below. This calculation uses no forgetful functor, no
localizedComparison, and no hypothesis on flatness of D. -/
theorem secondLocalization_ordinary_B_square (hflat : (algebraMap B Bp).Flat) (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D)
    (φB : ((ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight :
          B →ₐ[R] A ⊗[R] B).toRingHom).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex (.up ℤ)).obj
          Q) ⟶
      ((ModuleCat.restrictScalars (algebraMap B Bp)).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight :
          Bp →ₐ[R] A ⊗[R] Bp).toRingHom).mapHomologicalComplex (.up ℤ)).obj
          (((ModuleCat.extendScalars (algebraMap A (A ⊗[R] Bp))).mapHomologicalComplex (.up
            ℤ)).obj Q)))
    (hφ : ∀ (j : ℤ) (b : B) (x : Q.X j),
      φB.f j (L.ordinaryIso.hom.f j (b ⊗ₜ[R,algebraMap R B] x)) =
        K.ordinaryIso.hom.f j (algebraMap B Bp b ⊗ₜ[R,algebraMap R Bp] x)) :
    (ModuleCat.restrictScalars
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map
        (L.comparison i) ≫
      (((((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
        (.up ℤ)).obj Q).sc i).mapHomologyIso
          (ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom)).inv ≫
      HomologicalComplex.homologyMap φB i =
    secondLocalizationCohomologyMap R A B Bp D hflat Q L K i ≫
      (ModuleCat.restrictScalars (algebraMap B Bp)).map
        ((ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight : Bp →ₐ[R] A ⊗[R] Bp).toRingHom).map
            (K.comparison i) ≫
          (((((ModuleCat.extendScalars (algebraMap A (A ⊗[R] Bp))).mapHomologicalComplex
            (.up ℤ)).obj Q).sc i).mapHomologyIso
              (ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight : Bp →ₐ[R] A ⊗[R] Bp).toRingHom)).inv) ≫
      (((((ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight :
          Bp →ₐ[R] A ⊗[R] Bp).toRingHom).mapHomologicalComplex (.up ℤ)).obj
            (((ModuleCat.extendScalars (algebraMap A (A ⊗[R] Bp))).mapHomologicalComplex (.up
              ℤ)).obj Q)).sc i).mapHomologyIso (ModuleCat.restrictScalars (algebraMap B Bp))).inv
                := by
  sorry

end RingTensorCohomology
