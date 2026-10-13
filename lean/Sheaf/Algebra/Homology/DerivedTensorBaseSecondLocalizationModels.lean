/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Sheaf.Algebra.Homology.RingTensorCohomology
public import Mathlib.RingTheory.Localization.Basic
/-! # Localizing the base and second factor of a derived tensor

Source: Stacks Project, perfect.tex, Tag 0DJ8, localization of the base and
second coefficient ring; More on Algebra, Tag 06Y6.
(blueprint: lem-pc-derived-tensor-base-second-localization-models).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped TensorProduct ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology

variable (R A B Rp Bp D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing Rp] [CommRing Bp] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra R Rp] [Algebra B Bp]
  [Algebra R Bp] [Algebra Rp A] [Algebra Rp Bp]
  [tRpA : IsScalarTower R Rp A]
  [tRB : IsScalarTower R B Bp] [tRpB : IsScalarTower R Rp Bp]
  [Algebra (A ⊗[R] B) D] [Algebra (A ⊗[Rp] Bp) D]
  [Algebra A D] [Algebra B D] [Algebra Bp D]
  [tAD : IsScalarTower A (A ⊗[R] B) D]
  [tBD : IsScalarTower B (A ⊗[R] B) D]
  [tApD : IsScalarTower A (A ⊗[Rp] Bp) D]
  [tBpD : IsScalarTower Bp (A ⊗[Rp] Bp) D]
  [tBBpD : IsScalarTower B Bp D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Rp)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Bp)]

include tRpA tRB tRpB tAD tBD tApD tBpD tBBpD in
/-- Change a localized base and localize the second algebra, keeping Q fixed.
Source: Stacks Project, perfect.tex, Tag 0DJ8, second localization identity.
(blueprint: lem-pc-derived-tensor-base-second-localization-models).

Proof: let F -> B[0] be a K-flat R-resolution. As Q is an Rp-complex after
restriction from A, the tensor-localization formula identifies Q tensor_R F
with Q tensor_Rp (Rp tensor_R F), termwise and naturally in Q. Localization is
exact and preserves K-flatness, so Rp tensor_R F resolves Rp tensor_R B.
The map Rp tensor_R B -> Bp is a flat localization: it is the base change of
B -> Bp, and Rp tensor_R Bp = Bp because the R-elements in S are already
units in Bp. Flat second-factor base change identifies the cohomology after
extension to Bp with H(Q tensor-derived_Rp Bp). Both coefficient actions agree,
so this is linear over A tensor_Rp Bp. Tensor associativity followed by
extension to D gives the claimed isomorphism. The maps induced by F -> B[0]
and its localization are the comparison maps; their square commutes on pure
tensors d tensor x. Chain maps give naturality. Unique counit-compatible
identifications of derived functors transport this construction to arbitrary
models; cohomologyIso_smul identifies the A-action, and faithful restriction
of scalars identifies the characterized g and h. Tau is uniquely fixed by its
pure-tensor formula, so the comparison clause holds for every such tau.
The argument applies to unbounded Q and does not require Q to be R-K-flat. -/
theorem derivedTensor_base_second_localization_models
    (S : Submonoid R) [IsLocalization S Rp]
    (T : Submonoid B) [IsLocalization T Bp] (i : ℤ) :
    ∃ e : ∀ (Q : CochainComplex (ModuleCat.{u} A) ℤ)
        (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
        (K : ModuleCat.BaseDerivedTensorCohomologyModel Rp A Bp Q D),
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj
            (L.cohomology i) ≅
          (ModuleCat.extendScalars (algebraMap (A ⊗[Rp] Bp) D)).obj
            (K.cohomology i),
      (∀ (Q : CochainComplex (ModuleCat.{u} A) ℤ)
          (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
          (K : ModuleCat.BaseDerivedTensorCohomologyModel Rp A Bp Q D)
          (τ : ((ModuleCat.extendScalars ((algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj Q ≅
            ((ModuleCat.extendScalars ((algebraMap (A ⊗[Rp] Bp) D).comp
              (algebraMap A (A ⊗[Rp] Bp)))).mapHomologicalComplex (.up ℤ)).obj Q),
          (∀ (j : ℤ) (d : D) (x : Q.X j),
            τ.hom.f j (d ⊗ₜ[A, (algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B))] x) =
              d ⊗ₜ[A, (algebraMap (A ⊗[Rp] Bp) D).comp
                (algebraMap A (A ⊗[Rp] Bp))] x) →
          L.localizedComparison i ≫ HomologicalComplex.homologyMap τ.hom i =
            (e Q L K).hom ≫ K.localizedComparison i) ∧
      (∀ (Q Q' : CochainComplex (ModuleCat.{u} A) ℤ) (f : Q ⟶ Q')
          (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
          (K : ModuleCat.BaseDerivedTensorCohomologyModel Rp A Bp Q D)
          (L' : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q' D)
          (K' : ModuleCat.BaseDerivedTensorCohomologyModel Rp A Bp Q' D)
          (δ : L.derived ⟶ L'.derived) (ε : K.derived ⟶ K'.derived)
          (g : L.cohomology i ⟶ L'.cohomology i)
          (h : K.cohomology i ⟶ K'.cohomology i),
        Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} R)) δ ≫
            L'.counit = L.counit →
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map g ≫
              (L'.cohomologyIso i).hom =
          (L.cohomologyIso i).hom ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
              (L.derived.map (DerivedCategory.Qh.map
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
                  ((restrict R A).map f)))) ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
              (δ.app (DerivedCategory.Qh.obj
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
                  ((restrict R A).obj Q')))) →
        Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} Rp)) ε ≫
            K'.counit = K.counit →
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.includeRight : Bp →ₐ[Rp] A ⊗[Rp] Bp).toRingHom).map h ≫
              (K'.cohomologyIso i).hom =
          (K.cohomologyIso i).hom ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} Bp) i).map
              (K.derived.map (DerivedCategory.Qh.map
                ((HomotopyCategory.quotient (ModuleCat.{u} Rp) (.up ℤ)).map
                  ((restrict Rp A).map f)))) ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} Bp) i).map
              (ε.app (DerivedCategory.Qh.obj
                ((HomotopyCategory.quotient (ModuleCat.{u} Rp) (.up ℤ)).obj
                  ((restrict Rp A).obj Q')))) →
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).map g ≫
            (e Q' L' K').hom =
          (e Q L K).hom ≫
            (ModuleCat.extendScalars (algebraMap (A ⊗[Rp] Bp) D)).map h) := by
  sorry

end RingTensorCohomology
