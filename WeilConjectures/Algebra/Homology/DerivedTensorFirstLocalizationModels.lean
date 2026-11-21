/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import WeilConjectures.Algebra.Homology.RingTensorCohomology
public import Mathlib.RingTheory.Localization.Basic
import WeilConjectures.Algebra.Homology.FirstLocalizationComparison
import WeilConjectures.Algebra.Homology.FirstLocalizationNaturality
/-! # First-factor localization of base-derived tensor cohomology

## References

* Stacks Project, Tag 0DJ8 (first localization identity)
* Stacks Project, Tags 064K and 06Y6 (More on Algebra)
-/

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

include tRA tAD tBD tAqD tBqD tAAqD in
/-- Exact localization in the first algebra, with R and B unchanged. -/
theorem derivedTensor_first_localization_models
    (S : Submonoid A) [IsLocalization S Aq] (i : ℤ) :
    ∃ e : ∀ (Q : CochainComplex (ModuleCat.{u} A) ℤ)
        (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
        (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D),
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj
            (L.cohomology i) ≅
          (ModuleCat.extendScalars (algebraMap (Aq ⊗[R] B) D)).obj
            (K.cohomology i),
      (∀ (Q : CochainComplex (ModuleCat.{u} A) ℤ)
          (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
          (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D)
          (τ : ((ModuleCat.extendScalars ((algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj Q ≅
            ((ModuleCat.extendScalars ((algebraMap (Aq ⊗[R] B) D).comp
              (algebraMap Aq (Aq ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj
                ((extend A Aq).obj Q)),
          (∀ (j : ℤ) (d : D) (x : Q.X j),
            τ.hom.f j (d ⊗ₜ[A, (algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B))] x) =
              d ⊗ₜ[Aq, (algebraMap (Aq ⊗[R] B) D).comp
                (algebraMap Aq (Aq ⊗[R] B))] ((1 : Aq) ⊗ₜ[A, algebraMap A Aq] x)) →
          L.localizedComparison i ≫ HomologicalComplex.homologyMap τ.hom i =
            (e Q L K).hom ≫ K.localizedComparison i) ∧
      (∀ (Q Q' : CochainComplex (ModuleCat.{u} A) ℤ) (f : Q ⟶ Q')
          (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
          (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D)
          (L' : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q' D)
          (K' : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q') D)
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
        Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} R)) ε ≫
            K'.counit = K.counit →
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.includeRight : B →ₐ[R] Aq ⊗[R] B).toRingHom).map h ≫
              (K'.cohomologyIso i).hom =
          (K.cohomologyIso i).hom ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
              (K.derived.map (DerivedCategory.Qh.map
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
                  ((restrict R Aq).map ((extend A Aq).map f))))) ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
              (ε.app (DerivedCategory.Qh.obj
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
                  ((restrict R Aq).obj ((extend A Aq).obj Q'))))) →
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).map g ≫
            (e Q' L' K').hom =
          (e Q L K).hom ≫
            (ModuleCat.extendScalars (algebraMap (Aq ⊗[R] B) D)).map h) := by
  classical
  have hex (Q : CochainComplex (ModuleCat.{u} A) ℤ)
      (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
      (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D) :=
    exists_firstLocalization_iso R A Aq B D S i Q L K
  let e := fun Q L K ↦ (hex Q L K).choose
  have he (Q : CochainComplex (ModuleCat.{u} A) ℤ)
      (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
      (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D) :
      IsFirstLocalizationMap R A Aq B D Q L K i (e Q L K).hom :=
    (hex Q L K).choose_spec
  refine ⟨e, ?_, ?_⟩
  · intro Q L K τ hτ
    exact firstLocalization_comparison R A B Aq D i Q L K (e Q L K) (he Q L K) τ hτ
  · intro Q Q' f L K L' K' δ ε g h hδ hg hε hh
    exact firstLocalization_naturality R A B Aq D i Q Q' f L K L' K' δ ε g h
      (e Q L K) (e Q' L' K') (he Q L K) (he Q' L' K') hδ hg hε hh

end RingTensorCohomology
