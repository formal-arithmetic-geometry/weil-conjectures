/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Comparison in the derived category, before homology -/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace ModuleCat

variable (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} D)]

/-- Derived coefficient chain comparison.
Source: Stacks Project, Tag 065Y, construction of equation-comparison-map
(Tag 065Z); Tag 06Y6; perfect.tex equation-bc (Tag 0DJ7).
(blueprint: lem-pc-base-tensor-derived-chain-comparison).

Proof: resolve an A-complex by an A-K-flat complex U and its restriction by an
R-K-flat complex V. The map V to Res(U) induces on pure tensors the displayed
coefficient map into Res(D tensor_A U). Invert the resolution counits and the
quasi-isomorphism U to P. Comparison maps of resolutions commute with this map
on pure tensors, and tensor induction proves the commuting squares. Applying
the same argument to roofs proves naturality and independence of refinements.
The augmentation squares and counit naturality give the displayed derived
equation at P, without assuming the counit at P is invertible. Finally use the
unique counit-compatible isomorphisms of left derived functors to transport the
construction to the supplied universal pairs F and L. -/
theorem exists_baseTensorDerivedChainComparison
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (δ : DerivedCategory.Qh ⋙ F ⟶
      (extendScalars.{u, u, u} (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    (hF : F.IsLeftDerivedFunctor δ (HomotopyCategory.quasiIso _ (.up ℤ)))
    (L : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} D))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (extendScalars.{u, u, u} ((algebraMap (A ⊗[R] B) D).comp
        (algebraMap A (A ⊗[R] B)))).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hL : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))) :
    ∃ η : (restrictScalars.{u} (algebraMap R A)).mapDerivedCategory ⋙ F ⟶
        L ⋙ (restrictScalars.{u} (algebraMap (A ⊗[R] B) D) ⋙
          restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).mapDerivedCategory,
      ∀ (P : CochainComplex (ModuleCat.{u} A) ℤ)
        (β : ((extendScalars.{u, u, u} (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
            (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj P) ⟶
          ((restrictScalars.{u} (algebraMap (A ⊗[R] B) D) ⋙
            restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).mapHomologicalComplex
              (.up ℤ)).obj
            (((extendScalars.{u, u, u} ((algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj P)),
        (∀ (j : ℤ) (b : B) (p : P.X j),
          β.f j (b ⊗ₜ[R, algebraMap R B] p) =
            (algebraMap (A ⊗[R] B) D (Algebra.TensorProduct.includeRight b) ⊗ₜ[A,
              (algebraMap (A ⊗[R] B) D).comp (algebraMap A (A ⊗[R] B))] p)) →
        F.map (((DerivedCategory.quotientCompQhIso _).app _ ≪≫
          (restrictScalars.{u} (algebraMap R A)).mapDerivedCategoryFactors.symm.app P).inv) ≫
          δ.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
            (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj P)) ≫
          DerivedCategory.Qh.map
            (((extendScalars.{u, u, u} (algebraMap R B)).mapHomotopyCategoryFactors
              (.up ℤ)).hom.app _) ≫
          (DerivedCategory.quotientCompQhIso _).hom.app _ ≫ DerivedCategory.Q.map β =
        η.app (DerivedCategory.Q.obj P) ≫
          (restrictScalars.{u} (algebraMap (A ⊗[R] B) D) ⋙
            restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).mapDerivedCategory.map
            (L.map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
              ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
              DerivedCategory.Qh.map
                (((extendScalars.{u, u, u} ((algebraMap (A ⊗[R] B) D).comp
                  (algebraMap A (A ⊗[R] B)))).mapHomotopyCategoryFactors
                    (.up ℤ)).hom.app P) ≫
              (DerivedCategory.quotientCompQhIso _).hom.app _) ≫
          (Functor.mapDerivedCategoryFactors
            (restrictScalars.{u} (algebraMap (A ⊗[R] B) D) ⋙
              restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom)).hom.app _ := by
  sorry

end ModuleCat
