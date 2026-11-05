/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.Localization

import WeilConjectures.Algebra.Homology.BaseTensorCoefficientNaturalMap
import WeilConjectures.Algebra.Homology.ScalarExtensionDerivedRestriction

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
  have _hF := hF
  let r := restrictScalars.{u} (algebraMap R A)
  let e := extendScalars.{u, u, u} (algebraMap R B)
  let l := extendScalars.{u, u, u} ((algebraMap (A ⊗[R] B) D).comp
    (algebraMap A (A ⊗[R] B)))
  let s := restrictScalars.{u} (algebraMap (A ⊗[R] B) D) ⋙
    restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom
  obtain ⟨γ, hγ⟩ := exists_baseTensorCoefficientNaturalMap R A B D
  let γh : r.mapHomotopyCategory (.up ℤ) ⋙ e.mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh ⟶
      l.mapHomotopyCategory (.up ℤ) ⋙ s.mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh :=
    CategoryTheory.Quotient.natTransLift _
      (Functor.whiskerRight γ (HomotopyCategory.quotient _ (.up ℤ) ⋙ DerivedCategory.Qh))
  let G := r.mapDerivedCategory ⋙ F
  let T := L ⋙ s.mapDerivedCategory
  let α : DerivedCategory.Qh ⋙ T ⟶
      l.mapHomotopyCategory (.up ℤ) ⋙ s.mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight ε s.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (l.mapHomotopyCategory (.up ℤ))
        s.mapDerivedCategoryFactorsh.hom ≫ (Functor.associator _ _ _).inv
  let : T.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    scalarExtensionDerivedRestriction _ s L ε hL
  let τ : DerivedCategory.Qh ⋙ G ⟶
      l.mapHomotopyCategory (.up ℤ) ⋙ s.mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight r.mapDerivedCategoryFactorsh.hom F ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (r.mapHomotopyCategory (.up ℤ)) δ ≫
      (Functor.associator _ _ _).inv ≫ γh
  let η := T.leftDerivedLift α (HomotopyCategory.quasiIso _ (.up ℤ)) G τ
  refine ⟨η, ?_⟩
  intro P β hβ
  have hb : β = γ.app P := by
    ext j x
    induction x using TensorProduct.inductionOn with
    | tmul b p => exact (hβ j b p).trans (hγ P j b p).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  subst β
  have h := T.leftDerived_fac_app α (HomotopyCategory.quasiIso _ (.up ℤ)) G τ
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  dsimp only [η, α, τ, G, T, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app] at h
  simp only [Category.id_comp, Category.comp_id] at h
  change η.app (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫ s.mapDerivedCategory.map
      (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      s.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          ((l.mapHomologicalComplex (.up ℤ)).obj P)) =
    F.map (r.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫ δ.app _ ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map (γ.app P)) at h
  have hn := η.naturality ((DerivedCategory.quotientCompQhIso _).inv.app P)
  have h' := congrArg (fun f ↦
    G.map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫ f ≫
      (DerivedCategory.quotientCompQhIso _).hom.app
        ((s.mapHomologicalComplex (.up ℤ)).obj
          ((l.mapHomologicalComplex (.up ℤ)).obj P))) h
  rw [Functor.mapDerivedCategoryFactorsh_hom_app,
    Functor.mapDerivedCategoryFactorsh_hom_app] at h'
  have hr : (r.mapHomotopyCategoryFactors (.up ℤ)).inv.app P = 𝟙 _ := rfl
  have hs : (s.mapHomotopyCategoryFactors (.up ℤ)).inv.app
      ((l.mapHomologicalComplex (.up ℤ)).obj P) = 𝟙 _ := rfl
  have hmapr : DerivedCategory.Qh.map
      (𝟙 ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((r.mapHomologicalComplex (.up ℤ)).obj P))) = 𝟙 _ := DerivedCategory.Qh.map_id _
  have hmaps : DerivedCategory.Qh.map
      (𝟙 ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((s.mapHomologicalComplex (.up ℤ)).obj
          ((l.mapHomologicalComplex (.up ℤ)).obj P)))) = 𝟙 _ := DerivedCategory.Qh.map_id _
  simp only [hr, hs, Category.assoc] at h'
  erw [hmapr, hmaps] at h'
  simp only [Category.comp_id, Iso.inv_hom_id_app] at h'
  erw [DerivedCategory.quotientCompQhIso_hom_naturality (γ.app P)] at h'
  rw [reassoc_of% hn] at h'
  simp only [G, T, Functor.comp_map, Functor.map_comp, Category.assoc] at h'
  rw [← F.map_comp_assoc, ← r.mapDerivedCategory.map_comp, Iso.inv_hom_id_app,
    r.mapDerivedCategory.map_id, F.map_id, Category.id_comp] at h'
  have hmape : DerivedCategory.Qh.map
      (𝟙 ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((e.mapHomologicalComplex (.up ℤ)).obj
          ((r.mapHomologicalComplex (.up ℤ)).obj P)))) = 𝟙 _ := DerivedCategory.Qh.map_id _
  have hmapl : DerivedCategory.Qh.map
      (𝟙 ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((l.mapHomologicalComplex (.up ℤ)).obj P))) = 𝟙 _ := DerivedCategory.Qh.map_id _
  simp only [Iso.trans_inv, Iso.app_inv, Iso.symm_inv,
    Functor.mapHomotopyCategoryFactors_hom_app]
  erw [hmape, hmapl]
  simpa only [Functor.map_id, Category.id_comp, Category.comp_id,
    Functor.map_comp, Category.assoc] using h'.symm

end ModuleCat
