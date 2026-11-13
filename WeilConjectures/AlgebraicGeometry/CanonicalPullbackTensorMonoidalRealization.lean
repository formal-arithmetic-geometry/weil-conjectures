/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalModel

/-! # Realizing the canonical tensor comparison by a monoidal structure

Source: Stacks Project, Cohomology, Tag 079U.
-/

@[expose] public section

universe u w
open CategoryTheory MonoidalCategory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
namespace AlgebraicGeometry
attribute [local instance] pullbackDescentModuleTensor moduleSymmetric modulePreadditive
  moduleClosed moduleGrothendieck moduleResolutions moduleDerivedMonoidal pullbackDescentQLax

/-- The canonical pullback tensor comparison is the inverse tensorator of a
monoidal structure on the recorded derived pullback functor. -/
theorem canonicalPullbackTensor_monoidal_realization
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {T X : Scheme.{u}} (g : T ⟶ X)
    (τ : ∀ A B : schemeDerivedCategory X,
      (derivedPullback g).obj (A ⊗ B) ⟶
        (derivedPullback g).obj A ⊗ (derivedPullback g).obj B)
    (hτ : IsCanonicalPullbackTensorComparison g τ) :
    ∃ m : (derivedPullback g).CoreMonoidal,
      ∀ A B : schemeDerivedCategory X, (m.μIso A B).inv = τ A B := by
  classical
  obtain ⟨m, hm⟩ := exists_derivedPullbackMonoidalModel.{u, w} g
  dsimp only [IsDerivedPullbackMonoidalModel] at hm
  obtain ⟨F, hF, hmap, hAdd, mF, hμ, ε, hε, φ, hφ, hcoord⟩ := hm
  have hF' : F = Scheme.Modules.tensorPullback g :=
    CategoryTheory.Functor.ext hF (fun M N a ↦ hmap a)
  subst F
  have := hε
  have hshared :=
    Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) g
  change (derivedPullback g).IsLeftDerivedFunctor (SingleComplexBaseChange.counit g)
    (HomotopyCategory.quasiIso _ (.up ℤ)) at hshared
  have := hshared
  let δ := Functor.leftDerivedUnique (derivedPullback g) (derivedPullback g) ε
    (SingleComplexBaseChange.counit g) (HomotopyCategory.quasiIso _ (.up ℤ))
  have hδ (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
      δ.hom.app (DerivedCategory.Q.obj P) ≫
        (SingleComplexBaseChange.counit g).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
        ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
    change δ.hom.app (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫ _ = _
    simpa only [δ, Functor.leftDerivedUnique, Functor.leftDerivedNatIso,
      Iso.refl_hom, NatTrans.id_app, Category.comp_id] using
      Functor.leftDerivedNatTrans_app (derivedPullback g) (derivedPullback g) ε
        (SingleComplexBaseChange.counit g) (HomotopyCategory.quasiIso _ (.up ℤ))
        (𝟙 _) ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  let := m.toMonoidal
  let m' := Functor.Monoidal.coreMonoidalTransport δ
  have hc : IsCanonicalPullbackTensorComparison g (fun A B ↦ (m'.μIso A B).inv) := by
    dsimp only [IsCanonicalPullbackTensorComparison]
    refine ⟨?_, ?_⟩
    · intro P N hP hN
      refine ⟨φ P N, ?_, ?_⟩
      · intro p q n h
        simpa only [hμ, eqToHom_refl, Category.id_comp, tensorHom_id,
          Category.comp_id, id_whiskerRight] using hφ P N p q n h
      · have heq := hcoord P N hP hN
        have heq' :
            (derivedPullback g).map (pullbackTensorModelMap X P N) ≫
              ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
                (pullbackTensorTotal X P N)) ≫ DerivedCategory.Q.map (φ P N).hom =
            (m.μIso (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N)).inv ≫
              (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ⊗ₘ
                ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj N)) ≫
              pullbackTensorModelMap T
                (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P)
                (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N) := by
          apply (cancel_epi (m.μIso (DerivedCategory.Q.obj P)
            (DerivedCategory.Q.obj N)).hom).1
          simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
          dsimp only [pullbackTensorModelMap, pullbackTensorTotal]
          simpa only [cast_eq, Category.assoc] using heq
        rw [Functor.Monoidal.coreMonoidalTransport_μIso_inv]
        simp only [cast_eq, Category.assoc]
        rw [tensorHom_comp_tensorHom_assoc, hδ P, hδ N]
        apply (cancel_epi (δ.hom.app
          (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj N))).1
        simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
        rw [← δ.hom.naturality (pullbackTensorModelMap X P N)]
        simp only [Category.assoc]
        rw [← Category.assoc (δ.hom.app (DerivedCategory.Q.obj
          (pullbackTensorTotal X P N)))
          ((SingleComplexBaseChange.counit g).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj (pullbackTensorTotal X P N)))
          (DerivedCategory.Q.map (φ P N).hom), hδ (pullbackTensorTotal X P N)]
        exact heq'
    · intro A A' B B' a b
      let := m'.toMonoidal
      exact (Functor.OplaxMonoidal.δ_natural (derivedPullback g) a b).symm
  have heq := hc.unique hτ
  refine ⟨m', ?_⟩
  intro A B
  exact congrFun (congrFun heq A) B

end AlgebraicGeometry
