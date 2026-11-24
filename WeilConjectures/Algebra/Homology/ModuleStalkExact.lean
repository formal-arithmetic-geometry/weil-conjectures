/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Exactness of stalks of sheaves of modules

## References

* Stacks Project, Modules, Section 17.3 (Tag 01AF) and Tag 01AG
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat.Presheaf Opposite
noncomputable section
namespace AlgebraicGeometry.RingedSpace

private instance module_toSheaf_preservesFiniteColimits (X : RingedSpace.{u}) :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{u} (moduleRings X)) :=
  (CategoryTheory.moduleSheaves_colimits_forgetful (moduleRings X)).2.2.1

private theorem stalk_comp_forget (X : RingedSpace.{u}) (x : X) :
    moduleStalkFunctor X x ⋙ forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u} =
      SheafOfModules.toSheaf (moduleRings X) ⋙
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
          TopCat.Presheaf.stalkFunctor (X := X.carrier) AddCommGrpCat.{u} x) := by
  rfl

private instance stalk_preservesFiniteLimits (X : RingedSpace.{u}) (x : X) :
    PreservesFiniteLimits (moduleStalkFunctor X x) := by
  let A : ModuleCat.{u} (X.presheaf.stalk x) ⥤ AddCommGrpCat.{u} :=
    forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}
  have hb : PreservesFiniteLimits
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
        TopCat.Presheaf.stalkFunctor (X := X.carrier) AddCommGrpCat.{u} x) := inferInstance
  have : PreservesFiniteLimits (moduleStalkFunctor X x ⋙ A) := by
    rw [stalk_comp_forget]
    exact comp_preservesFiniteLimits (SheafOfModules.toSheaf (moduleRings X))
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
        TopCat.Presheaf.stalkFunctor (X := X.carrier) AddCommGrpCat.{u} x)
  exact preservesFiniteLimits_of_reflects_of_preserves _ A

private instance stalk_preservesFiniteColimits (X : RingedSpace.{u}) (x : X) :
    PreservesFiniteColimits (moduleStalkFunctor X x) := by
  let A : ModuleCat.{u} (X.presheaf.stalk x) ⥤ AddCommGrpCat.{u} :=
    forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}
  have hb : PreservesFiniteColimits
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
        TopCat.Presheaf.stalkFunctor (X := X.carrier) AddCommGrpCat.{u} x) := inferInstance
  have : PreservesFiniteColimits (moduleStalkFunctor X x ⋙ A) := by
    rw [stalk_comp_forget]
    exact comp_preservesFiniteColimits (SheafOfModules.toSheaf (moduleRings X))
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
        TopCat.Presheaf.stalkFunctor (X := X.carrier) AddCommGrpCat.{u} x)
  exact preservesFiniteColimits_of_reflects_of_preserves _ A

/-- Sectionwise injectivity implies stalkwise injectivity. Stalks preserve the canonical kernel,
cokernel and image, and detect exactness of a complex at its middle term. -/
theorem module_stalk_exact (X : RingedSpace.{u})
    {F G : SheafOfModules.{u} (moduleRings X)} (φ : F ⟶ G) :
    ((∀ (U : Opens X),
        Function.Injective (ConcreteCategory.hom (φ.val.app (Opposite.op U)))) →
      ∀ (x : X), Mono ((moduleStalkFunctor X x).map φ)) ∧
    (∀ (x : X),
      Mono ((moduleStalkFunctor X x).map (kernel.ι φ)) ∧
      ((ShortComplex.mk
          ((moduleStalkFunctor X x).map (kernel.ι φ))
          ((moduleStalkFunctor X x).map φ) (by
            rw [← (moduleStalkFunctor X x).map_comp]
            simp)).Exact)) ∧
    (∀ (x : X),
      Epi ((moduleStalkFunctor X x).map (cokernel.π φ)) ∧
      ((ShortComplex.mk
          ((moduleStalkFunctor X x).map φ)
          ((moduleStalkFunctor X x).map (cokernel.π φ)) (by
            rw [← (moduleStalkFunctor X x).map_comp]
            simp)).Exact)) ∧
    (∀ (x : X),
      Epi ((moduleStalkFunctor X x).map (Abelian.factorThruImage φ)) ∧
      Mono ((moduleStalkFunctor X x).map (Abelian.image.ι φ)) ∧
      LinearMap.range ((moduleStalkFunctor X x).map (Abelian.image.ι φ)).hom =
        LinearMap.range ((moduleStalkFunctor X x).map φ).hom) ∧
    (∀ (H : SheafOfModules.{u} (moduleRings X)) (χ : F ⟶ G) (ψ : G ⟶ H),
      ∀ (h : χ ≫ ψ = 0),
        (ShortComplex.mk χ ψ h).Exact ↔
          ∀ (x : X), ((ShortComplex.mk χ ψ h).map (moduleStalkFunctor X x)).Exact) := by
  -- Transfer exactness through the faithful functors to abelian sheaves and groups.
  have detect (S : ShortComplex (SheafOfModules.{u} (moduleRings X))) :
      S.Exact ↔ ∀ x : X, (S.map (moduleStalkFunctor X x)).Exact := by
    let T := SheafOfModules.toSheaf (moduleRings X)
    rw [← S.exact_map_iff_of_faithful T,
      TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
    apply forall_congr'
    intro x
    let A : ModuleCat.{u} (X.presheaf.stalk x) ⥤ AddCommGrpCat.{u} :=
      forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}
    rw [← (S.map (moduleStalkFunctor X x)).exact_map_iff_of_faithful A]
    have hb : Functor.PreservesZeroMorphisms
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
          TopCat.Presheaf.stalkFunctor (X := X.carrier) AddCommGrpCat.{u} x) := inferInstance
    change ((S.map (SheafOfModules.toSheaf (moduleRings X))).map
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
        TopCat.Presheaf.stalkFunctor (X := X.carrier) AddCommGrpCat.{u} x)).Exact ↔
      ((S.map (moduleStalkFunctor X x)).map
        (forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u})).Exact
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hinj x
    have : Mono φ := by
      constructor
      intro Z a b hab
      ext U z
      apply hinj (unop U)
      exact congrArg (fun f => f.val.app U z) hab
    exact Functor.map_mono (moduleStalkFunctor X x) φ
  · intro x
    refine ⟨Functor.map_mono _ _, ?_⟩
    exact (ShortComplex.exact_kernel φ).map (moduleStalkFunctor X x)
  · intro x
    refine ⟨Functor.map_epi _ _, ?_⟩
    exact (ShortComplex.exact_cokernel φ).map (moduleStalkFunctor X x)
  · intro x
    have := Functor.map_epi (moduleStalkFunctor X x) (Abelian.factorThruImage φ)
    refine ⟨inferInstance, Functor.map_mono _ _, ?_⟩
    have hf := (ModuleCat.epi_iff_surjective
      ((moduleStalkFunctor X x).map (Abelian.factorThruImage φ))).mp inferInstance
    have he : (moduleStalkFunctor X x).map (Abelian.factorThruImage φ) ≫
        (moduleStalkFunctor X x).map (Abelian.image.ι φ) =
          (moduleStalkFunctor X x).map φ := by
      rw [← Functor.map_comp, Abelian.image.fac]
    rw [← he, ModuleCat.hom_comp, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr hf)]
  · intro H χ ψ h
    exact detect (ShortComplex.mk χ ψ h)

end AlgebraicGeometry.RingedSpace
