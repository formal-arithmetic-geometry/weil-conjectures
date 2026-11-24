/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import WeilConjectures.AlgebraicGeometry.Modules.ExtensionByZeroAdjunction
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-!
# Exact restriction of module sheaves and injective objects

## References

* [Stacks, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks, Tag 02N5](https://stacks.math.columbia.edu/tag/02N5)
* [Stacks, Tag 01AJ](https://stacks.math.columbia.edu/tag/01AJ)
* [Stacks, Tag 01AK](https://stacks.math.columbia.edu/tag/01AK)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

private theorem restriction_injective (X : Scheme.{u}) (U : X.Opens)
    (I : SheafOfModules.{u} X.ringCatSheaf) (hI : Injective I) : Injective (I.over U) := by
  let P := SheafOfModules.extensionByZeroPresheaf.{u} X.ringCatSheaf U
  have : P.PreservesMonomorphisms := by
    constructor
    intro F G f hf
    have : Mono f.val := Functor.map_mono (SheafOfModules.forget _) f
    apply PresheafOfModules.mono_of_injective
    intro V
    dsimp [P, SheafOfModules.extensionByZeroPresheaf,
      SheafOfModules.extensionByZeroPresheafHom,
      SheafOfModules.extensionByZeroPresheafHomApp]
    exact (DirectSum.lmap_injective _).mpr fun φ ↦
      PresheafOfModules.injective_of_mono f.val _
  obtain ⟨_, adj, _⟩ := module_extensionByZero_adjunction X U
  exact adj.map_injective I hI

private theorem restriction_resolution (X : Scheme.{u}) (U : X.Opens)
    (F : SheafOfModules.{u} X.ringCatSheaf) (I : InjectiveResolution F) :
    ∃ (J : InjectiveResolution (F.over U))
      (h : J.cocomplex = ((SheafOfModules.overFunctor.{u} X.ringCatSheaf U).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex),
      J.ι.f 0 ≫ eqToHom (congrArg (fun K ↦ K.X 0) h) = (I.ι.f 0).over U := by
  let R := SheafOfModules.overFunctor.{u} X.ringCatSheaf U
  have : R.PreservesInjectiveObjects := ⟨fun h ↦ restriction_injective X U _ h⟩
  let J : InjectiveResolution (R.obj F) :=
    { cocomplex := (R.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
      injective := fun n ↦ R.injective_obj (I.cocomplex.X n)
      ι := (HomologicalComplex.singleMapHomologicalComplex R (ComplexShape.up ℕ) 0).inv.app F ≫
        (R.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι }
  refine ⟨J, rfl, ?_⟩
  simp [J, R, HomologicalComplex.singleMapHomologicalComplex_inv_app_self]

/-- Restriction to an open `U` (`SheafOfModules.overFunctor`, modules over `𝒪_X.over U`)
is additive and exact, preserves injective objects, and sends an injective resolution
to its termwise restriction with restricted augmentation. Direct image along the
inclusion (`SheafOfModules.pushforward (SheafOfModules.pushforwardOver U)`) also preserves
injective objects. -/
theorem module_open_restriction_injectives (X : Scheme.{u}) (U : X.Opens) :
    (SheafOfModules.overFunctor.{u} X.ringCatSheaf U).Additive ∧
    (∀ S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf), S.Exact →
      (S.map (SheafOfModules.overFunctor.{u} X.ringCatSheaf U)).Exact) ∧
    (∀ I : SheafOfModules.{u} X.ringCatSheaf, Injective I → Injective (I.over U)) ∧
    (∀ J : SheafOfModules.{u} (X.ringCatSheaf.over U), Injective J →
      Injective ((SheafOfModules.pushforward.{u}
        (SheafOfModules.pushforwardOver (R := X.ringCatSheaf) U)).obj J)) ∧
    (∀ (F : SheafOfModules.{u} X.ringCatSheaf) (I : InjectiveResolution F),
      ∃ (J : InjectiveResolution (F.over U))
        (h : J.cocomplex = ((SheafOfModules.overFunctor.{u} X.ringCatSheaf U).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex),
        J.ι.f 0 ≫ eqToHom (congrArg (fun K ↦ K.X 0) h) = (I.ι.f 0).over U) := by
  refine ⟨moduleOverFunctor_additive X.toRingedSpace U, ?_, ?_, ?_, ?_⟩
  · intro S hS
    exact hS.map (SheafOfModules.overFunctor.{u} X.ringCatSheaf U)
  · exact restriction_injective X U
  · intro J hJ
    have : CategoryTheory.Limits.PreservesFiniteLimits
        (SheafOfModules.overFunctor.{u} X.ringCatSheaf U) :=
      moduleOverFunctor_limits X.toRingedSpace U
    exact (Adjunction.preservesInjectiveObjects_of_preservesFiniteLimits
      (SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) U)).injective_obj hJ
  · exact restriction_resolution X U

end AlgebraicGeometry.Scheme.Modules
