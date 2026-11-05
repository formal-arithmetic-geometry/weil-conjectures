/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Basis.Prod
public import WeilConjectures.Algebra.Homology.BifunctorSingleNaturality
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatDevissage
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# The projection map at flat modules placed in degree zero

Let `F : Mod_Λ ⥤ D` be an exact strong monoidal functor to a monoidal Grothendieck abelian
category, preserving flat objects and left adjoint, let `Γ : D ⥤ Mod_Λ` be a left exact functor
whose derived functors `RᵠΓ` commute with filtered colimits, and let `adj : D(F) ⊣ RΓ`. For `E`
bounded below and `M` a flat `Λ`-module, the projection map
`τ_E : RΓ E ⊗ᴸ M[0] ⟶ RΓ (E ⊗ᴸ D(F) M[0])`
(`CategoryTheory.Functor.mapDerivedCategoryProjectionMap`) is an isomorphism
(`CategoryTheory.Functor.isIso_mapDerivedCategoryProjectionMap_app_singleFunctor_of_flat`).

Indeed it is an isomorphism at the unit, hence at the finite free modules `Λ^k`, and both sides,
in a fixed degree `n`, commute with filtered colimits of flat modules: writing `RΓ E` as `Q(L)`
for a K-flat complex `L`, the source is `Hⁿ(L ⊗ M)`; writing `E` as `Q(I)` for a bounded below
complex `I` of injective objects, the target is `Hⁿ(Γ(I ⊗ F M))`, the complex `I ⊗ F M` being a
bounded below complex of `Γ`-acyclic objects. By Lazard's theorem
(`ModuleCat.FinFreeOver.isColimitCocone`), a flat module is a filtered colimit of finite free
modules.
-/

@[expose] public section

universe u u₂

open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory

open scoped CategoryTheory.Functor

namespace ModuleCat

variable (R : Type u) [CommRing R]

end ModuleCat

namespace CategoryTheory

namespace Functor

/-- For a complex `L`, the functor `M ↦ L ⊗ M` (tensoring termwise on the right) from `C` to
cochain complexes. -/
@[simps]
noncomputable def tensorRightComplex {C : Type*} [Category* C] [MonoidalCategory C]
    [Preadditive C] [MonoidalPreadditive C] (L : CochainComplex C ℤ) :
    C ⥤ CochainComplex C ℤ where
  obj M := (((curriedTensor C).flip.obj M).mapHomologicalComplex (.up ℤ)).obj L
  map f := (NatTrans.mapHomologicalComplex ((curriedTensor C).flip.map f) (.up ℤ)).app L
  map_id M := by
    ext
    simp
  map_comp f g := by
    ext
    simp

instance {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]
    (L : CochainComplex C ℤ) (n : ℤ) [MonoidalClosed C] (J : Type*) [Category* J] :
    PreservesColimitsOfShape J (tensorRightComplex L ⋙ HomologicalComplex.eval C (.up ℤ) n) :=
  preservesColimitsOfShape_of_natIso (F := tensorLeft (L.X n)) (NatIso.ofComponents
    (fun _ ↦ Iso.refl _) (by intros; simp))

instance {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]
    [MonoidalClosed C] (L : CochainComplex C ℤ) (J : Type*) [Category* J] :
    PreservesColimitsOfShape J (tensorRightComplex L) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ fun _ ↦ inferInstance

end Functor

namespace DerivedCategory

variable {C : Type u₂} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]

end DerivedCategory

namespace Functor

variable {Λ : Type (u + 1)} [CommRing Λ]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]
  {F : ModuleCat.{u + 1} Λ ⥤ D} [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
  {Γ : D ⥤ ModuleCat.{u + 1} Λ} [Γ.Additive] [PreservesFiniteLimits Γ]

end Functor

end CategoryTheory

namespace CategoryTheory.Functor

section Unit

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasInjectiveResolutions A] [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B]
  [Abelian.HasKInjectiveResolutions A] (Γ : A ⥤ B) [Γ.Additive] [PreservesFiniteLimits Γ]

/-- **Bounded below acyclic complexes compute the right derived functor**: the unit
`Γ(T) ⟶ RΓ(T)` is an isomorphism at a bounded below complex `T` of `Γ`-acyclic objects. -/
lemma isIso_rightDerivedFunctorUnit_app_of_isStrictlyGE (T : CochainComplex A ℤ) (a : ℤ)
    [T.IsStrictlyGE a] (hT : ∀ n, Γ.rightAcyclic (T.X n)) :
    IsIso (Γ.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient A (.up ℤ)).obj T)) := by
  obtain ⟨I, ι, _, hI, _⟩ := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective T a
  have : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  have := Γ.quasiIso_map_of_rightAcyclic ι a hT (fun n ↦ rightAcyclic_of_injective _)
  have h₁ : IsIso (Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map ι)) :=
    Localization.inverts Qh (HomotopyCategory.quasiIso A _) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
        ((HomologicalComplex.mem_quasiIso_iff _).2 inferInstance))
  have h₂ : IsIso ((Γ.mapHomotopyCategory (.up ℤ) ⋙ Qh).map
      ((HomotopyCategory.quotient A (.up ℤ)).map ι)) := by
    dsimp only [Functor.comp_map]
    rw [Functor.mapHomotopyCategory_map]
    exact Localization.inverts Qh (HomotopyCategory.quasiIso B _) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
        ((HomologicalComplex.mem_quasiIso_iff _).2 inferInstance))
  have h₃ : IsIso ((Qh ⋙ Γ.rightDerivedFunctor).map
      ((HomotopyCategory.quotient A (.up ℤ)).map ι)) := by
    dsimp only [Functor.comp_map]
    infer_instance
  have h₄ : IsIso (Γ.rightDerivedFunctorUnit.app
    ((HomotopyCategory.quotient A (.up ℤ)).obj I)) := inferInstance
  exact IsIso.of_isIso_fac_right (h := (Γ.mapHomotopyCategory (.up ℤ) ⋙ Qh).map
    ((HomotopyCategory.quotient A (.up ℤ)).map ι) ≫ Γ.rightDerivedFunctorUnit.app _)
    (Γ.rightDerivedFunctorUnit.naturality _).symm

end Unit

open DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]
  {F : ModuleCat.{u + 1} Λ ⥤ D} [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
  {Γ : D ⥤ ModuleCat.{u + 1} Λ} [Γ.Additive] [PreservesFiniteLimits Γ]
  (adj : F.mapDerivedCategory ⊣ Γ.rightDerivedFunctor)

end CategoryTheory.Functor
