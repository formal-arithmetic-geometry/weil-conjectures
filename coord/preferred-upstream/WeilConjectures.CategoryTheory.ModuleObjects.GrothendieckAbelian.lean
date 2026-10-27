/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
import WeilConjectures.CategoryTheory.Monoidal.Mod.FreePresentation

/-!

# Module objects in a closed symmetric monoidal Grothendieck abelian category

Let `C` be a closed symmetric monoidal Grothendieck abelian category whose tensor product is
additive, and let `R : C` be a commutative algebra object. The category `Mod C R` of
`R`-module objects is abelian (`WeilConjectures.CategoryTheory.ModuleObjects.Abelian`) and
symmetric monoidal for the relative tensor product `⊗_R`
(`WeilConjectures.CategoryTheory.ModuleObjects.Symmetric`). This file records that `Mod C R`
inherits the remaining properties of `C` needed by the K-flat machinery:

* `Mod.monoidalClosed`: `Mod C R` is closed monoidal;
* `Mod C R` is Grothendieck abelian, as an instance deduced from `Mod.isGrothendieckAbelian`;
* `Mod.hasFunctorialFlatResolution`: `Mod C R` admits functorial flat resolutions if `C` does.

## Sorried input

The instances `Mod.monoidalClosed` and `Mod.hasFunctorialFlatResolution` are currently `sorry`ed.
The intended arguments are:

* The internal hom `Hom_R(M, N)` is the equalizer of the two maps `[M, N] ⇉ [R ⊗ M, N]`, adjoint
  to `R ⊗ M ⊗ [M, N] ⟶ R ⊗ N ⟶ N` and to `R ⊗ M ⊗ [M, N] ⟶ M ⊗ [M, N] ⟶ N`, with the
  `R`-action induced by that of `N`.
* If `F` is flat in `C`, then `R ⊗ F` is flat in `Mod C R` because `(R ⊗ F) ⊗_R M ≅ F ⊗ M`; and
  a functorial flat resolution `P(M) ⟶ M` in `C` gives the functorial epimorphism
  `R ⊗ P(M) ⟶ R ⊗ M ⟶ M` of `R`-modules.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  {R : C} [MonObj R] [IsCommMonObj R]

/-- The relative tensor product of module objects over a commutative algebra object in a closed
symmetric monoidal Grothendieck abelian category is closed. -/
noncomputable instance monoidalClosed : MonoidalClosed (Mod C R) where
  closed M := by
    -- Keep the original signature: closedness already makes the ambient tensor additive.
    rename_i hpre _ _ _ _
    clear hpre
    have hleft (X : C) : (MonoidalCategory.tensorLeft X).Additive := by
      have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
        (MonoidalCategory.tensorLeft X)
      exact Functor.additive_of_preservesBinaryBiproducts _
    have hright (X : C) : (MonoidalCategory.tensorRight X).Additive := by
      have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
        (MonoidalCategory.tensorRight X)
      exact Functor.additive_of_preservesBinaryBiproducts _
    have : MonoidalPreadditive C :=
      { whiskerLeft_zero := fun {X Y Z} ↦ (MonoidalCategory.tensorLeft X).map_zero Y Z
        zero_whiskerRight := fun {X Y Z} ↦ (MonoidalCategory.tensorRight X).map_zero Y Z
        whiskerLeft_add := fun {X Y Z} f g ↦ (MonoidalCategory.tensorLeft X).map_add
        add_whiskerRight := fun {X Y Z} f g ↦ (MonoidalCategory.tensorRight X).map_add }
    have : IsGrothendieckAbelian.{v} (Mod C R) := isGrothendieckAbelian R
    let F₀ := forget R ⋙ MonoidalCategory.tensorRight R ⋙
      MonoidalCategory.tensorRight M.X
    let F₁ := forget R ⋙ MonoidalCategory.tensorRight M.X
    let f : F₀ ⟶ F₁ :=
      { app := fun N ↦ ((β_ N.X R).hom ≫ γ[R,N.X]) ▷ M.X
        naturality := by
          intro N N' φ
          change (φ.hom ▷ R) ▷ M.X ≫
              ((β_ N'.X R).hom ≫ γ[R,N'.X]) ▷ M.X =
            ((β_ N.X R).hom ≫ γ[R,N.X]) ▷ M.X ≫ φ.hom ▷ M.X
          rw [← comp_whiskerRight, ← comp_whiskerRight]
          congr 1
          rw [BraidedCategory.braiding_naturality_left_assoc, ← act_hom]
          simp only [Category.assoc] }
    let g : F₀ ⟶ F₁ :=
      { app := fun N ↦ (α_ N.X R M.X).hom ≫ N.X ◁ γ[R,M.X]
        naturality := by
          intro N N' φ
          change (φ.hom ▷ R) ▷ M.X ≫ (α_ N'.X R M.X).hom ≫
              N'.X ◁ γ[R,M.X] =
            ((α_ N.X R M.X).hom ≫ N.X ◁ γ[R,M.X]) ≫ φ.hom ▷ M.X
          rw [associator_naturality_left_assoc, ← whisker_exchange]
          simp only [Category.assoc] }
    let D := parallelPair f g
    have : PreservesColimitsOfSize.{v, v} D.flip :=
      ⟨fun {J} _ ↦ preservesColimitsOfShape_of_evaluation _ _ fun j ↦ by
        cases j
        · exact inferInstanceAs (PreservesColimitsOfShape J F₀)
        · exact inferInstanceAs (PreservesColimitsOfShape J F₁)⟩
    let e : D.flip ⋙ colim ≅ MonoidalCategory.tensorRight M ⋙ forget R :=
      NatIso.ofComponents
        (fun N ↦ HasColimit.isoOfNatIso (diagramIsoParallelPair (D.flip.obj N)) ≪≫
          IsColimit.coconePointUniqueUpToIso
            (t := Cofork.ofπ (tensorObjπ N M) (tensorObjπ_condition N M))
            (colimit.isColimit _) (isColimitTensorπ N M)) (by
        intro N N' φ
        apply colimit.hom_ext
        intro j
        simp only [Functor.comp_map, colim_map, Iso.trans_hom, Category.assoc,
          ι_colimMap_assoc, HasColimit.isoOfNatIso_ι_hom_assoc]
        cases j
        · simp [D, F₀, F₁, f, g, tensorObjπ_whiskerRight]
          have h := congrArg (fun k ↦ k ≫ tensorObjπ N' M) (f.naturality φ)
          simp only [Category.assoc] at h
          change (φ.hom ▷ R) ▷ M.X ≫
              ((β_ N'.X R).hom ≫ γ[R,N'.X]) ▷ M.X ≫ tensorObjπ N' M =
            ((β_ N.X R).hom ≫ γ[R,N.X]) ▷ M.X ≫
              φ.hom ▷ M.X ≫ tensorObjπ N' M at h
          simpa only [comp_whiskerRight, Category.assoc] using h
        · simp [D, F₀, F₁, f, g, tensorObjπ_whiskerRight])
    have : PreservesColimitsOfSize.{v, v}
        (MonoidalCategory.tensorRight M ⋙ forget R) := preservesColimits_of_natIso e
    have : PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight M) :=
      preservesColimits_of_reflects_of_preserves _ (forget R)
    have : PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft M) :=
      preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M).symm
    have : (MonoidalCategory.tensorLeft M).IsLeftAdjoint :=
      isLeftAdjoint_of_preservesColimits_of_isSeparating
        (isSeparator_separator (Mod C R)) _
    exact
      { rightAdj := (MonoidalCategory.tensorLeft M).rightAdjoint
        adj := Adjunction.ofIsLeftAdjoint _ }

/-- The category of module objects over a commutative algebra object in a closed symmetric
monoidal Grothendieck abelian category is Grothendieck abelian, see `Mod.isGrothendieckAbelian`:
tensoring with an object is a left adjoint, so it preserves colimits. -/
instance : IsGrothendieckAbelian.{v} (Mod C R) :=
  isGrothendieckAbelian R

/-- If `C` admits functorial flat resolutions, then so does `Mod C R`, by the free modules
`R ⊗ F` on flat objects `F` of `C`. -/
instance hasFunctorialFlatResolution [Abelian.HasFunctorialFlatResolution C] :
    Abelian.HasFunctorialFlatResolution (Mod C R) :=
  sorry

end CategoryTheory.Mod
