/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Abelian.Images
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitEpi
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitStalkKernel
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Kernel of the closed immersion pullback unit

## References

* Stacks Project, Tags 04CJ and 08KS
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
/-- The geometric part of the closed immersion quotient theorem: the unit is epi
and the multiplication image is its kernel (Stacks, Tags 04CJ and 08KS). -/
theorem closedImmersion_unit_kernel {Y Z : Scheme.{w}} (i : Z ⟶ Y)
    [IsClosedImmersion i] :
    let adj : tensorPullback i ⊣ pushforward i :=
      Classical.choice (nonempty_tensorPullbackAdjunction i)
    let J : Y.IdealSheafData := i.ker
    let μ : ∀ F : Y.Modules, J.toModules ⊗ F ⟶ F := fun F =>
      J.toModulesι ▷ F ≫ (λ_ F).hom
    ∀ F : Y.Modules,
      Epi (adj.unit.app F) ∧
        (∃ w : image.ι (μ F) ≫ adj.unit.app F = 0,
          Nonempty (IsLimit (KernelFork.ofι (image.ι (μ F)) w))) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  dsimp
  intro F
  refine ⟨closedImmersion_unit_epi i F, ?_⟩
  let adj := Classical.choice (nonempty_tensorPullbackAdjunction i)
  let μ : i.ker.toModules ⊗ F ⟶ F := i.ker.toModulesι ▷ F ≫ (λ_ F).hom
  have hr (x : Y) :
      let S := RingedSpace.moduleStalkFunctor Y.toRingedSpace x
      LinearMap.range (S.map (image.ι μ)).hom =
        LinearMap.ker (S.map (adj.unit.app F)).hom := by
    let S := RingedSpace.moduleStalkFunctor Y.toRingedSpace x
    have ha := ((RingedSpace.module_stalk_exact Y.toRingedSpace μ).2.2.2.1 x).2.2
    have he : S.map (Abelian.image.ι μ) =
        (S.mapIso (Abelian.imageIsoImage μ)).hom ≫ S.map (image.ι μ) := by
      exact (congrArg S.map (Abelian.imageIsoImage_hom_comp_image_ι μ).symm).trans
        (S.map_comp _ _)
    rw [he, ModuleCat.hom_comp, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr
        ((ModuleCat.epi_iff_surjective _).mp inferInstance))] at ha
    exact ha.trans (closedImmersion_unit_stalk_kernel i F x)
  have hw : image.ι μ ≫ adj.unit.app F = 0 := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext m
    apply TopCat.Presheaf.section_ext
      ⟨((pushforward i).obj ((tensorPullback i).obj F)).presheaf,
        ((pushforward i).obj ((tensorPullback i).obj F)).isSheaf⟩ (Opposite.unop V)
    intro x hx
    have hz := LinearMap.range_le_ker_iff.mp (le_of_eq (hr x))
    have heq := LinearMap.congr_fun hz
      (TopCat.Presheaf.germ (image μ).presheaf (Opposite.unop V) x hx m)
    change (TopCat.Presheaf.stalkFunctor Ab x).map (adj.unit.app F).mapPresheaf
      ((TopCat.Presheaf.stalkFunctor Ab x).map (image.ι μ).mapPresheaf
        (TopCat.Presheaf.germ (image μ).presheaf (Opposite.unop V) x hx m)) = 0 at heq
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply] at heq
    change TopCat.Presheaf.germ
      ((pushforward i).obj ((tensorPullback i).obj F)).presheaf (Opposite.unop V) x hx
        ((adj.unit.app F).app (Opposite.unop V) ((image.ι μ).app (Opposite.unop V) m)) =
      TopCat.Presheaf.germ
        ((pushforward i).obj ((tensorPullback i).obj F)).presheaf (Opposite.unop V) x hx 0
    erw [map_zero]
    exact heq
  refine ⟨hw, ⟨?_⟩⟩
  let T := ShortComplex.mk (image.ι μ) (adj.unit.app F) hw
  have ht : T.Exact := by
    apply ((RingedSpace.module_stalk_exact Y.toRingedSpace (image.ι μ)).2.2.2.2
      _ _ _ hw).mpr
    intro x
    have : (RingedSpace.moduleStalkFunctor Y.toRingedSpace x).PreservesZeroMorphisms :=
      RingedSpace.moduleStalkFunctor_preservesZeroMorphisms Y.toRingedSpace x
    apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
    exact hr x
  exact ht.fIsKernel

end
end AlgebraicGeometry.Scheme.Modules
