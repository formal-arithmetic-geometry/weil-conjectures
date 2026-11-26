/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedModuleSkyscraper
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Stalk recovery for skyscraper complexes

The stalk of the termwise skyscraper complex at its point recovers the original complex of stalk
modules.

## References

* [Stacks Project, Tag 009A](https://stacks.math.columbia.edu/tag/009A)
-/

@[expose] public section

universe u_complex
open CategoryTheory TopologicalSpace AlgebraicGeometry
namespace SheafOfModules

/-- Send a vector to the germ of its constant global section. -/
private noncomputable def constantGermAdd (X : RingedSpace.{u_complex}) (x : X)
    (M : ModuleCat.{u_complex} (X.presheaf.stalk x)) :
    M →+ (RingedSpace.moduleStalkFunctor X x).obj (ringedModuleSkyscraper X x M) :=
  (TopCat.Presheaf.germ (ringedSkyscraperPresheafAb X x M) ⊤ x (by trivial)).hom.comp
    { toFun := fun m _ ↦ m
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

/-- Constant sections have the same germ on every neighbourhood. -/
private theorem constantGermAdd_eq (X : RingedSpace.{u_complex}) (x : X)
    (M : ModuleCat.{u_complex} (X.presheaf.stalk x)) (U : Opens X) (hx : x ∈ U)
    (m : M) :
    constantGermAdd X x M m =
      TopCat.Presheaf.germ (ringedSkyscraperPresheafAb X x M) U x hx (fun _ ↦ m) := by
  exact (TopCat.Presheaf.germ_res_apply (ringedSkyscraperPresheafAb X x M)
    (homOfLE le_top : U ⟶ ⊤) x hx (fun _ ↦ m)).symm

set_option backward.isDefEq.respectTransparency false in
/-- Taking the germ of the constant section is linear over the stalk ring. -/
private theorem constantGermAdd_linear (X : RingedSpace.{u_complex}) (x : X)
    (M : ModuleCat.{u_complex} (X.presheaf.stalk x)) (r : X.presheaf.stalk x) (m : M) :
    constantGermAdd X x M (r • m) = r • constantGermAdd X x M m := by
  obtain ⟨U, hx, a, rfl⟩ := X.presheaf.exists_germ_eq r
  rw [constantGermAdd_eq X x M U hx, constantGermAdd_eq X x M U hx]
  exact PresheafOfModules.germ_smul (R := X.presheaf)
    (ringedModuleSkyscraper X x M).val x U hx a (fun _ ↦ m)

/-- The constant-section germ as a morphism of stalk modules. -/
private noncomputable def constantGerm (X : RingedSpace.{u_complex}) (x : X)
    (M : ModuleCat.{u_complex} (X.presheaf.stalk x)) :
    M ⟶ (RingedSpace.moduleStalkFunctor X x).obj (ringedModuleSkyscraper X x M) :=
  ModuleCat.ofHom
    { toFun := constantGermAdd X x M
      map_add' := (constantGermAdd X x M).map_add
      map_smul' := constantGermAdd_linear X x M }

/-- The constant-section germ map is bijective. -/
private theorem constantGerm_bijective (X : RingedSpace.{u_complex}) (x : X)
    (M : ModuleCat.{u_complex} (X.presheaf.stalk x)) :
    Function.Bijective (constantGerm X x M) := by
  constructor
  · intro m n h
    obtain ⟨U, hx, i, j, heq⟩ := TopCat.Presheaf.germ_eq
      (ringedSkyscraperPresheafAb X x M) (U := ⊤) (V := ⊤) x
      (by trivial) (by trivial) (fun _ ↦ m) (fun _ ↦ n) h
    exact congrFun heq ⟨hx⟩
  · intro t
    obtain ⟨U, hx, s, rfl⟩ :=
      TopCat.Presheaf.exists_germ_eq (ringedSkyscraperPresheafAb X x M) t
    refine ⟨s ⟨hx⟩, ?_⟩
    change constantGermAdd X x M (s ⟨hx⟩) = _
    rw [constantGermAdd_eq X x M U hx]

/-- Pointwise module maps take constant sections to constant sections. -/
private theorem constantGerm_naturality (X : RingedSpace.{u_complex}) (x : X)
    {M N : ModuleCat.{u_complex} (X.presheaf.stalk x)} (f : M ⟶ N) :
    constantGerm X x M ≫ (RingedSpace.moduleStalkFunctor X x).map
      ((ringedModuleSkyscraperFunctor X x).map f) = f ≫ constantGerm X x N := by
  ext m
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((PresheafOfModules.toPresheaf _).map (ringedModuleSkyscraperMap X x f).val)
      (TopCat.Presheaf.germ (ringedSkyscraperPresheafAb X x M) ⊤ x (by trivial)
        (fun _ ↦ m)) = _
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  rfl

/-- Stalk recovery for the termwise skyscraper complex: its stalk at the point is isomorphic
to the original complex. -/
theorem skyscraper_complex_stalk_recovery (X : RingedSpace.{u_complex}) (x : X)
    (M : CochainComplex (ModuleCat.{u_complex} (X.presheaf.stalk x)) ℤ) :
    Nonempty (((RingedSpace.moduleStalkFunctor X x).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        (((ringedModuleSkyscraperFunctor X x).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) ≅ M) := by
  let e (N : ModuleCat.{u_complex} (X.presheaf.stalk x)) :=
    (LinearEquiv.ofBijective (constantGerm X x N).hom
      (constantGerm_bijective X x N)).toModuleIso
  refine ⟨(HomologicalComplex.Hom.isoOfComponents (fun i ↦ e (M.X i)) ?_).symm⟩
  intro i j _
  exact constantGerm_naturality X x (M.d i j)

end SheafOfModules
