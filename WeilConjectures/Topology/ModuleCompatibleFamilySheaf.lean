/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.Topology.ModuleCompatibleFamilyPresheaf
import WeilConjectures.Topology.ModuleCompatibleFamilySmall
import WeilConjectures.Topology.ModuleCompatibleFamilySheafCondition

/-! # The sheaf of compatible local module sections

The compatible-family equalizer of local sheaves of modules along overlap maps is represented by
a sheaf of modules.

## Implementation details

On an open `V` the sections are the families in `Fi i (V ∩ U i)` identified by every overlap
map; they form a submodule, and gluing is componentwise. To land in universe `max u v`, the
explicit module of compatible families is shown to be small using a subcover indexed by the
points of `X`, and then shrunk.

## References

* [Stacks Project, Tags 00AL and 00AM](https://stacks.math.columbia.edu/tag/00AL)
-/

@[expose] public section

universe u v w

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The compatible-family equalizer is represented by a module sheaf with projections.
No diagonal or cocycle assumption is needed for this construction. -/
theorem module_compatible_family_sheaf
    (X : RingedSpace.{u}) (I : Type w) (U : I → Opens X)
    (hcover : ⨆ i, U i = ⊤)
    (Fi : ∀ i : I, SheafOfModules.{max u v} ((moduleRings X).over (U i)))
    (φij : ∀ i j : I,
      (SheafOfModules.overMap (moduleRings X)
        (homOfLE inf_le_left : U i ⊓ U j ⟶ U i)).obj (Fi i) ≅
      (SheafOfModules.overMap (moduleRings X)
        (homOfLE inf_le_right : U i ⊓ U j ⟶ U j)).obj (Fi j))
    : ∃ (H : SheafOfModules.{max u v} (moduleRings X))
      (π : ∀ i : I, H.over (U i) ⟶ Fi i),
      ∀ V : Opens X,
        (∀ s : H.val.obj (op V),
          OpenModuleFamilyCoherent X I U Fi φij V
            (openModuleFamilyEval X I U Fi H π V s)) ∧
        Function.Injective (openModuleFamilyEval X I U Fi H π V) ∧
        (∀ a : OpenModuleFamily X I U Fi V,
          OpenModuleFamilyCoherent X I U Fi φij V a →
            ∃ s : H.val.obj (op V), openModuleFamilyEval X I U Fi H π V s = a)  := by
  have hs (V : Opens X) :
      Small.{max u v} (coherentOpenModuleSubmodule X I U Fi φij V) :=
    coherent_open_module_small X I U Fi φij hcover V
  let H : SheafOfModules.{max u v} (moduleRings X) :=
    ⟨smallCoherentOpenModulePresheaf X I U Fi φij,
      small_coherent_open_module_isSheaf X I U Fi φij⟩
  let π : ∀ i : I, H.over (U i) ⟶ Fi i := fun i =>
    ⟨{ app := fun W => ModuleCat.ofHom
          { toFun := fun s =>
              (coherentOpenModuleShrinkEquiv X I U Fi φij W.unop.left s).1
                i W.unop.left (leOfHom W.unop.hom) le_rfl
            map_add' := by
              intro a b
              change ((coherentOpenModuleShrinkEquiv X I U Fi φij W.unop.left)
                (a + b)).1 i W.unop.left _ _ = _
              rw [map_add]
              rfl
            map_smul' := by
              intro r a
              change ((coherentOpenModuleShrinkEquiv X I U Fi φij W.unop.left)
                (r • a)).1 i W.unop.left _ _ = _
              rw [map_smul]
              change (moduleRings X).obj.map (𝟙 (op W.unop.left)) r •
                (coherentOpenModuleShrinkEquiv X I U Fi φij W.unop.left a).1
                  i W.unop.left (leOfHom W.unop.hom) le_rfl = _
              erw [(moduleRings X).obj.map_id]
              rfl }
       naturality := by
         intro W Z f
         ext a
         change ((coherentOpenModuleShrinkEquiv X I U Fi φij Z.unop.left)
           ((smallCoherentOpenModulePresheaf X I U Fi φij).map f.unop.left.op a)).1
             i Z.unop.left (leOfHom Z.unop.hom) le_rfl =
           (Fi i).val.map f
             ((coherentOpenModuleShrinkEquiv X I U Fi φij W.unop.left a).1
               i W.unop.left (leOfHom W.unop.hom) le_rfl)
         have hh := smallCoherentOpenModulePresheaf_map_equiv X I U Fi φij
           f.unop.left.op a
         refine (congrArg
           (fun b : coherentOpenModuleSubmodule X I U Fi φij Z.unop.left =>
             b.1 i Z.unop.left (leOfHom Z.unop.hom) le_rfl) hh).trans ?_
         exact ((coherentOpenModuleShrinkEquiv X I U Fi φij W.unop.left a).2.1
           i W.unop.left Z.unop.left (leOfHom W.unop.hom) le_rfl
           (leOfHom f.unop.left)).symm }⟩
  have heval (V : Opens X) (s : H.val.obj (op V)) :
      openModuleFamilyEval X I U Fi H π V s =
        (coherentOpenModuleShrinkEquiv X I U Fi φij V s).1 := by
    funext i W hi hWV
    change ((coherentOpenModuleShrinkEquiv X I U Fi φij W)
      ((smallCoherentOpenModulePresheaf X I U Fi φij).map (homOfLE hWV).op s)).1
        i W hi le_rfl = _
    erw [smallCoherentOpenModulePresheaf_map_equiv]
    rfl
  refine ⟨H, π, fun V => ⟨?_, ?_, ?_⟩⟩
  · intro s
    rw [heval]
    exact (coherentOpenModuleShrinkEquiv X I U Fi φij V s).2
  · intro s t h
    apply (coherentOpenModuleShrinkEquiv X I U Fi φij V).injective
    apply Subtype.ext
    simpa only [heval] using h
  · intro a ha
    refine ⟨(coherentOpenModuleShrinkEquiv X I U Fi φij V).symm ⟨a, ha⟩, ?_⟩
    rw [heval, LinearEquiv.apply_symm_apply]

end AlgebraicGeometry
