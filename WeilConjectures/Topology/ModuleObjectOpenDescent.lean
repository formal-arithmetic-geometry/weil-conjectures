/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import WeilConjectures.Topology.ModuleObjectOpenDescentAux

/-! # Effectivity of open-cover descent for sheaves of modules

Local sheaves of modules on an open cover with overlap isomorphisms satisfying the cocycle
condition descend to a global sheaf of modules.

## Implementation details

The cocycle condition forces the diagonal overlap maps to be identities, which reduces the
statement to `module_object_open_descent_aux`. There, after passing to a subcover indexed by the
points of `X` (to stay in universe `max u v`), the global module has as sections over `W` the
compatible families of sections of the local modules on `W ∩ U i`.

## References

* [Stacks Project, Tags 00AL and 00AM](https://stacks.math.columbia.edu/tag/00AL)
-/

@[expose] public section

universe u v w

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- The cocycle condition forces each diagonal overlap map `φij i i` to be the identity. -/
theorem diagonal_transition_identity
    (X : RingedSpace.{u}) (I : Type w) (U : I → Opens X)
    (Fi : ∀ i : I, SheafOfModules.{max u v} ((moduleRings X).over (U i)))
    (φij : ∀ i j : I, (SheafOfModules.overMap (moduleRings X)
      (homOfLE inf_le_left : U i ⊓ U j ⟶ U i)).obj (Fi i) ≅
      (SheafOfModules.overMap (moduleRings X)
      (homOfLE inf_le_right : U i ⊓ U j ⟶ U j)).obj (Fi j))
    (hcoc : ∀ (i j k : I) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j)
      (hk : W ≤ U k), (φij i k).hom.val.app (op (Over.mk
      (homOfLE (le_inf hi hk)))) = (φij i j).hom.val.app (op (Over.mk
      (homOfLE (le_inf hi hj)))) ≫ (φij j k).hom.val.app (op (Over.mk
      (homOfLE (le_inf hj hk))))) :
    ∀ (i : I) (W : Opens X) (hi : W ≤ U i),
      (φij i i).hom.val.app (op (Over.mk (homOfLE (le_inf hi hi)))) = 𝟙 _ := by
  intro i W hi
  let f := (φij i i).hom.val.app (op (Over.mk (homOfLE (le_inf hi hi))))
  let g := (φij i i).inv.val.app (op (Over.mk (homOfLE (le_inf hi hi))))
  have hgf : g ≫ f = 𝟙 _ := by
    have hh := congrArg (fun q => q.val.app (op (Over.mk (homOfLE (le_inf hi hi)))))
      (φij i i).inv_hom_id
    exact hh
  have hff : f = f ≫ f := hcoc i i i W hi hi hi
  have h := congrArg (fun q => g ≫ q) hff
  rw [← Category.assoc, hgf, Category.id_comp] at h
  exact h.symm

/-- Local module sheaves on an open cover with overlap isomorphisms satisfying the cocycle
condition descend to a global module sheaf, compatibly with the overlap isomorphisms. -/
theorem module_object_open_descent
    (X : RingedSpace.{u}) (I : Type w) (U : I → Opens X)
    (hcover : ⨆ i, U i = ⊤) :
    ∀ (Fi : ∀ i : I, SheafOfModules.{max u v} ((moduleRings X).over (U i)))
      (φij : ∀ i j : I,
        (SheafOfModules.overMap (moduleRings X) (homOfLE inf_le_left : U i ⊓ U j ⟶ U i)).obj
            (Fi i) ≅
          (SheafOfModules.overMap (moduleRings X)
            (homOfLE inf_le_right : U i ⊓ U j ⟶ U j)).obj (Fi j)),
      (∀ (i j k : I) (W : Opens X)
        (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k),
        (φij i k).hom.val.app (op (Over.mk (homOfLE (le_inf hi hk)))) =
          (φij i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) ≫
            (φij j k).hom.val.app (op (Over.mk (homOfLE (le_inf hj hk))))) →
      ∃ (H : SheafOfModules.{max u v} (moduleRings X))
        (φi : ∀ i : I, H.over (U i) ≅ Fi i),
        ∀ (i j : I) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
          (φi i).hom.val.app (op (Over.mk (homOfLE hi))) ≫
            (φij i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) =
              (φi j).hom.val.app (op (Over.mk (homOfLE hj))) := by
  intro Fi φij hcoc
  apply module_object_open_descent_aux X I U hcover Fi φij
    (diagonal_transition_identity X I U Fi φij hcoc) hcoc

end AlgebraicGeometry
