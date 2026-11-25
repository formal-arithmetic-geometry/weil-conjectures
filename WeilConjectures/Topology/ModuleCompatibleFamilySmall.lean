/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.ModuleCompatibleFamilyPresheaf

/-! # A step of the compatible-family sheaf construction

Coherent families of local module sections form a small type, independently of the universe of
the cover's index.

## Implementation details

Choosing for each point `x` an index `i(x)` with `x ∈ U i(x)` embeds coherent families into a
product indexed by the points of `X`; injectivity follows from overlap coherence and separation.

## References

* [Stacks Project, Tag 00AL](https://stacks.math.columbia.edu/tag/00AL)
-/

@[expose] public section

universe u v w

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- Coherent families are small independently of the cover's index universe. -/
theorem coherent_open_module_small
    (X : RingedSpace.{u}) (I : Type w) (U : I → Opens X)
  (Fi : ∀ i : I, SheafOfModules.{max u v} ((moduleRings X).over (U i)))
  (φij : ∀ i j : I,
    (SheafOfModules.overMap (moduleRings X)
      (homOfLE inf_le_left : U i ⊓ U j ⟶ U i)).obj (Fi i) ≅
    (SheafOfModules.overMap (moduleRings X)
      (homOfLE inf_le_right : U i ⊓ U j ⟶ U j)).obj (Fi j))
    (hcover : ⨆ i, U i = ⊤) (V : Opens X) :
    Small.{max u v} (coherentOpenModuleSubmodule X I U Fi φij V)  := by
  classical
  have hp (x : X) : ∃ i : I, x ∈ U i := by
    apply Opens.mem_iSup.mp
    rw [hcover]
    trivial
  choose c hc using hp
  let T := Σ x : X, {W : Opens X // W ≤ U (c x) ∧ W ≤ V}
  let target (t : T) := (Fi (c t.1)).val.obj
    (op (Over.mk (homOfLE t.2.2.1)))
  let encode (a : coherentOpenModuleSubmodule X I U Fi φij V) : ∀ t : T, target t :=
    fun t => a.1 (c t.1) t.2.1 t.2.2.1 t.2.2.2
  apply small_of_injective (f := encode)
  intro a b hab
  apply Subtype.ext
  funext i W hi hWV
  let S : Sieve W :=
    { arrows := fun Z _ => ∃ x : X, Z ≤ U (c x)
      downward_closed := by
        intro Z T f hf g
        obtain ⟨x, hx⟩ := hf
        exact ⟨x, (leOfHom g).trans hx⟩ }
  have hS : S ∈ Opens.grothendieckTopology X W := by
    intro x hx
    exact ⟨W ⊓ U (c x), homOfLE inf_le_left, ⟨x, inf_le_right⟩, hx, hc x⟩
  let O : Over (U i) := Over.mk (homOfLE hi)
  have hSO := (Opens.grothendieckTopology X).overEquiv_symm_mem_over O S hS
  apply (Fi i).isSheaf.isSeparated O ((Sieve.overEquiv O).symm S) hSO
  intro Z f hf
  obtain ⟨x, hx⟩ := hf
  have hZW : Z.left ≤ W := leOfHom f.left
  have hzV : Z.left ≤ V := hZW.trans hWV
  have hzi : Z.left ≤ U i := hZW.trans hi
  change (Fi i).val.map f.op (a.1 i W hi hWV) =
    (Fi i).val.map f.op (b.1 i W hi hWV)
  have ha := a.2.1 i W Z.left hi hWV hZW
  have hb := b.2.1 i W Z.left hi hWV hZW
  change (Fi i).val.map f.op (a.1 i W hi hWV) = a.1 i Z.left hzi hzV at ha
  change (Fi i).val.map f.op (b.1 i W hi hWV) = b.1 i Z.left hzi hzV at hb
  rw [ha, hb, ← a.2.2 (c x) i Z.left hx hzi hzV,
    ← b.2.2 (c x) i Z.left hx hzi hzV]
  congr 1
  exact congrFun hab (⟨x, Z.left, hx, hzV⟩ : T)

end AlgebraicGeometry
