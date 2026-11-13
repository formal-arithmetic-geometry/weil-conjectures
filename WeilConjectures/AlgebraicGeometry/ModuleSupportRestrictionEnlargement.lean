/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Restricting a supported section and enlarging its support

## References

* Stacks Project, Modules, proof of Tag 01BB, and Tag 01AH (2).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

set_option maxHeartbeats 600000 in
-- Comparing iterated and direct restriction unfolds module pushforward functors.
set_option backward.isDefEq.respectTransparency false in
/-- An existing one-section factorization stays a factorization after further
restriction and inclusion into a larger finite support. -/
theorem enlarge_restricted_unit_support
    (X : Scheme.{u}) (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (V U W Z : X.Opens) (hUV : U ≤ V) (hWU : W ≤ U) (hZU : Z ≤ U) (hZW : Z ≤ W)
    (I : Type u) (S T : Finset I) (hST : S ⊆ T)
    (b : unit (R.over U) ⟶ (overMap R (homOfLE hUV)).obj (free (R := R.over V) I))
    (a : unit (R.over W) ⟶
      (overMap R (homOfLE (hWU.trans hUV))).obj (free (R := R.over V) S))
    (ha : a ≫ (overMap R (homOfLE (hWU.trans hUV))).map
        (freeMap (R := R.over V) ((↑) : S → I)) =
      (overMap R (homOfLE hWU)).map b) :
    (((overMap R (homOfLE hZW)).map a ≫
        (overMap R (homOfLE (hZU.trans hUV))).map
          (freeMap (R := R.over V) (fun j : S ↦ (⟨j.val, hST j.property⟩ : T)))) ≫
        (overMap R (homOfLE (hZU.trans hUV))).map
          (freeMap (R := R.over V) ((↑) : T → I)) :
      (overMap R (homOfLE hZU)).obj (unit (R.over U)) ⟶
        (overMap R (homOfLE (hZU.trans hUV))).obj (free (R := R.over V) I)) =
      (overMap R (homOfLE hZU)).map b := by
  have hfree :
      freeMap (R := R.over V) (fun j : S ↦ (⟨j.val, hST j.property⟩ : T)) ≫
        freeMap (R := R.over V) ((↑) : T → I) =
      freeMap (R := R.over V) ((↑) : S → I) := by
    apply CategoryTheory.Limits.Cofan.IsColimit.hom_ext
      (isColimitFreeCofan (R := R.over V) S)
    intro i
    simp only [freeCofan_inj, ιFree_freeMap_assoc, ιFree_freeMap]
  let F := overMap R (homOfLE hZU)
  let G := overMap R (homOfLE (hZU.trans hUV))
  let aZ : F.obj (unit (R.over U)) ⟶ G.obj (free (R := R.over V) S) :=
    (overMap R (homOfLE hZW)).map a
  change (aZ ≫ G.map _) ≫ G.map _ = F.map b
  rw [Category.assoc, ← G.map_comp, hfree]
  have h := congrArg ((overMap R (homOfLE hZW)).map) ha
  rw [Functor.map_comp] at h
  exact h

end AlgebraicGeometry.Scheme.Modules
