/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.ModuleFiniteFreeLocalLift
import WeilConjectures.AlgebraicGeometry.ModuleFiniteFreeLocalSupport

/-! # Finite support of a generating family near a point

## References

* [Stacks, Tag 01BB](https://stacks.math.columbia.edu/tag/01BB)
* [Stacks, Tag 01B8](https://stacks.math.columbia.edu/tag/01B8)
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

set_option maxHeartbeats 700000 in
-- Comparing iterated slice restrictions requires additional elaboration steps.
set_option backward.isDefEq.respectTransparency false in
/-- Near any point of an open on which a module sheaf is of finite type, finitely many
members of a specified global generating family generate. Compactness is not assumed
(Stacks, Tags 01BB and 01B8). -/
theorem exists_finset_generatingSections_near_point
    (X : Scheme.{u}) (V K : X.Opens) (hKV : K ≤ V)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [(H.over K).IsFiniteType] (σ : (H.over V).GeneratingSections) (x : K) :
    ∃ (U : X.Opens) (hUK : U ≤ K), (x : X) ∈ U ∧ ∃ S : Finset σ.I,
      Epi ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE (hUK.trans hKV))).map
          (SheafOfModules.freeMap (R := (moduleRings X.toRingedSpace).over V)
            ((↑) : S → σ.I) ≫ σ.π)) := by
  obtain ⟨U, hUK, hxU, n, l, hl⟩ := exists_finite_free_local_lift X V K hKV H
    (free (R := (moduleRings X.toRingedSpace).over V) σ.I) σ.π x
  obtain ⟨W, hWU, hxW, S, a, ha⟩ := exists_finite_free_local_support X V U
    (hUK.trans hKV) σ.I n l ⟨x.val, hxU⟩
  refine ⟨W, hWU.trans hUK, hxW, S, ?_⟩
  let F := overMap (moduleRings X.toRingedSpace) (homOfLE hWU)
  have : F.PreservesEpimorphisms := Functor.preservesEpimorphisms_of_adjunction
    (overMapPushforwardAdj (moduleRings X.toRingedSpace) (homOfLE hWU))
  have : Epi (F.map (l ≫ (overMap (moduleRings X.toRingedSpace)
      (homOfLE (hUK.trans hKV))).map σ.π)) := by
    have := hl
    exact F.map_epi _
  have hfac : a ≫ (overMap (moduleRings X.toRingedSpace)
      (homOfLE ((hWU.trans hUK).trans hKV))).map
        (freeMap (R := (moduleRings X.toRingedSpace).over V) ((↑) : S → σ.I) ≫ σ.π) =
      F.map (l ≫ (overMap (moduleRings X.toRingedSpace)
        (homOfLE (hUK.trans hKV))).map σ.π) := by
    rw [Functor.map_comp, ← Category.assoc, ha, Functor.map_comp]
    rfl
  exact epi_of_epi_fac hfac

end AlgebraicGeometry.Scheme.Modules
