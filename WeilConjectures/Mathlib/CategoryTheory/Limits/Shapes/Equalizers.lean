/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Comparison maps between colimit coforks

## Main statements

- `CategoryTheory.Limits.Cofork.IsColimit.isIso_of_π_comp_eq`: a map between the points of two
  colimit coforks of the same pair of morphisms, compatible with the projections, is an
  isomorphism.
- `CategoryTheory.Limits.CokernelCofork.isColimitOfEq`: transport of a colimit cokernel cofork
  along an equality of morphisms.
-/

@[expose] public section

namespace CategoryTheory.Limits

/-- A map `φ : c.pt ⟶ c'.pt` between the points of two colimit coforks of the same pair of
morphisms with `c.π ≫ φ = c'.π` is an isomorphism: it is the comparison isomorphism of the two
colimits. -/
lemma Cofork.IsColimit.isIso_of_π_comp_eq {C : Type*} [Category* C] {X Y : C} {f g : X ⟶ Y}
    {c c' : Cofork f g} (hc : IsColimit c) (hc' : IsColimit c') (φ : c.pt ⟶ c'.pt)
    (w : c.π ≫ φ = c'.π) : IsIso φ := by
  obtain rfl : φ = (hc.coconePointUniqueUpToIso hc').hom := Cofork.IsColimit.hom_ext hc (by
    rw [w]
    exact (hc.comp_coconePointUniqueUpToIso_hom hc' WalkingParallelPair.one).symm)
  infer_instance

/-- A colimit cokernel cofork of `f` is a colimit cokernel cofork of any `f'` equal to `f`. -/
def CokernelCofork.isColimitOfEq {C : Type*} [Category* C] [HasZeroMorphisms C] {X Y Q : C}
    {f f' : X ⟶ Y} (hf : f = f') {p : Y ⟶ Q} (hp : f ≫ p = 0) (hp' : f' ≫ p = 0)
    (h : IsColimit (CokernelCofork.ofπ p hp)) : IsColimit (CokernelCofork.ofπ p hp') := by
  subst hf
  exact h

end CategoryTheory.Limits
