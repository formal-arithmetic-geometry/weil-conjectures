/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective

/-!
# Flatness descends along surjective morphisms

For a surjective morphism of schemes `π : T' ⟶ T`, an étale sheaf `F` of `Λ`-modules on `T` is
flat as soon as its pullback `π^* F` is flat. The stalk of `π^* F` at a geometric point `s` of
`T'` is the stalk of `F` at `s ≫ π`, and since `π` is surjective these geometric points form a
conservative family of points of `T`, at which flatness can be tested.

Source: Stacks Project, Lemma 09YU (3), proof (flatness of the descended terms is detected on
stalks after the faithfully flat base change).

## Main statements

- `AlgebraicGeometry.Etale.flat_of_flat_upperStar_of_surjective`
-/

@[expose] public section

universe u

open CategoryTheory

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable {Λ : Type (u + 1)} [CommRing Λ] {T T' : Scheme.{u}} (π : T' ⟶ T)

/-- **Flatness descends along surjective morphisms.** If `π : T' ⟶ T` is surjective and the
pullback `π^* F` of an étale sheaf of `Λ`-modules `F` on `T` is flat, then `F` is flat: the stalk
of `F` at the geometric point `s ≫ π` is the stalk of `π^* F` at `s`, and these geometric points
form a conservative family of points of `T`.

Source: Stacks Project, Lemma 09YU (3), proof (flatness is checked on stalks). -/
theorem Etale.flat_of_flat_upperStar_of_surjective (hπ : Function.Surjective π.base)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ObjectProperty.flat ((π)^*[ModuleCat.{u + 1} Λ].obj F)) :
    ObjectProperty.flat F := by
  have hP := (Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale_of_iUnion_range_eq_univ
    T (fun t' : T' ↦ T'.algClosurePoint t' ≫ π) (by
      refine Set.eq_univ_of_forall fun t ↦ ?_
      obtain ⟨t', rfl⟩ := hπ t
      obtain ⟨x, hx⟩ : t' ∈ ⋃ s : T', Set.range (T'.algClosurePoint s) := by
        rw [T'.iUnion_range_algClosurePoint]
        trivial
      obtain ⟨s, x, rfl⟩ := Set.mem_iUnion.1 ⟨x, hx⟩
      exact Set.mem_iUnion.2 ⟨s, x, rfl⟩)).jointlyReflectIsomorphisms (ModuleCat.{u + 1} Λ)
  refine GrothendieckTopology.flat_of_forall_flat_sheafFiber_obj hP F ?_
  rintro ⟨-, ⟨t'⟩⟩
  exact ObjectProperty.prop_of_iso _
    ((Etale.upperStarCompUliftSheafFiberIso _ π (T'.algClosurePoint t')).app F)
    ((Etale.flat_iff_forall_flat_sheafFiber_obj _).1 hF (T'.algClosurePoint t'))

end AlgebraicGeometry
