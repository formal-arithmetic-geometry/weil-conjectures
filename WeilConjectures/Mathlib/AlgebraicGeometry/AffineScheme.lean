/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# `Spec` of a restriction map and the canonical isomorphisms of affine opens

We record that `Spec` of a restriction map between affine opens intertwines the canonical
isomorphisms `Spec Γ(X, U) ≅ U` with the inclusion of opens, and that the algebra map
realizing `Γ(X, X.basicOpen f)` as a localization is the restriction map of the structure
sheaf. On an affine scheme, the stalk at a point is the localization of the global sections at
the sections invertible at that point (`Scheme.exists_mul_Γgerm_eq`,
`Scheme.exists_mul_eq_zero_of_Γgerm_eq_zero`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The `Spec` of a restriction map intertwines the canonical isomorphisms
`Spec Γ(X, U) ≅ U` with the inclusion of opens. -/
lemma specMap_res_isoSpec_inv {U V : X.affineOpens} (hUV : U ≤ V) :
    Spec.map (X.presheaf.map (homOfLE (X := X.Opens) hUV).op) ≫ V.2.isoSpec.inv =
      U.2.isoSpec.inv ≫ X.homOfLE hUV := by
  rw [← cancel_mono V.1.ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι,
    Scheme.homOfLE_ι, IsAffineOpen.isoSpec_inv_ι,
    V.2.map_fromSpec U.2 (homOfLE (X := X.Opens) hUV).op]

/-- The algebra map exhibiting the sections over a basic open as a localization is the
restriction map of the structure sheaf. -/
lemma algebraMap_basicOpen_eq {U : X.Opens} (f : Γ(X, U)) :
    algebraMap Γ(X, U) Γ(X, X.basicOpen f) =
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom :=
  rfl

section Stalk

variable (Z : Scheme.{u}) [IsAffine Z] (x : Z)

/-- On an affine scheme, every element of the stalk at `x` is a fraction of global sections whose
denominator is invertible at `x`. -/
lemma Scheme.exists_mul_Γgerm_eq (z : Z.presheaf.stalk x) :
    ∃ a s : Γ(Z, ⊤), IsUnit (Z.presheaf.Γgerm x s) ∧
      z * Z.presheaf.Γgerm x s = Z.presheaf.Γgerm x a := by
  let := Z.presheaf.algebra_section_stalk (U := ⊤) ⟨x, trivial⟩
  have := (isAffineOpen_top Z).isLocalization_stalk ⟨x, trivial⟩
  obtain ⟨⟨a, s⟩, e⟩ :=
    IsLocalization.surj ((isAffineOpen_top Z).primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl z
  exact ⟨a, s, (IsLocalization.AtPrime.isUnit_to_map_iff _ _ _).2 s.2, e⟩

/-- On an affine scheme, a global section vanishing in the stalk at `x` is killed by a global
section invertible at `x`. -/
lemma Scheme.exists_mul_eq_zero_of_Γgerm_eq_zero (a : Γ(Z, ⊤))
    (ha : Z.presheaf.Γgerm x a = 0) :
    ∃ s : Γ(Z, ⊤), IsUnit (Z.presheaf.Γgerm x s) ∧ s * a = 0 := by
  let := Z.presheaf.algebra_section_stalk (U := ⊤) ⟨x, trivial⟩
  have := (isAffineOpen_top Z).isLocalization_stalk ⟨x, trivial⟩
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff
    ((isAffineOpen_top Z).primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl (Z.presheaf.stalk x) a).1 ha
  exact ⟨s, (IsLocalization.AtPrime.isUnit_to_map_iff _ _ _).2 s.2, hs⟩

end Stalk

end AlgebraicGeometry
