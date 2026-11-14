/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.AlgebraicGeometry.DenseOpenComponentModificationsEmpty
import WeilConjectures.AlgebraicGeometry.DenseOpenComponentModificationsNonempty

/-!
# Dense-open gluing of component modifications

## References

* Stacks Project, Tags 0BAJ and 0A3Q
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The coproduct of modifications of distinct integral components is an isomorphism
on a dense open of the reduced target (Stacks, Tags 0BAJ and 0A3Q). -/
theorem exists_dense_open_isIso_component_modifications
    (X : Scheme.{u}) [IsReduced X]
    (n : ℕ) (C : Fin n → Scheme.{u}) (ι : ∀ i, C i ⟶ X)
    (hC : ∀ i, IsIntegral (C i) ∧ IsClosedImmersion (ι i) ∧
      Set.range (ι i) ∈ irreducibleComponents X)
    (hinj : Function.Injective (fun i => Set.range (ι i)))
    (hcover : ∀ Z ∈ irreducibleComponents X, ∃ i, Set.range (ι i) = Z)
    (Y : Fin n → Scheme.{u}) (ν : ∀ i, Y i ⟶ C i)
    (hν : ∀ i, ∃ U : (C i).Opens, Dense (U : Set (C i)) ∧ IsIso (ν i ∣_ U)) :
    ∃ U : X.Opens, Dense (U : Set X) ∧
      IsIso (CategoryTheory.Limits.Sigma.desc (fun i => ν i ≫ ι i) ∣_ U) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact exists_dense_open_isIso_component_modifications_of_zero X C ι hC hinj hcover Y ν hν
  · exact exists_dense_open_isIso_component_modifications_of_pos X n hn C ι hC hinj hcover Y ν hν

end AlgebraicGeometry
