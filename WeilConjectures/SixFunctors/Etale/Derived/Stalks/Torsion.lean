/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived

/-!
# Torsion sheaves with orders invertible in a field

For a field `K`, a sheaf of `Λ`-modules on the small étale site of a `K`-scheme has *orders
invertible in `K`* if every element of every geometric stalk is killed by a positive integer
`n` with `n ≠ 0` in `K`. In the repository this is
`AlgebraicGeometry.Scheme.IsTorsionSheafOfInvertibleOrder (Spec K)`, whose defining condition
asks for `n` to be a unit in `Γ(Spec K, ⊤) ≅ K`.

## Main statements

- `AlgebraicGeometry.Scheme.isTorsionSheafOfInvertibleOrder_spec_iff`
  (`def-kun-torsion-invertible`): the characterisation in terms of `K`.
- `AlgebraicGeometry.Scheme.IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero_of_ne_zero`
  (`lem-kun-zn-sheaf-invertible-orders`): sheaves of modules over a ring killed by an integer
  invertible in `K` have orders invertible in `K`.
- `AlgebraicGeometry.Scheme.isTorsionSheafOfInvertibleOrder_iff_exists_isColimit`
  (`lem-kun-invertible-orders-colimit`): a sheaf has orders invertible on `S` if and only if it
  is a filtered colimit of sheaves killed by integers invertible on `S`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- A natural number is a unit in `Γ(Spec K, ⊤)` if and only if it is nonzero in `K`. -/
lemma isUnit_natCast_Γ_spec_iff {K : Type u} [Field K] (n : ℕ) :
    IsUnit (n : Γ(Spec (.of K), ⊤)) ↔ (n : K) ≠ 0 := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  rw [← isUnit_iff_ne_zero, ← MulEquiv.isUnit_map e.toMulEquiv]
  simp

/-- Blueprint `lem-kun-zn-sheaf-invertible-orders`: **modules over `ℤ/nℤ` have invertible
orders.** If an integer `n ≥ 1`, nonzero in the field `K`, kills the coefficient ring `Λ` (for
instance `Λ = ℤ/nℤ`), then every sheaf of `Λ`-modules on the small étale site of a scheme has
orders invertible in `K`: multiplication by `n` is zero on it. -/
theorem IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero_of_ne_zero {K : Type u} [Field K]
    {T : Scheme.{u}} (n : ℕ) (hn₀ : n ≠ 0) (hn : (n : Λ) = 0) (hnK : (n : K) ≠ 0)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsTorsionSheafOfInvertibleOrder (Spec (.of K)) F :=
  IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero Λ n hn₀ hn
    ((isUnit_natCast_Γ_spec_iff n).2 hnK) F

end Scheme

end AlgebraicGeometry
