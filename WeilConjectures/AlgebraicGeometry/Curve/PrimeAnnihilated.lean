/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenTmp

/-!
# Étale sheaves annihilated by a prime

Let `r` be a prime and `F` an étale sheaf of `Λ`-modules on a scheme `X` with `r • 𝟙 F = 0`.
We record how the torsion conditions of the eight curve assertions
(`AlgebraicGeometry.IsCurve.Assertions`) specialise to `F`.

## Main statements

- `AlgebraicGeometry.Scheme.prime_annihilated_invertible_cases`: if `r` is a unit on
  `Spec k`, then `F` has torsion of invertible order; if not, torsion of invertible order
  forces `F = 0`.
- `AlgebraicGeometry.Scheme.prime_annihilated_primary_cases`: `F` is `r`-primary, and `F` is
  zero if it is `p`-primary for a prime `p ≠ r`.
- `AlgebraicGeometry.IsCurve.prime_torsion_nonunit_cohomology`: if `r` is not a unit on
  `Spec k` and `F` has torsion of invertible order, all cohomology of `F` and of its
  pullbacks vanishes.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Etale

namespace Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- **Invertible-order cases for a prime-annihilated sheaf.** Let `F` be an étale sheaf of
`Λ`-modules with `r • 𝟙 F = 0` for a prime `r`. If `r` is a unit in `Γ(Spec k, ⊤)`, then `F` has
torsion of invertible order relative to `Spec k`; if `r` is not a unit there, torsion of
invertible order forces `F` to be zero.
(blueprint: `lem-pbc-a3-prime-annihilated-invertible-cases`) -/
theorem prime_annihilated_invertible_cases (k : Type u) [Field k]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {r : ℕ} (hr : r.Prime)
    (hF : r • 𝟙 F = 0) :
    (IsUnit (r : Γ(Spec (.of k), ⊤)) → IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F) ∧
      (¬ IsUnit (r : Γ(Spec (.of k), ⊤)) →
        IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F → IsZero F) :=
  ⟨IsTorsionSheafOfInvertibleOrder.of_nsmul_id_eq_zero _ hr.pos hF, fun hu _ ↦ by
    by_contra hz
    exact hu (IsTorsionSheafOfInvertibleOrder.isUnit_of_nsmul_id_eq_zero _ hr hF hz)⟩

/-- **Primary torsion cases for a prime-annihilated sheaf.** Let `F` be an étale sheaf of
`Λ`-modules with `r • 𝟙 F = 0` for a prime `r`. Then `F` is `r`-primary, and if `F` is
`p`-primary for a prime `p ≠ r`, then `F` is zero.
(blueprint: `lem-pbc-a3-prime-annihilated-primary-cases`) -/
theorem prime_annihilated_primary_cases
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {r : ℕ} (hr : r.Prime)
    (hF : r • 𝟙 F = 0) :
    IsPrimaryTorsionSheaf Λ F r ∧
      ∀ p : ℕ, p.Prime → p ≠ r → IsPrimaryTorsionSheaf Λ F p → IsZero F :=
  ⟨IsPrimaryTorsionSheaf.of_nsmul_id_eq_zero hF dvd_rfl, fun p hp hpr hFp ↦ by
    by_contra hz
    exact hpr ((Nat.prime_dvd_prime_iff_eq hr hp).1
      (IsPrimaryTorsionSheaf.dvd_of_nsmul_id_eq_zero hr hF hFp hz)).symm⟩

end Scheme

namespace IsCurve

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **Vanishing with a nonunit prime annihilator.** Let `F` be an étale sheaf of `Λ`-modules
on `X` with `r • 𝟙 F = 0` for a prime `r` which is not a unit in `Γ(Spec k, ⊤)`, and suppose
that `F` has torsion of invertible order relative to `Spec k`. Then for every morphism
`a : Y ⟶ X` and every `q`, both `Hᵠ(X, F)` and `Hᵠ(Y, a^* F)` (of the underlying abelian
sheaves) vanish. (blueprint: `lem-pbc-x2-prime-torsion-nonunit-cohomology`) -/
theorem prime_torsion_nonunit_cohomology (k : Type u) [Field k] {X Y : Scheme.{u}}
    (a : Y ⟶ X) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {r : ℕ}
    (hr : r.Prime) (hF : r • 𝟙 F = 0) (hu : ¬ IsUnit (r : Γ(Spec (.of k), ⊤)))
    [Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F] (q : ℕ) :
    Subsingleton (Sheaf.H
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) ∧
      Subsingleton (Sheaf.H ((a)^*[AddCommGrpCat.{u + 1}].obj
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)) q) := by
  have h₀ : IsZero ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
      F) := Functor.map_isZero _
    ((Scheme.prime_annihilated_invertible_cases k F hr hF).2 hu inferInstance)
  exact ⟨subsingleton_H_of_isZero h₀ q,
    subsingleton_H_of_isZero (Functor.map_isZero (a)^*[AddCommGrpCat.{u + 1}] h₀) q⟩

end IsCurve

end AlgebraicGeometry
