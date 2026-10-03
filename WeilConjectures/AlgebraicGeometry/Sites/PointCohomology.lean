/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Étale cohomology of the constant sheaf `ℤ` on the spectrum of a field

The étale cohomology of the spectrum of a field `K` is the Galois cohomology of
`Gal(Kˢᵉᵖ/K)`. For the constant sheaf `ℤ` this gives:

- in degree `1`, `H¹(Spec K_ét, ℤ) = Hom_cont(Gal(Kˢᵉᵖ/K), ℤ) = 0`, since a continuous
  homomorphism from a profinite group to the discrete torsion-free group `ℤ` has finite, hence
  trivial, image;
- in every positive degree, `Hⁿ(Spec k_ét, ℤ) = 0` for `k` separably closed, since then the
  Galois group is trivial.

## Main statements

- `AlgebraicGeometry.Scheme.subsingleton_H_constantSheaf_of_isSepClosed`:
  `H^q(Spec k_ét, ℤ) = 0` for `q ≥ 1` and `k` separably closed.
- `AlgebraicGeometry.Scheme.subsingleton_H_one_constantSheaf_of_isField`:
  `H¹(Spec K_ét, ℤ) = 0` for every field `K`. The proof is `sorry`.

## Blueprint references

The labels quoted below are labels of the *sketch* blueprint, which lives in the separate
repository `formal-arithmetic-geometry/weil-conjectures-blueprint`, not of `blueprint/src` in
this repository.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- **Cohomology of `ℤ` on a geometric point.** For a separably closed field `k` (in
particular an algebraically closed one), `H^q(Spec k_ét, ℤ) = 0` for all `q ≥ 1`.
(blueprint: `lem-sc-point-z-cohomology`) -/
theorem subsingleton_H_constantSheaf_of_isSepClosed (k : Type u) [Field k] [IsSepClosed k]
    (q : ℕ) :
    Subsingleton (Sheaf.H ((constantSheaf (Spec (.of k)).smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))) (q + 1)) :=
  sorry

/-- **`H¹` of `ℤ` on the spectrum of a field vanishes.** For every field `K`,
`H¹(Spec K_ét, ℤ) = Hom_cont(Gal(Kˢᵉᵖ/K), ℤ) = 0`: étale cohomology of `Spec K` is Galois
cohomology, and a continuous homomorphism from the profinite group `Gal(Kˢᵉᵖ/K)` to the
discrete group `ℤ` has finite image, hence is trivial. The proof is `sorry`; it needs the
comparison of étale cohomology of a field with Galois cohomology. -/
theorem subsingleton_H_one_constantSheaf_of_isField (K : CommRingCat.{u}) (hK : IsField K) :
    Subsingleton (Sheaf.H ((constantSheaf (Spec K).smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))) 1) :=
  sorry

end AlgebraicGeometry.Scheme
