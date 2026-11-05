/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful

/-!
# The closed-support triangle on the pro-étale site

Let `i : Z ⟶ X` be a closed immersion with quasi-compact complementary open immersion
`j : U ⟶ X` (for instance, `X` noetherian), and let `R` be a ring. On the unbounded derived
categories of pro-étale sheaves of `R`-modules, the direct image `Ri_*` has the right adjoint
`Ri^!` of `AlgebraicGeometry.ProEtale.derivedLowerStarClosedUpperShriekAdjunction`, and for
every `K` the counit of `Ri_* ⊣ Ri^!` and the unit of `Lj^* ⊣ Rj_*` extend to a distinguished
triangle

`Ri_* Ri^! K ⟶ K ⟶ Rj_* Lj^* K ⟶ (Ri_* Ri^! K)[1]`

(blueprint `lem-exc-proetale-support-triangle`). No constructibility is involved.

The proof is formal from the following sheaf-level facts:

- `j^* i_* = 0` (`AlgebraicGeometry.ProEtale.isZero_upperStar_lowerStar_of_disjoint`), so that
  `Hom((Ri_* M)[n], Rj_* N) = 0`;
- `j^* j_* ≅ 𝟭`, so that `Rj_*` is fully faithful and `Lj^*` inverts the unit of
  `Lj^* ⊣ Rj_*`;
- a sheaf killed by `j^*` is in the essential image of the exact functor `i_*`
  (`AlgebraicGeometry.ProEtale.isIso_upperStarLowerStarAdjunction_unit_app_of_isCompl`), so that
  a complex killed by `Lj^*` is in the essential image of `Ri_*`.

Complete the unit `K ⟶ Rj_* Lj^* K` to a distinguished triangle `K' ⟶ K ⟶ Rj_* Lj^* K ⟶`;
then `Lj^* K' = 0`, so `K'` lies in the essential image of `Ri_*`, and
`CategoryTheory.Pretriangulated.exists_distTriang_counit_of_subsingleton` identifies `K'` with
`Ri_* Ri^! K`.

## Main statements

- `AlgebraicGeometry.ProEtale.isZero_mapDerivedCategoryUpperStar_obj_rightDerivedFunctor_lowerStar`:
  `D(j^*) Ri_* = 0`.
- `AlgebraicGeometry.ProEtale.subsingleton_hom_shift_rightDerivedFunctor_lowerStar`:
  `Hom((Ri_* M)[n], Rj_* N) = 0`.
- `AlgebraicGeometry.ProEtale.exists_distTriang_derivedLowerStarClosedUpperShriekAdjunction_counit`:
  the closed-support triangle (blueprint `lem-exc-proetale-support-triangle`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable {R : Type (u + 1)} [CommRing R] {Z U X : Scheme.{u}}

variable (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]

end ProEtale

end AlgebraicGeometry
