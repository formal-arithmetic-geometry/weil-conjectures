/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension.StalkVanishing
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity

/-!
# Geometric stalks of higher direct images and the strict localization

Let `h : X ⟶ S` be quasi-compact and quasi-separated, `F` an abelian étale sheaf on `X`, and
`s̄` a geometric point of `S` which factors as `s : Spec Ω ⟶ W` followed by an étale
`ι : W ⟶ S`. If `Hᵠ(X ×_S W_(s), F|) = 0`, where `W_(s)` is the strict localization of `W` at `s`,
then the geometric stalk of `Rᵠh_* F` at `s̄` vanishes
(`AlgebraicGeometry.Etale.isZero_upperStar_rightDerived_lowerStar_of_subsingleton_H`). This is
the vanishing half of the strict-henselization stalk formula (blueprint
`prop-weil-pbc-strict-henselization-stalk-formula`).

`X ×_S W_(s)` is the limit of the `X ×_S V`, `V` running over the affine pointed étale
neighbourhoods of `s` in `W`, so by continuity of étale cohomology
(`AlgebraicGeometry.Etale.cohomologyMap_isColimit_of_isLimit`) every class on some `X ×_S V`
dies on a smaller `X ×_S V'`; and pointed étale neighbourhoods of `s` in `W` refine those of
`s ≫ ι` in `S`. We conclude with
`AlgebraicGeometry.Etale.isZero_upperStar_rightDerived_lowerStar_of_forall_exists`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

/-- **Vanishing of geometric stalks of higher direct images.** Let `h : X ⟶ S` be
quasi-compact and quasi-separated, `F` an abelian étale sheaf on `X`, `ι : W ⟶ S` étale and
`s : Spec Ω ⟶ W` a geometric point. If `Hᵠ(X ×_S W_(s), F|) = 0` for `q > 0`, where `W_(s)` is
the strict localization of `W` at `s`, then the geometric stalk of `Rᵠh_* F` at `s ≫ ι`
vanishes. -/
theorem isZero_upperStar_rightDerived_lowerStar_of_subsingleton_H {X S W : Scheme.{u}}
    (h : X ⟶ S) [QuasiCompact h] [QuasiSeparated h] (ι : W ⟶ S) [Etale ι]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ W) (q : ℕ) (hq : 0 < q)
    (hcoh : Subsingleton (Sheaf.H
      ((pullback.fst h (strictLocalizationToBase s ≫ ι))^*[AddCommGrpCat.{u + 1}].obj F) q)) :
    IsZero ((s ≫ ι)^*[AddCommGrpCat.{u + 1}].obj
      ((((h)_*[AddCommGrpCat.{u + 1}]).rightDerived q).obj F)) :=
  sorry

end AlgebraicGeometry.Etale
