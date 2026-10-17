/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension.StalkFormula
public import WeilConjectures.AlgebraicGeometry.Curve.TorsionCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Sites.SupportDimension

/-!
# Higher direct images of the affine line at a geometric generic point

Let `K` be a field, `B = Spec K[y₁, …, y_c]` and `f : 𝔸¹_B ⟶ B` the projection. At a geometric
point `s` of `B` lying over the generic point (equivalently, whose residue field has
transcendence degree at least `c` over `K`), the stalk of `Rᵠf_* M` vanishes for `q ≥ 2` and
every torsion sheaf `M` (`AlgebraicGeometry.AffineSpace.isZero_upperStar_rightDerived_lowerStar_of_generic`).

Indeed the strict henselization of `B` at `s` is a separably closed field `L`
(`AlgebraicGeometry.Scheme.isField_strictHenselization`), so by the stalk formula it suffices
that `Hᵠ(𝔸¹_L, M|) = 0`, which holds since `𝔸¹_L` is an affine curve over a separably closed
field (`AlgebraicGeometry.IsCurve.hasTorsionCohomologicalDimensionLE_of_isSepClosed`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.AffineSpace

open Scheme Etale

/-- **The geometric generic stalk.** Let `K` be a field, `B = Spec K[y₁, …, y_c]` and
`f : 𝔸¹_B ⟶ B` the projection. If `s` is a geometric point of `B` whose residue field has
transcendence degree at least `c` over `K` (so that `s` lies over the generic point), then for
every torsion abelian étale sheaf `M` on `𝔸¹_B` and `q ≥ 2` the stalk of `Rᵠf_* M` at `s`
vanishes. -/
theorem isZero_upperStar_rightDerived_lowerStar_of_generic {K : Type u} [Field K] {c : ℕ}
    (M : Sheaf 𝔸(PUnit.{u + 1}; Spec (.of (MvPolynomial (Fin c) K))).smallEtaleTopology
      AddCommGrpCat.{u + 1}) (hM : M.IsTorsion) (q : ℕ) (hq : 2 ≤ q)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of (MvPolynomial (Fin c) K)))
    (hs : (c : Cardinal.{u}) ≤ residueFieldTrdeg
      (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin c) K))))
      (s (IsLocalRing.closedPoint Ω))) :
    IsZero ((s)^*[AddCommGrpCat.{u + 1}].obj
      ((((𝔸(PUnit.{u + 1}; Spec (.of (MvPolynomial (Fin c) K))) ↘
        Spec (.of (MvPolynomial (Fin c) K)))_*[AddCommGrpCat.{u + 1}]).rightDerived q).obj M)) :=
  sorry

end AlgebraicGeometry.AffineSpace
