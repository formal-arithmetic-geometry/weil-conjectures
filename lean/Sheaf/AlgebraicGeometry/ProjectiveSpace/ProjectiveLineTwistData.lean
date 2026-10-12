/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits

/-!
# Standard generators for the projective-space twist on the projective line

Source: Stacks Project, Constructions, Tags 01MN and 01M7; Section 01MM.
(blueprint: lem-sc-p1-projective-space-twist-data).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveLine

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem integral_transition (n : Type u) (i j : n) (d : ℤ) :
    let A := MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)
    let U := Proj.basicOpen A (MvPolynomial.X i) ⊓ Proj.basicOpen A (MvPolynomial.X j)
    ∃ c : Γ(Proj A, U)ˣ,
      c.val = (Proj A).presheaf.map (homOfLE inf_le_right).op
        (Proj.awayToSection A (MvPolynomial.X j) (ProjectiveSpace.awayRatio n i j)) ∧
      (Proj.twist A d).presheaf.map (homOfLE inf_le_left).op
          (Proj.twistPowSection d (MvPolynomial.X_mem_homogeneousSubmodule_one _ i)) =
        (c ^ d).val • (Proj.twist A d).presheaf.map (homOfLE inf_le_right).op
          (Proj.twistPowSection d (MvPolynomial.X_mem_homogeneousSubmodule_one _ j)) := by
  classical
  dsimp only
  let A := MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)
  let U := Proj.basicOpen A (MvPolynomial.X i) ⊓ Proj.basicOpen A (MvPolynomial.X j)
  let r : Γ(Proj A, U) := (Proj A).presheaf.map (homOfLE inf_le_right).op
    (Proj.awayToSection A (MvPolynomial.X j) (ProjectiveSpace.awayRatio n i j))
  let s : Γ(Proj A, U) := (Proj A).presheaf.map (homOfLE inf_le_left).op
    (Proj.awayToSection A (MvPolynomial.X i) (ProjectiveSpace.awayRatio n j i))
  have hr (x : U) : (r.1 x).val = Localization.mk (MvPolynomial.X i)
      ⟨MvPolynomial.X j, x.2.2⟩ := by
    change ((Proj.awayToSection A (MvPolynomial.X j)
      (ProjectiveSpace.awayRatio n i j)).1 ⟨x.1, x.2.2⟩).val = _
    erw [ProjectiveSpectrum.Proj.awayToSection_apply]
    rw [ProjectiveSpace.awayRatio, HomogeneousLocalization.Away.val_mk,
      Localization.mk_eq_mk', IsLocalization.map_mk', RingHom.id_apply,
      ← Localization.mk_eq_mk']
    simp
  have hs (x : U) : (s.1 x).val = Localization.mk (MvPolynomial.X j)
      ⟨MvPolynomial.X i, x.2.1⟩ := by
    change ((Proj.awayToSection A (MvPolynomial.X i)
      (ProjectiveSpace.awayRatio n j i)).1 ⟨x.1, x.2.1⟩).val = _
    erw [ProjectiveSpectrum.Proj.awayToSection_apply]
    rw [ProjectiveSpace.awayRatio, HomogeneousLocalization.Away.val_mk,
      Localization.mk_eq_mk', IsLocalization.map_mk', RingHom.id_apply,
      ← Localization.mk_eq_mk']
    simp
  have hrs : r * s = 1 := by
    apply Subtype.ext
    funext x
    apply HomogeneousLocalization.val_injective
    change (r.1 x * s.1 x).val =
      (1 : HomogeneousLocalization A x.1.asHomogeneousIdeal.toIdeal.primeCompl).val
    rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one]
    rw [hr, hs, Localization.mk_mul, ← Localization.mk_one,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]; ring⟩
  let c : Γ(Proj A, U)ˣ := ⟨r, s, hrs, by rw [mul_comm, hrs]⟩
  refine ⟨c, rfl, ?_⟩
  apply Subtype.ext
  funext x
  apply Subtype.ext
  rw [Proj.coe_twist_smul_apply, Proj.twist_presheaf_map_apply,
    Proj.twist_presheaf_map_apply, Proj.val_twistPowSection_apply,
    Proj.val_twistPowSection_apply]
  cases d with
  | ofNat m =>
    change Localization.mk (MvPolynomial.X i ^ (m : ℤ).toNat) _ =
      (r.1 x ^ m).val * Localization.mk (MvPolynomial.X j ^ (m : ℤ).toNat) _
    rw [HomogeneousLocalization.val_pow, hr, Localization.mk_pow, Localization.mk_mul,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul]
    change MvPolynomial.X j ^ m * MvPolynomial.X j ^ (-Int.ofNat m).toNat *
      MvPolynomial.X i ^ m = MvPolynomial.X i ^ (-Int.ofNat m).toNat *
        (MvPolynomial.X i ^ m * MvPolynomial.X j ^ m)
    have h : (-Int.ofNat m).toNat = 0 := Int.toNat_of_nonpos (neg_nonpos.mpr (Int.natCast_nonneg m))
    rw [h, pow_zero, pow_zero, mul_one, one_mul]
    exact mul_comm _ _
  | negSucc m =>
    simp only [Int.negSucc_eq, zpow_neg]
    change Localization.mk (MvPolynomial.X i ^ (-(m + 1 : ℕ) : ℤ).toNat) _ =
      (s.1 x ^ (m + 1)).val *
        Localization.mk (MvPolynomial.X j ^ (-(m + 1 : ℕ) : ℤ).toNat) _
    rw [HomogeneousLocalization.val_pow, hs, Localization.mk_pow, Localization.mk_mul,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul]
    simp only [SubmonoidClass.coe_pow, Int.toNat_neg_natCast, pow_zero, mul_one]
    have h : (- -(↑m + 1 : ℤ)).toNat = m + 1 := by omega
    rw [h]

/-- The integral-model twist on the projective line has the prescribed chart generators.
Source: Stacks Project, Constructions, Tags 01MN, 01M7, Section 01MM;
blueprint lem-sc-p1-graded-resolution, shifted-free clause.
(blueprint: lem-sc-p1-projective-space-twist-data).

Proof: on the integral chart D(T_i), take the Laurent monomial T_i^d, whose inverse
is T_i^(-d). Multiplication by these monomials identifies the degree-d module with
its degree-zero ring on every subopen, for positive, zero and negative d. Pull back
these free generators along the map to the integral model. On the overlap,
T_0^d = (T_0/T_1)^d T_1^d. The pullback on ring sections preserves products, inverses
of units and integer powers, so the coefficient becomes transitionUnit d 0 1.
These generators, their free-generator proofs and this equality give TwistData. -/
theorem nonempty_twistData_projectiveSpace (k : Type u) [Field k] (d : ℤ) :
    Nonempty (TwistData (Spec (.of k)) d
      (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d)) := by
  classical
  let S := Spec (.of k)
  let n := ULift.{u} (Fin 2)
  let A := MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)
  let f := ProjectiveSpace.toProjInt n S
  let g (i : n) := Scheme.Modules.pullbackSection f
    (Proj.twistPowSection d (MvPolynomial.X_mem_homogeneousSubmodule_one _ i))
  have hg (i : n) : Scheme.Modules.IsFreeGenerator (g i) :=
    (Proj.isFreeGenerator_twistPowSection d
      (MvPolynomial.X_mem_homogeneousSubmodule_one _ i)).pullback_unit_app f
  refine ⟨{ g₀ := g ⟨0⟩
            g₁ := g ⟨1⟩
            bijective_smul_g₀ := hg ⟨0⟩
            bijective_smul_g₁ := hg ⟨1⟩
            map_g₀ := ?_ }⟩
  obtain ⟨c, hc, htrans⟩ := integral_transition n ⟨0⟩ ⟨1⟩ d
  let U := Proj.basicOpen A (MvPolynomial.X (⟨0⟩ : n)) ⊓
    Proj.basicOpen A (MvPolynomial.X (⟨1⟩ : n))
  have h := congrArg (Scheme.Modules.pullbackSection f) htrans
  rw [Scheme.Modules.pullbackSection_smul, Scheme.Modules.pullbackSection_map,
    Scheme.Modules.pullbackSection_map] at h
  have hunit : Units.map (f.app U).hom.toMonoidHom c =
      ProjectiveSpace.ratioUnit n S ⟨0⟩ ⟨1⟩ := by
    apply Units.ext
    change f.app U c.val = ProjectiveSpace.ratio n S ⟨0⟩ ⟨1⟩
    rw [hc]
    change f.app U ((Proj A).presheaf.map (homOfLE inf_le_right).op _) = _
    have h := ConcreteCategory.congr_hom (f.naturality
      (homOfLE (inf_le_right : U ≤ Proj.basicOpen A (MvPolynomial.X (⟨1⟩ : n)))).op)
      (Proj.awayToSection A (MvPolynomial.X (⟨1⟩ : n))
        (ProjectiveSpace.awayRatio n ⟨0⟩ ⟨1⟩))
    have hi : ((TopologicalSpace.Opens.map f.base).map
        (homOfLE (inf_le_right : U ≤ Proj.basicOpen A (MvPolynomial.X (⟨1⟩ : n))))) =
        homOfLE (f.preimage_mono inf_le_right) := Subsingleton.elim _ _
    simp only [Quiver.Hom.unop_op] at h
    rw [hi] at h
    simpa only [CommRingCat.comp_apply, ProjectiveSpace.ratio, Scheme.Hom.appLE,
      ProjectiveSpace.standardOpen, Scheme.Hom.preimage_inf,
      Proj.projectiveSpaceOverAffine, f, U, A] using h
  have hcoeff : f.app U (c ^ d).val =
      (ProjectiveSpace.transitionUnit n S d ⟨0⟩ ⟨1⟩).val := by
    change (Units.map (f.app U).hom.toMonoidHom (c ^ d)).val = _
    rw [map_zpow, hunit]
    rfl
  rw [hcoeff] at h
  exact h

end AlgebraicGeometry.ProjectiveLine
