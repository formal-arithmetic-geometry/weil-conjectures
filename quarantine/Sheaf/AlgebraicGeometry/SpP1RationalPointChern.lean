/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTraceSystem
import Sheaf.AlgebraicGeometry.ProjectiveLineGenusZero
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
import WeilConjectures.AlgebraicGeometry.Curve.RootsOfUnityTop

/-! # The rational-point normalization of the finite projective-line Chern class -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

private theorem p1_twist_degree_one (k : Type u) [Field k] :
    (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) 1).degree k = 1 := by
  have hchi (d : ℕ) :
      (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d).eulerChar k =
        (d + 1 : ℕ) := by
    obtain ⟨e⟩ := ProjectiveLine.nonempty_H_zero_twist_equiv k d
    let b := (ProjectiveSpace.homogeneousSubmoduleBasis (ULift.{u} (Fin 2)) k d).reindex
      (ProjectiveLine.degreeEqEquivFin d)
    have hzero : Scheme.Modules.finrankH k
        (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d) 0 = d + 1 := by
      rw [Scheme.Modules.finrankH, e.finrank_eq, Module.finrank_eq_card_basis b]
      simp
    have := ProjectiveLine.subsingleton_H_one_twist k d (by omega)
    have hone : Scheme.Modules.finrankH k
        (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d) 1 = 0 :=
      Module.finrank_zero_of_subsingleton
    rw [Scheme.Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one, hzero, hone]
    simp
  unfold Scheme.Modules.degree
  rw [Scheme.Modules.eulerChar_congr k
    (ProjectiveSpace.unitIsoTwistZero (ULift.{u} (Fin 2)) (Spec (.of k)))]
  have h1 := hchi 1
  have h0 := hchi 0
  simp only [Nat.cast_one] at h1
  simp only [Nat.cast_zero] at h0
  rw [h1, h0]
  norm_num


/-- A rational point and O(1) have equal scalar Kummer classes.
Source: det-sp-p1-trace, proof paragraph 2.
(blueprint: lem-sp-p1-rational-point-chern)

Proof: a section of the smooth relative curve P1 has invertible ideal. The dual
of this ideal has degree one because its divisor is a rational point. The two
standard charts compute chi(O(d)) = d + 1 for d = 0, 1, hence deg(O(1)) = 1.
The root-sheaf Kummer trace on the smooth proper connected geometric curve is
bijective and takes the boundary of a line bundle to its degree modulo N.
Thus the two root-sheaf boundaries agree. Applying the scalar root map gives
the displayed scalar class equality. The Chern specification identifies its
left side with the chosen normalized Chern representative. -/
theorem spP1RationalPointChern_of_normalized
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (c : SpP1ChernFamily A N hA)
    (b : SpP1TwistedFamily A N hA) (d : SpP1DecompositionFamily A N hA)
    (hnorm : SpP1NormalizedDecompositions A N hN hA c b d) :
    SpP1RationalPointChern A N hA c := by
  intro Ω _ _ hΩ x hx
  have hI := Scheme.Hom.isInvertible_ker_of_smoothOfRelativeDimension_one
    (ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω)) x hx
  refine ⟨hI, heq_of_eq ?_⟩
  rw [(hnorm (Spec (.of Ω)) hΩ).chern]
  unfold Etale.ordinaryFiniteP1KummerClass Etale.supportedKummerChern
  congr 1
  have hgeom := ProjectiveSpace.isConnectedCurve_smooth_proper_genus_zero Ω
  let := hgeom.1
  let := hgeom.2.1
  have : ConnectedSpace (ProjectiveLine (Spec (.of Ω))) :=
    IsConnectedCurve.connectedSpace (ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω))
  have : GeometricallyIntegral (ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω)) :=
    GeometricallyIntegral.of_isSepClosed
  have hNΩ : (N : Ω) ≠ 0 := by
    have hunit := hΩ.map (Scheme.ΓSpecIso (.of Ω)).hom.hom
    simpa only [map_natCast] using hunit.ne_zero
  have : NeZero N := ⟨ne_of_gt hN⟩
  let := hI.isInvertible_dual_toModules
  apply (Scheme.bijective_sheafHTwoTrace (k := Ω)
    (X := ProjectiveLine (Spec (.of Ω))) N hNΩ).1
  change Scheme.sheafHTwoTrace (k := Ω) (X := ProjectiveLine (Spec (.of Ω))) N hNΩ
      (Scheme.picToSheafHTwo N hNΩ (Additive.ofMul (Scheme.Pic.ofIsInvertible
        (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of Ω)) 1)))) =
    Scheme.sheafHTwoTrace (k := Ω) (X := ProjectiveLine (Spec (.of Ω))) N hNΩ
      (Scheme.picToSheafHTwo N hNΩ (Additive.ofMul (Scheme.Pic.ofIsInvertible
        (Scheme.Modules.dual x.ker.toModules))))
  rw [Scheme.sheafHTwoTrace_picToSheafHTwo, Scheme.sheafHTwoTrace_picToSheafHTwo]
  change (((Scheme.picDegreeHom Ω _ (Scheme.Pic.ofIsInvertible
      (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of Ω)) 1))).toAdd : ℤ) : ZMod N) =
    (((Scheme.picDegreeHom Ω _ (Scheme.Pic.ofIsInvertible
      (Scheme.Modules.dual x.ker.toModules))).toAdd : ℤ) : ZMod N)
  rw [Scheme.picDegreeHom_ofIsInvertible, Scheme.picDegreeHom_ofIsInvertible,
    p1_twist_degree_one]
  let x' : (ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω)).fieldPoints Ω :=
    ⟨x, by simpa only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id] using hx⟩
  have hdegree := hI.degree_dual_toModules_eq_one
    ((ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω)).finrankΓ_subschemeι_ker_fieldPoints x')
  rw [hdegree]

end AlgebraicGeometry.ProEtale
