/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveLineProjChartIsomorphism
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

import Sheaf.AlgebraicGeometry.ProjectiveSpace.ProjectiveLineTwistData
import Sheaf.AlgebraicGeometry.ProjShiftedFreeTwist
import Sheaf.AlgebraicGeometry.ProjectiveLineTwistExists

/-!
# Transport of a polynomial Proj twist to the projective line

Source: Stacks Project, Constructions, Definitions 01M6, 01MN and Lemma 01M7;
Section 01MM, chart trivializations; blueprint lem-sc-p1-graded-resolution.
(blueprint: lem-sc-p1-proj-twist-inverse-transport).
-/

@[expose] public section

universe u

open CategoryTheory MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Any chart-compatible comparison transports the Proj twist to the projective-space twist.
Source: Stacks Project, Constructions, Definitions 01M6, 01MN and Lemma 01M7;
blueprint lem-sc-p1-graded-resolution, shifted-free clause.
(blueprint: lem-sc-p1-proj-twist-inverse-transport).

Proof: On D(x_i), the degree-d fractions form a rank-one module with generator x_i^d,
interpreted as a fraction when d is negative. On the overlap their relation is
x_0^d=t^(-d)*x_1^d. The chart equations of C identify these trivializations with the
standard projective-line charts, and their scalar actions with the chart rings.
Transporting along C inverse therefore gives the rank-one chart gluing with that
transition. The projective-space twist has the same trivializations and transition:
its definition is the base change of the integral Proj twist, and degree-d fractions
commute with this base change: on the integral chart the module is free on x_i^d,
so extension of scalars carries its generator to x_i^d over k; its overlap coefficient
(x_i/x_j)^d maps to the identical ratio over k. Map each transported generator to the corresponding
projective-space generator. The transition equation makes the local maps compatible,
so they glue. Glue their inverses as well; the composites fix the chart generators
and hence are identities. This covers every integer d, including zero. -/
theorem proj_twist_inverse_transport (k : Type u) [Field k]
    (C : ProjectiveLine.ProjChartIsomorphism k) (d : ℤ) :
    Nonempty ((Scheme.Modules.pullback C.iso.inv).obj
      (twist (homogeneousSubmodule (Fin 2) k) d) ≅
        ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d) := by
  classical
  let L := ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d
  obtain ⟨T⟩ := ProjectiveLine.nonempty_twistData_projectiveSpace k d
  obtain ⟨C', ⟨L', ⟨T'⟩, ⟨e'⟩⟩, _⟩ := proj_shifted_free_is_twist k d
  have hcov : (⨆ i : ULift.{u} (Fin 2),
      basicOpen (homogeneousSubmodule (Fin 2) k) (X i.down)) = ⊤ := by
    have h := iSup_basicOpen_eq_top' (homogeneousSubmodule (Fin 2) k)
      X (fun i ↦ ⟨1, isHomogeneous_X k i⟩) (adjoin_range_X_eq_top (Fin 2) k)
    refine top_le_iff.mp fun x hx ↦ ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (h.ge hx)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩
  have hC : C'.iso.hom = C.iso.hom := by
    apply (linearCover (homogeneousSubmodule (Fin 2) k)
      (fun j : ULift.{u} (Fin 2) ↦ X j.down)
      (fun j ↦ X_mem_homogeneousSubmodule_one k j.down) hcov).hom_ext
    intro i
    exact (C'.chart_eq i).trans (C.chart_eq i).symm
  obtain ⟨L₀, T₀, _, huniq⟩ := ProjectiveLine.exists_twistData_unique_iso k d
  obtain ⟨e₀, _, _⟩ := huniq L' T'
  obtain ⟨e₁, _, _⟩ := huniq L T
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction C'.iso.hom
  let a := adj.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction C'.iso.hom)
  let e := e' ≪≫ a.app L' ≪≫
    (Scheme.Modules.pullback C'.iso.hom).mapIso (e₀.symm ≪≫ e₁) ≪≫
    (Scheme.Modules.pullbackCongr hC).app L
  exact ⟨(Scheme.Modules.pullback C.iso.inv).mapIso e ≪≫
    (Scheme.Modules.pullbackComp C.iso.inv C.iso.hom).app L ≪≫
    (Scheme.Modules.pullbackCongr C.iso.inv_hom_id).app L ≪≫
    (Scheme.Modules.pullbackId _).app L⟩

end AlgebraicGeometry.Proj
