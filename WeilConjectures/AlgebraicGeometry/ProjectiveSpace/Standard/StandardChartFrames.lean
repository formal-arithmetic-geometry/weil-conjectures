/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineDifferentials
import WeilConjectures.AlgebraicGeometry.Modules.InvertibleSections
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PicardGroup

/-! # Frames for invertible modules on the standard projective-line charts

Source: Stacks Project, Tag 0BXJ, proof of divisors-lemma-Pic-projective-space-UFD.
(blueprint: lem-sfb-projective-line-standard-chart-frames)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveLine

open ProjectiveSpace

/-- An invertible module has a free generator on each of the two standard charts.

Source: Stacks Project, Tag 0BXJ, proof of divisors-lemma-Pic-projective-space-UFD,
first paragraph, specialized to the projective line over a field.
(blueprint: lem-sfb-projective-line-standard-chart-frames)

Proof: each standard chart is affine and its function ring is k[t], by
polyEquivChart (using the other coordinate for each chart). Transport the domain
and principal-ideal-ring structures along this ring isomorphism. The module of
sections of L over the chart is invertible by invertible_sections_of_isAffineOpen.
An invertible module over this PID has trivial class in CommRing.Pic, so
CommRing.Pic.mk_eq_one_iff supplies a linear isomorphism with the chart ring.
The inverse image of 1 is a basis vector of the section module. Finally,
isFreeGenerator_of_bijective_smul extends this basis to every subopen of the
affine chart, giving the asserted free generator. -/
theorem exists_standardChart_frames (k : Type u) [Field k]
    (L : (ProjectiveLine (Spec (.of k))).Modules) [Scheme.Modules.IsInvertible L]
    (i : ULift.{u} (Fin 2)) :
    ∃ g : Γ(L, standardOpen _ (Spec (.of k)) i), Scheme.Modules.IsFreeGenerator g := by
  let U := chart k {i}
  let r := polyEquivChart k (ne_other i)
  have : IsDomain Γ(ProjectiveLine (Spec (.of k)), U) := r.symm.toMulEquiv.isDomain _
  have : IsPrincipalIdealRing Γ(ProjectiveLine (Spec (.of k)), U) :=
    IsPrincipalIdealRing.of_surjective r r.surjective
  have hU : IsAffineOpen U := isAffineOpen_chart k (Set.singleton_nonempty i)
  have := Scheme.Modules.invertible_sections_of_isAffineOpen L hU
  obtain ⟨f⟩ := CommRing.Pic.mk_eq_one_iff.mp
    (Subsingleton.elim
      (CommRing.Pic.mk Γ(ProjectiveLine (Spec (.of k)), U) Γ(L, U)) 1)
  have hg : Scheme.Modules.IsFreeGenerator (f.symm 1) :=
    Scheme.Modules.isFreeGenerator_of_bijective_smul L hU (by
      convert f.symm.bijective using 1
      ext a
      simp only [← map_smul, smul_eq_mul, mul_one])
  exact ⟨_, hg.map (chart_singleton k i).ge⟩

end AlgebraicGeometry.ProjectiveLine
