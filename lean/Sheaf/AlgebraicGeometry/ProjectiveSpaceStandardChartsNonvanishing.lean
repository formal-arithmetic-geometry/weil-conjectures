/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
public import Sheaf.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection
import Sheaf.AlgebraicGeometry.SectionNonvanishingZeroLocus

/-!
# Standard charts and coordinate sections of projective space

Source: Stacks Project, Tags 01NG, 01MV, 01MS, 01ND, 01JR and 01I4
(blueprint: lem-weil-pbc-projective-space-standard-charts-part2).
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveSpace

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The nonvanishing set of a homogeneous coordinate section is its standard chart.
Source: Stacks Project, Constructions, Tag 01MV; Modules, Tag 01CY.
(blueprint: lem-weil-pbc-projective-space-standard-charts-part2).

Proof: The pullback formula for the image of 1 identifies the global value of the
upstream morphism coordinateSection with twistOneSection. Naturality under restriction
then identifies coordinateSection with homOfGlobalSection of twistOneSection, since
maps from the structure module are determined by the image of 1. The proved theorem
nonvanishingLocus_eq_compl_support_zeroLocus identifies the stalk definition with the
complement of this morphism's zero-locus support. The upstream theorem
compl_support_zeroLocus_coordinateSection identifies that open with standardOpen. -/
theorem projectiveSpace_standardCharts_part2 (n : Type u) (S : Scheme.{u})
    [Finite n] [Nonempty n] :
    (∀ i : n, Scheme.Modules.nonvanishingLocus (twist n S 1) (twistOneSection n S i) =
          (standardOpen n S i : Set ℙ(n; S))) := by
  intro i
  have hsection :
      (coordinateSection n S i).app ⊤ (1 : Γ(ℙ(n; S), ⊤)) = twistOneSection n S i := by
    convert
      (pullbackSection_app_one (toProjInt n S)
        (Proj.unitToTwist
          (MvPolynomial.X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i))).symm
      using 1 <;>
      simp [coordinateSection, twistOneSection, twist] <;> rfl
  have hhom : homOfGlobalSection (twist n S 1) (twistOneSection n S i) =
      coordinateSection n S i := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext
    change (homOfGlobalSection (twist n S 1) (twistOneSection n S i)).app V.unop
        (1 : Γ(ℙ(n; S), V.unop)) =
      (coordinateSection n S i).app V.unop (1 : Γ(ℙ(n; S), V.unop))
    rw [homOfGlobalSection_app_one]
    have hn := Hom.app_presheaf_map (coordinateSection n S i)
      (homOfLE (le_top : V.unop ≤ ⊤)) (1 : Γ(ℙ(n; S), ⊤))
    rw [hsection] at hn
    change (coordinateSection n S i).app V.unop
      ((ℙ(n; S)).presheaf.map (homOfLE le_top).op (1 : Γ(ℙ(n; S), ⊤))) = _ at hn
    simpa only [map_one] using hn.symm
  rw [nonvanishingLocus_eq_compl_support_zeroLocus, hhom]
  exact congrArg (fun U : (ℙ(n; S)).Opens ↦ (U : Set ℙ(n; S)))
    (compl_support_zeroLocus_coordinateSection n S i)

end
end AlgebraicGeometry.ProjectiveSpace
