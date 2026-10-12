/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Paper.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
import Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import Sheaf.AlgebraicGeometry.InvertSCOhomology

/-!
# A power of a section kills a positive cohomology class

Source: Stacks Project, Cohomology of Schemes, Lemma 01XR
(blueprint: lem-sc-section-affine-open-kills-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- If the nonvanishing open of a section of an invertible module is affine, every positive
cohomology class of a quasi-coherent module is killed by some tensor power of that section.
The map is induced by `F ≅ F ⊗ 𝒪_X ⟶ F ⊗ L^{⊗ e}`, with second factor `s^{⊗ e}`.

Source: Stacks Project, Cohomology of Schemes, Lemma 01XR
(blueprint: lem-sc-section-affine-open-kills-cohomology).

Proof:
1. Apply lem-sc-invert-s-cohomology (Stacks 09MR) to identify cohomology on the
nonvanishing open with the degree-zero localization of graded twisted cohomology.
The restriction of `F` is quasi-coherent. Since this open is affine, its positive
cohomology vanishes by pqf-lem-affine-vanishing (Stacks 01XB). Thus the image of the
class in the localization is zero.
2. By the definition of module localization, a homogeneous class whose fraction with
unit denominator vanishes is annihilated by a power of the section. In degree `e`
this is exactly the cohomology map induced by `f ↦ f ⊗ s^e` displayed below. -/
theorem exists_tensorPowSection_cohomology_eq_zero
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules) [L.IsInvertible] (s : Γ(L, ⊤))
    (U : X.Opens) (hU : (U : Set X) = nonvanishingLocus L s) (hAffine : IsAffineOpen U)
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ) (hp : 0 < p)
    (xi : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F) :
    ∃ e : ℕ, (RingedSpace.moduleCohomology X.toRingedSpace p).map
      ((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) e) xi = 0 := by
  sorry

end AlgebraicGeometry.Scheme.Modules
