/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import Mathlib.Algebra.Module.LocalizedModule.Away
import WeilConjectures.AlgebraicGeometry.SectionCohomologyPrincipalLocalization

/-! # Principal localization of the higher-image cohomology presheaf

## References

* Stacks Project, Tags 09MR and 01E4
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The restriction on resolution cohomology over inverse images of affine opens is
module localization at the defining function. This concerns presheaf cohomology,
not sections of the higher direct image sheaf. (Stacks, Tags 09MR and 01E4) -/
theorem higherImageCohomologyPresheaf_isLocalized
    {X T : Scheme.{u}} (f : X ⟶ T) [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] (I : InjectiveResolution F) (q : ℕ)
    (W : T.Opens) (hW : IsAffineOpen W) (a : Γ(T, W)) :
    let P := sectionCohomologyPresheaf
      (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) q
    IsLocalizedModule.Away a (P.map (homOfLE (T.basicOpen_le a)).op).hom := by
  exact sectionCohomologyPresheaf_isLocalized_away f F I q W hW a

end AlgebraicGeometry.Scheme.Modules
