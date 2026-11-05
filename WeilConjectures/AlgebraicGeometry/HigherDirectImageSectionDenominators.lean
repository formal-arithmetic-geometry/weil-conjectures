/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.SectionCohomologyPrincipalLocalization
import WeilConjectures.AlgebraicGeometry.AffineLocalizationSheafification
import WeilConjectures.AlgebraicGeometry.HigherDirectImagePresheaf

/-! # Denominator bounds for higher direct image sections

Source: Stacks Project, Tags 01XJ (1), 09MR and 01E4.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}} (f : X ⟶ T) (ℱ : X.Modules)
variable [QuasiCompact f] [QuasiSeparated f] [HasInjectiveResolutions X.Modules]
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

end AlgebraicGeometry.Scheme.Modules
