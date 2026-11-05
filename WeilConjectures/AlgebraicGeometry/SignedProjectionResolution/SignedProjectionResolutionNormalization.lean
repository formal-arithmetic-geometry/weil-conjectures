/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionFormulaArrows
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.Algebra.Homology.FixedTensorLocalization.FixedTensorLocalizationComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleMixedProjectionMate

/-! # Normalized signed projection formula on chosen resolutions

Source: main-20261015 blueprint, proper base change, perfect projection formula,
proof paragraphs 2 and 3; Stacks Tag 0B56, equation-projection-formula-map
(blueprint: lem-weil-pbc-signed-projection-resolution-normalization).

The source and target comparisons are the specified mixed tensor comparisons,
with arbitrary derived isomorphisms to the chosen representatives. All operations
are on the original small pro-etale sites and ordinary uncompleted derived categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.SignedProjectionResolution

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

variable (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S)
  (K : DerivedCategory (proEtaleRingModules X S))
  (P : DerivedCategory (proEtaleRingModules Y R))
  (I : CochainComplex (proEtaleRingModules X S) ℤ) (hI : I.IsKInjective)
  (alpha : K ≅ DerivedCategory.Q.obj I)
  (F : CochainComplex (proEtaleRingModules Y R) ℤ)
  (beta : DerivedCategory.Q.obj F ≅ P)
  (package : SheafOfModules.StrictPerfectCoefficientPackageOnSite
    ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) F)
  (bounded : ∃ l h : ℤ, ∀ r : ℤ, r < l ∨ h < r → IsZero (F.X r))

end AlgebraicGeometry.Scheme.SignedProjectionResolution
