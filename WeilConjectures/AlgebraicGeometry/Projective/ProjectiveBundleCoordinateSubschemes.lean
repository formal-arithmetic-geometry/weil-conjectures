/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData
import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.RingTheory.MvPolynomial.Ideal
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSectionChart
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartPolynomial
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientGeometry
import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Canonical

/-! # The coordinate hyperplane of projective space

Source: Stacks Project, Constructions, Tags 01NG and 01MS.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
private def renameGraded {I J R : Type u} [CommRing R] (e : I ≃ J) :
    MvPolynomial.homogeneousSubmodule I R →+*ᵍ
      MvPolynomial.homogeneousSubmodule J R where
  toRingHom := (MvPolynomial.rename e).toRingHom
  map_mem := fun h ↦ h.rename_isHomogeneous
private lemma renameGraded_comp {I J R : Type u} [CommRing R] (e : I ≃ J) :
    (renameGraded (R := R) e.symm).comp (renameGraded e) =
      GradedRingHom.id (MvPolynomial.homogeneousSubmodule I R) := by
  apply GradedRingHom.ext
  intro p
  exact (MvPolynomial.renameEquiv R e).symm_apply_apply p
end

end AlgebraicGeometry
