/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M7
-/
module

public import Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation

/-! # The canonical bundle projection at the coefficient unit

Source: sk-thm-dnc, final comparison with vector-bundle purity;
thm-amb-vector-bundle-purity, opening paragraph.
(blueprint: lem-trf-bundle-section-projection-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.Etale

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence

/-- At the scalar unit, the specified projection followed by the canonical source unit
identification is exactly the compact-support left unitor. This assertion involves no
integration trace, exceptional adjoint, or inverse projection.
Source: sk-thm-dnc, final comparison with vector-bundle purity;
thm-amb-vector-bundle-purity, opening paragraph.
(blueprint: lem-trf-bundle-section-projection-unit).

Proof: Expand the coefficient-first projection as target symmetry, the ordinary
projection, and source symmetry. The canonical pullback of the scalar unit equals the
monoidal unit map of derived inverse image: apply the single-functor unit comparison
and cancel its identity components. Naturality of the source braiding moves this unit
map before the braiding. The source left unitor then becomes the right unitor.
The right-unit equation for the ordinary projection identifies the resulting composite
with the target right unitor. The outer braiding changes this into the target left
unitor. These equations hold for every rank, including zero, and the empty base. -/
theorem bundleSectionProjection_unit (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    vectorBundlePurityProjectionMap A N hA S d M (ordinaryFiniteUnit A S) ≫
        (vectorBundlePurityLower A S d M).map
          (bundleSectionPurityUnitIso N A hA S d M).hom =
      (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) S
        (vectorIntegrationSource A N hA S d M)).hom := by
  sorry

end AlgebraicGeometry.Etale
