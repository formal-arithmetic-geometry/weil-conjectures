/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J8
-/
module

public import Sheaf.Paper.LisseTowerPulledScalar

/-! # Constant models for localized fixed realization

Source: Stacks Project, Modules on Sites, Tags 03CY and 03DA; Sites, Tag 0H7J;
Cohomology on Sites, Tag 06YY.

This is the model-existence part of
`lem-weil-pbc-lisse-tower-localized-constants`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard pbcDerivedRestrict
  lisseTowerFixedRealization constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow lisseTowerAlgebraArrow

/-- Constant complexes admit the localized fixed-realization models used in the
constant part of the proper-base-change amplification.

Source: Stacks Project, Modules on Sites, Tags 03CY and 03DA; Sites, Tag 0H7J;
Cohomology on Sites, Tag 06YY.  The proof constructs the ordinary constant-sheaf
comparison by the constant-sheaf and inverse-image adjunctions, transports scalars
through the finite coefficient comparison, applies the resulting exact comparison
termwise to complexes, and localizes.  The construction is natural in every
algebraic complex and includes zero objects and empty schemes.
(blueprint: lem-weil-pbc-lisse-tower-localized-constants-model). -/
theorem lisseTower_localized_constants_model
    {X Z T S : Scheme.{u}} (g : Z ⟶ X) (a : T ⟶ S) (b : Z ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    let L (j : ℕ) := (ProEtale.upperStar
      (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) b).mapDerivedCategory ⋙
        lisseTowerFixedRealization g d j
    Nonempty (∀ (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))),
    (L n).obj ((localProEtaleComparison a
      (lisseTowerEtaleRing d n)).obj
        ((normalizationConstant S.smallEtaleTopology).obj E)) ≅
      (constantAdicQuotientRealization g d n).obj E) := by
  sorry

end AlgebraicGeometry.Scheme
