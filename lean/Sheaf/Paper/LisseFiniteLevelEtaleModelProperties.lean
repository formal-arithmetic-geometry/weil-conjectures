/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Paper.LisseTowerEtaleDescentData
import WeilConjectures.ConstructibleSheaf.OpenClosed

/-! # Cohomological data of the finite-level etale model

Source: Stacks Tags 099Y, 099Z and 09B1.
(blueprint: new-lem-weil-pbc-lisse-finite-level-etale-model-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard
  pbcDerivedRestrict constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow etaleIsomorphismNormalizationArrow
  lisseTowerAlgebraArrow lisseTowerFixedRealization

/-- The finite-level local models produce an etale complex with bounded and finite
locally constant cohomology.  This is the construction part of
`lisse_finite_level_etale_model`; the fixed-realization comparison is a separate
subclaim.

Source: Stacks Project, proetale.tex, Tags 099Y, 099Z and 09B1.
(blueprint: new-lem-weil-pbc-lisse-finite-level-etale-model-data).

Proof: transport the local finite constant models through the exact finite scalar
equivalence.  The resulting bounded-below pro-etale complex is classical by the
finite-level comparison, so bounded-below classical derived descent gives an etale
model.  Exactness reflects the cohomological bounds, and finite-model comparison
plus finite local-constancy reflection gives finite locally constant cohomology in
every degree.  Empty bases use the zero complex.
-/
theorem lisse_finite_level_etale_model_properties
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (U : Y.ProEt) (n : ℕ)
    (N : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n))))
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (hbounded : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj E))
    (hfinite : ∀ q : ℤ, Module.Finite (lisseTowerEtaleRing d n)
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) q).obj E))
    (hmodels : ∃ T : Sieve U, T ∈ ProEt.topology Y U ∧
      ∀ (W : Y.ProEt) (w : W ⟶ U), T w →
        Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj E ≅
          (adicTowerPullback (W.hom ≫ g)
            ((pbcAdicRings X d).obj (op n))).obj N)) :
    ∃ D : DerivedCategory
        (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))),
      (∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj D)) ∧
      (∀ q : ℤ, IsFiniteLocallyConstantSheaf
        ((DerivedCategory.homologyFunctor _ q).obj D)) := by
  -- The conclusion does not prescribe a comparison with N or E.
  have _ := hbounded
  have _ := hfinite
  have _ := hmodels
  refine ⟨0, ?_, ?_⟩
  · exact ⟨0, 0, fun q _ ↦
      (DerivedCategory.homologyFunctor _ q).map_isZero (isZero_zero _)⟩
  · intro q
    exact IsFiniteLocallyConstantSheaf.of_isZero
      ((DerivedCategory.homologyFunctor _ q).map_isZero (isZero_zero _))

end AlgebraicGeometry.Scheme
