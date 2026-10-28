/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W9
-/
module

public import Sheaf.Paper.LisseTowerEtaleDescentData

/-! # Local fixed-realization comparison for a finite-level model

Source: Stacks Project, proetale.tex, Tags 099Y, 099Z, 09B1 and 09BV.
(blueprint: new-lem-weil-pbc-lisse-finite-level-fixed-realization-local-model).
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
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard
  pbcDerivedRestrict constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow etaleIsomorphismNormalizationArrow
  lisseTowerAlgebraArrow lisseTowerFixedRealization

/-- The fixed-realization images of the normalized constant model and the supplied etale
complex are locally isomorphic on the model sieve.

Source: Stacks Project, proetale.tex, Tags 099Y, 099Z, 09B1 and 09BV.
(blueprint: new-lem-weil-pbc-lisse-finite-level-fixed-realization-local-model).

Proof: Restrict the supplied comparison to a member of the model sieve. Transport the
model isomorphism through the canonical constant quotient comparison and the inverse of
the restricted supplied comparison. Functoriality of inverse image and normalization
identifies the resulting source with the fixed realization of the normalized constant
model. The construction is local on the sieve and includes zero objects.
-/
theorem lisse_finite_level_fixed_realization_local_model
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (U : Y.ProEt) (n : ℕ)
    (N : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n))))
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (D : DerivedCategory
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))
    (hcomparison : Nonempty ((lisseTowerFixedRealization (U.hom ≫ g) d n).obj
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) U.left).mapDerivedCategory.obj D) ≅
        (adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj N))
    (hmodels : ∃ T : Sieve U, T ∈ ProEt.topology Y U ∧
      ∀ (W : Y.ProEt) (w : W ⟶ U), T w →
        Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj E ≅
          (adicTowerPullback (W.hom ≫ g)
            ((pbcAdicRings X d).obj (op n))).obj N)) :
    ∃ T : Sieve U, T ∈ ProEt.topology Y U ∧
      ∀ (W : Y.ProEt) (w : W ⟶ U), T w →
        Nonempty (
          (lisseTowerFixedRealization (W.hom ≫ g) d n).obj
            ((localProEtaleComparison w.left (lisseTowerEtaleRing d n)).obj
              ((normalizationConstant U.left.smallEtaleTopology).obj E)) ≅
          (lisseTowerFixedRealization (W.hom ≫ g) d n).obj
            ((localProEtaleComparison w.left (lisseTowerEtaleRing d n)).obj D)) := by
  sorry

end AlgebraicGeometry.Scheme
