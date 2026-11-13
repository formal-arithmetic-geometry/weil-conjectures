/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceRestriction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finitely.ProEtaleFinitelyPresentedLocalModelsComparisonSupplement
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientEtaleLocalEncodingForward
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientEtaleLocalEncodingReverse

/-! # Comparing finite etale models with intrinsic pro-etale local systems

Source: sites-modules.tex, localization of ringed sites, Tag 04IX.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The etale finite-model condition for a single sheaf agrees with finite
pro-etale models of its existing fixed-scalar chart restriction.
This compares local models; it asserts no exactness or closure property.

Source: sites-modules.tex, Tag 04IX, localization of ringed sites; Tags 03CY and 093J,
constant modules and change of coefficients. -/
theorem finiteCoefficient_etaleLocal_encoding
    (X : Scheme.{t}) (B : Type t) [CommRing B] [Finite B]
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (φ : adicConstantRing X B ⟶ R) (hφ : IsIso φ) (V : X.Etale)
    (F : SheafOfModules.{t + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) :
    let R₀ := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R
    let P : ObjectProperty (SheafOfModules.{t + 1} R₀) := fun F ↦
      ∀ (W : X.Etale) (_g : W ⟶ V),
        ∃ S : Sieve W, S ∈ X.smallEtaleTopology W ∧
          ∀ (Z : X.Etale) (f : Z ⟶ W), S f →
            ∃ N : ModuleCat.{t} B, Module.Finite B N ∧ Nonempty
              ((SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj Z)).obj F ≅
                (SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj Z)).obj
                  ((completedAdicChange X (φ)).obj
                    ((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
                      ModuleCat.restrictScalars.{t + 1}
                        (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙
                      koszulConstantFunctor X B).obj N)))
    P F ↔ ProFiniteModels.fixedModels (ProEt.topology V.left) (ULift.{t + 1} B)
      ((finiteCoefficientSliceRestriction X B R φ V).obj F) := by
  dsimp
  constructor
  · exact finiteCoefficient_etaleLocal_encoding_forward X B R φ hφ V F
  · exact finiteCoefficient_etaleLocal_encoding_reverse X B R φ hφ V F

end AlgebraicGeometry.Scheme
