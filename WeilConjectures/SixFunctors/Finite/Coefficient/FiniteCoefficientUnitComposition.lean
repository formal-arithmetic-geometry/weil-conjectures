/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientUnitInsertion
import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidalPresheaf

/-! # Composition of normalized regular scalar units

Source: lem-coef-integral-finite-extension.proof.md, quotient compatibility;
lem-coef-finite-dualizing.proof.md, the coefficient counit cocycle.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory

namespace WeilConjectures

attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.mapDerivedCategory

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2

open Functor.LaxMonoidal

private theorem ordinary_unit_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (S : Scheme.{u}) :
    Functor.LaxMonoidal.ε (Sheaf.restrictScalars S.smallEtaleTopology (ψ.comp φ)) =
      Functor.LaxMonoidal.ε (Sheaf.restrictScalars S.smallEtaleTopology φ) ≫
        (Sheaf.restrictScalars S.smallEtaleTopology φ).map
          (Functor.LaxMonoidal.ε (Sheaf.restrictScalars S.smallEtaleTopology ψ)) ≫
        (Sheaf.restrictScalarsCompIso S.smallEtaleTopology φ ψ (ψ.comp φ) rfl).hom.app
          (𝟙_ _) := by
  have hr : (Sheaf.restrictScalarsCompIso S.smallEtaleTopology φ ψ
      (ψ.comp φ) rfl).hom.app (𝟙_ _) = 𝟙 _ := by
    ext U x
    rfl
  erw [hr, Category.comp_id]
  apply Sheaf.hom_ext_of_ε_comp
  have h₁ := Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose S.smallEtaleTopology
    (ModuleCat.restrictScalars.{u + 1} (ψ.comp φ))
  have h₂ := Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose S.smallEtaleTopology
    (ModuleCat.restrictScalars.{u + 1} φ)
  have h₃ := Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose S.smallEtaleTopology
    (ModuleCat.restrictScalars.{u + 1} ψ)
  simp only [Functor.map_comp]
  rw [h₁, reassoc_of% h₂]
  rw [show (sheafToPresheaf _ _).map ((sheafCompose _
      (ModuleCat.restrictScalars.{u + 1} φ)).map
        (ε (sheafCompose S.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} ψ)))) =
      ((Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars.{u + 1} φ)).map
        ((sheafToPresheaf _ _).map (ε (sheafCompose S.smallEtaleTopology
          (ModuleCat.restrictScalars.{u + 1} ψ)))) from rfl,
    ← Functor.map_comp, h₃]
  have key : ε ((Functor.whiskeringRight S.Etaleᵒᵖ _ _).obj
        (ModuleCat.restrictScalars.{u + 1} φ)) ≫
      ((Functor.whiskeringRight S.Etaleᵒᵖ _ _).obj (ModuleCat.restrictScalars.{u + 1} φ)).map
        (ε ((Functor.whiskeringRight S.Etaleᵒᵖ _ _).obj
          (ModuleCat.restrictScalars.{u + 1} ψ))) =
      ε ((Functor.whiskeringRight S.Etaleᵒᵖ _ _).obj
        (ModuleCat.restrictScalars.{u + 1} (ψ.comp φ))) := by
    ext U : 2
    apply ModuleCat.hom_ext
    ext
    simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
    erw [ModuleCat.restrictScalars_η, ModuleCat.restrictScalars_η, ModuleCat.restrictScalars_η]
    rfl
  rw [Functor.map_comp, ← Category.assoc]
  erw [key]
  rfl

/-- The regular scalar-unit identifications compose with the associator obtained
from restriction of scalars. This is a coefficient-only statement, with no compact
support functor, exceptional adjoint, dualizing object or realization functor.

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-integral-finite-extension.proof.md, quotient compatibility in paragraphs 2--3;
lem-coef-finite-dualizing.proof.md, the coefficient counit cocycle.
(blueprint: lem-sf-finite-coefficient-unit-composition)

Proof: the ordinary scalar-unit comparisons are multiplication maps on the regular
module. Their restriction adjuncts send the regular generator to 1. The successive
adjuncts therefore compose to the adjunct for the composite coefficient homomorphism,
as is checked by the constant-sheaf adjunction on that generator. Apply the exact
restriction functors to complexes and localize. The scalar associator is the
left-adjoint conjugate of the resulting restriction-composition isomorphism.
The normalized derived unit comparisons agree with these localized ordinary
adjuncts: their representative equation is precisely UnitNormalization, whose
solution is unique. Transposing the ordinary generator equation thus gives the
displayed equation. This uses no flatness of either coefficient homomorphism;
the regular unit itself is K-flat. Identity maps and the zero ring obey the same
multiplication equations. -/
theorem finiteCoefficient_unit_composition
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (hχ : χ = ψ.comp φ)
    (S : Scheme.{u}) :
    (Etale.scalarExtension ψ S).map (Etale.ExceptionalCoefficients.unitIso φ S).hom ≫
        (Etale.ExceptionalCoefficients.unitIso ψ S).hom =
      (ProEtale.pbcFixedScalarExtensionComp S.smallEtaleTopology φ ψ χ hχ).hom.app
          (𝟙_ (Etale.DerivedCategoryModule A S)) ≫
        (Etale.ExceptionalCoefficients.unitIso χ S).hom := by
  subst χ
  rw [finiteCoefficient_unit_eq_scalarInsertion φ S,
    finiteCoefficient_unit_eq_scalarInsertion ψ S,
    finiteCoefficient_unit_eq_scalarInsertion (ψ.comp φ) S]
  exact SheafExactDegreeZero.scalarAdjointInsertion_comp S.smallEtaleTopology φ ψ
    (ε (Sheaf.restrictScalars S.smallEtaleTopology φ))
    (ε (Sheaf.restrictScalars S.smallEtaleTopology ψ))
    (ε (Sheaf.restrictScalars S.smallEtaleTopology (ψ.comp φ)))
    (ordinary_unit_comp φ ψ S)

end WeilConjectures
