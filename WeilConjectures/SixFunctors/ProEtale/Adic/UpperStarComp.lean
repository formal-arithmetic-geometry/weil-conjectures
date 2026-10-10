/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.GeometricFrobenius

/-!
# The pullback isomorphisms of `ℓ`-adic sheaves on underlying sheaves

The pullback `g^*` of sheaves of modules over the constant `ℓ`-adic sheaf is the pullback of
the underlying sheaf of `ℚ̄_ℓ`-modules. This file shows that the same holds for the composition,
congruence and inverse-pushforward isomorphisms `ProEtale.adicUpperStarComp`,
`ProEtale.adicUpperStarCongr` and `ProEtale.adicUpperStarIsoLowerStarInv`: their components are
those of `ProEtale.upperStarComp`, `ProEtale.upperStarCongr` and
`ProEtale.upperStarIsoLowerStarInv`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- The composition isomorphism of `ℓ`-adic pullbacks is that of the underlying pullbacks. -/
lemma adicUpperStarComp_hom_app_hom {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (M : AdicSheaf l R) :
    ((adicUpperStarComp l h₁ h₂).hom.app M).hom =
      (upperStarComp (WeilCoefficients.{u} l) h₁ h₂).hom.app M.X := by
  simp only [adicUpperStarComp, upperStarComp, Iso.symm_hom, conjugateIsoEquiv_symm_apply_inv,
    Iso.symm_inv, conjugateEquiv_symm_apply_app,
    Adjunction.comp_unit_app]
  simp [adicUpperStar_map_hom, adicLowerStarComp_hom_app_hom, adicUpperStarLowerStarAdjunction,
    adicLowerStar_map_hom]
  erw [Adjunction.modAdjunction_unit_app_hom, Adjunction.modAdjunction_unit_app_hom,
    Adjunction.modAdjunction_counit_app_hom]
  rfl

/-- The congruence isomorphism of `ℓ`-adic pullbacks is that of the underlying pullbacks. -/
lemma adicUpperStarCongr_hom_app_hom {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g')
    (M : AdicSheaf l Y) :
    ((adicUpperStarCongr l h).hom.app M).hom =
      (upperStarCongr (WeilCoefficients.{u} l) h).hom.app M.X := by
  subst h
  rfl

/-- The identification `e^* ≅ (e⁻¹)_*` of `ℓ`-adic sheaves is that of the underlying sheaves. -/
lemma adicUpperStarIsoLowerStarInv_hom_app_hom {X Y : Scheme.{u}} (e : X ≅ Y)
    (M : AdicSheaf l Y) :
    ((adicUpperStarIsoLowerStarInv l e).hom.app M).hom =
      (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) e).hom.app M.X := by
  apply ((upperStarLowerStarAdjunction (WeilCoefficients.{u} l) e.hom).homEquiv _ _).injective
  have h1 := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (adicUpperStarLowerStarAdjunction l e.hom) (adicLowerStarEquivalence l e).symm.toAdjunction M
  have h2 := congrArg Mod.Hom.hom h1
  refine (Eq.trans rfl h2).trans ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_leftAdjointUniq_hom_app
    (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) e.hom)
    (lowerStarEquivalence (WeilCoefficients.{u} l) e).symm.toAdjunction M.X).symm
  simp only [adicLowerStarEquivalence, lowerStarEquivalence]
  rfl

/-- The inverse of the composition isomorphism of `ℓ`-adic pullbacks on underlying sheaves. -/
lemma adicUpperStarComp_inv_app_hom {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (M : AdicSheaf l R) :
    ((adicUpperStarComp l h₁ h₂).inv.app M).hom =
      (upperStarComp (WeilCoefficients.{u} l) h₁ h₂).inv.app M.X := by
  have := Iso.ext (α := (AdicSheaf.forget _).mapIso ((adicUpperStarComp l h₁ h₂).app M))
    (β := (upperStarComp (WeilCoefficients.{u} l) h₁ h₂).app M.X)
    (adicUpperStarComp_hom_app_hom h₁ h₂ M)
  exact congrArg Iso.inv this

/-- The inverse of `e^* ≅ (e⁻¹)_*` for `ℓ`-adic sheaves on underlying sheaves. -/
lemma adicUpperStarIsoLowerStarInv_inv_app_hom {X Y : Scheme.{u}} (e : X ≅ Y)
    (M : AdicSheaf l Y) :
    ((adicUpperStarIsoLowerStarInv l e).inv.app M).hom =
      (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) e).inv.app M.X := by
  have := Iso.ext (α := (AdicSheaf.forget _).mapIso ((adicUpperStarIsoLowerStarInv l e).app M))
    (β := (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) e).app M.X)
    (adicUpperStarIsoLowerStarInv_hom_app_hom e M)
  exact congrArg Iso.inv this

/-- The inverse of the congruence isomorphism of `ℓ`-adic pullbacks on underlying sheaves. -/
lemma adicUpperStarCongr_inv_app_hom {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g')
    (M : AdicSheaf l Y) :
    ((adicUpperStarCongr l h).inv.app M).hom =
      (upperStarCongr (WeilCoefficients.{u} l) h).inv.app M.X := by
  subst h
  rfl

end AlgebraicGeometry.ProEtale
