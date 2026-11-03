/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.ModelVanishing
public import WeilConjectures.TraceFormula.CurveLocal.FrobeniusModel
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSectionsRestrictionBasic
public import WeilConjectures.Compactification.NagataCompactification

/-! # Localization of the supported restriction on a curve

Source: literature/blueprint/latest/blueprint/sec-trace-formula/
sk-lem-tf-curve-restriction-zero/det-tf-restriction-zero-localization.md,
clauses (i)--(iii) (blueprint: det-tf-restriction-zero-localization).

All objects and arrows below use classical étale sheaves of modules. The two copies
of the strictly local curve are identical copies of `strictLocalization M.y`.
The external product on the complement of both axes is written as the restriction
of the external product on the original curve. This is precisely the restriction of
`N ⊠ Q`, by functoriality and monoidality of inverse image; it avoids choosing a new
external-product comparison or new projections on strict henselizations.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.CurveLocalModel

open Scheme

local instance {S T : Scheme.{u}} (f : S ⟶ T)
    [SmoothOfRelativeDimension 1 f] : Smooth f :=
  SmoothOfRelativeDimension.smooth 1 f

variable {k : Type u} [Field k] [IsAlgClosed k] (M : CurveLocalModel k)

local instance : IsClosedImmersion M.y :=
  isClosedImmersion_of_comp_eq_id M.f M.y M.y_comp

/-- The punctured strict localization of the curve at `y`, expressed as the inverse
image of the complement of `y` on the original curve.
Source: clause (i) (blueprint: det-tf-restriction-zero-localization). -/
abbrev localizationPuncture : (strictLocalization M.y).Opens :=
  strictLocalizationToBase M.y ⁻¹ᵁ M.y.openComplement

/-- The complement of both axes, with its inclusion into `T - V`.
Source: clause (i), `g` (blueprint: det-tf-restriction-zero-localization). -/
abbrev twoAxesOpen : M.T.Opens := M.hH.openComplement ⊓ M.v.openComplement

/-- The open inclusion `g : T - (H ∪ V) → T - V`.
Source: clause (i) (blueprint: det-tf-restriction-zero-localization). -/
abbrev twoAxesInclusion : M.twoAxesOpen.toScheme ⟶ M.v.openComplement.toScheme :=
  M.T.homOfLE inf_le_right

/-- The restriction of `N ⊠ Q` to `T - (H ∪ V)`, written as restriction of the
original external product `L ⊠ K`. In the theorem `L` is the actual Verdier dual.
Source: clause (i) (blueprint: det-tf-restriction-zero-localization). -/
def puncturedExternal {Λ : Type (u + 1)} [CommRing Λ]
    (L K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  D((M.twoAxesOpen.ι)^*[ModuleCat.{u + 1} Λ]).obj
    (D((M.τ)^*[ModuleCat.{u + 1} Λ]).obj
      (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K))

/-- Extension by zero of the punctured external product to `T - V`.
Source: clause (i), `g_!(N ⊠ Q)`
(blueprint: det-tf-restriction-zero-localization). -/
def puncturedExtension {Λ : Type (u + 1)} [CommRing Λ]
    (L K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  D((M.twoAxesInclusion)_!open[ModuleCat.{u + 1} Λ]).obj (M.puncturedExternal L K)

/-- The restriction of `N ⊠ Q` to the punctured diagonal, expressed as the
pullback of the original external product. Both coordinates avoid `y` there.
Source: clause (iii) (blueprint: det-tf-restriction-zero-localization). -/
def puncturedDiagonalProduct {Λ : Type (u + 1)} [CommRing Λ]
    (L K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  D((M.yB.openComplement.ι ≫ M.b ≫ M.τ)^*[ModuleCat.{u + 1} Λ]).obj
    (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K)

end AlgebraicGeometry.Etale.CurveLocalModel
