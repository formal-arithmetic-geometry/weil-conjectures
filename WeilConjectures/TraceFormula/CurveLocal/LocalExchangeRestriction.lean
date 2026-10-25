/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSectionsRestrictionBasic
public import WeilConjectures.TraceFormula.CurveLocal.ExchangeRestriction

/-!

# The exchange restriction on the strictly local model is the supported restriction

On the strictly local model `M` of a curve (`AlgebraicGeometry.Etale.CurveLocalModel`), with
closed immersions `a : G ⟶ T`, `b : B ⟶ T` and `Y = G ×_T B`, this file compares two forms of
the supported restriction of blueprint `det-tf-supported-restriction`, (2), for a bounded below
complex `Q` on `T`:

* the classical `ρ_{a,b} : RΓ_G(T, Q) ⟶ RΓ_Y(B, b^* Q)`
  (`AlgebraicGeometry.Etale.sectionsWithSupportRestriction`), a map of localization triangles;
* derived global sections over `Y` of the étale exchange restriction
  `Lι'^* Ra^! Q ⟶ Ry_B^! Lb^* Q` (`AlgebraicGeometry.Etale.exchangeRestriction`).

Under the identifications `RΓ_G(T, Q) ≅ RΓ(G, Ra^! Q)` and `RΓ(Y, Ry_B^! N) ≅ RΓ_Y(B, N)`, the
first is the restriction from `G` to `Y` followed by the second.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.CurveLocalModel

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]
  (M : CurveLocalModel k)

/-- **The supported restriction through the exchange restriction**: on the strictly local
model, the classical supported restriction `ρ_{a,b} : RΓ_G(T, Q) ⟶ RΓ_Y(B, b^* Q)` is, through the
identifications `RΓ_G(T, Q) ≅ RΓ(G, Ra^! Q)` and `RΓ(Y, Ry_B^! Lb^* Q) ≅ RΓ_Y(B, b^* Q)`, the
restriction from `G` to `Y = G ×_T B` followed by derived global sections over `Y` of the étale
exchange restriction of the square `ι' ≫ a = y_B ≫ b`. -/
theorem exists_sectionsWithSupportRestriction_eq
    (Q : DerivedCategory.Plus (Sheaf M.T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃ (t : ((sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) M.a).obj Q).obj₁ ≅
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) M.G).obj
          ((R(M.a)^![ModuleCat.{u + 1} Λ]).obj Q.obj))
      (e : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) M.Y).obj
        ((R(M.yB)^![ModuleCat.{u + 1} Λ]).obj ((L((M.b)^*[ModuleCat.{u + 1} Λ])).obj Q.obj)) ≅
        ((sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) M.yB).obj
          ((Functor.mapDerivedCategoryPlus (M.b)^*[ModuleCat.{u + 1} Λ]).obj Q)).obj₁),
      sectionsWithSupportRestriction (ModuleCat.{u + 1} Λ) M.b M.a M.yB M.openComplement_yB_le Q =
        t.hom ≫ globalSectionsRestriction (A := ModuleCat.{u + 1} Λ) M.ιY
            ((R(M.a)^![ModuleCat.{u + 1} Λ]).obj Q.obj) ≫
          (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) M.Y).map
            ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) M.ιY).inv.app _ ≫
              exchangeRestriction Λ M.isPullback_ιY Q.obj) ≫ e.hom :=
  sorry

end AlgebraicGeometry.Etale.CurveLocalModel
