/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.ModelVanishing
public import WeilConjectures.TraceFormula.CurveLocal.FrobeniusModel
public import WeilConjectures.TraceFormula.CurveLocal.SectionsRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSectionsRestrictionBasic

/-! Compatibility of the punctured-diagonal comparison with the localization triangles.

Source: literature/blueprint/latest/blueprint/sec-trace-formula/
sk-lem-tf-curve-restriction-zero/det-tf-restriction-zero-localization.md, clause (iii)
(blueprint: restriction-zero-localization-compatibility).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.CurveLocalModel

open Scheme

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Clause (iii), the diagonal comparison and the Leray/ordinary-restriction compatibility.

The proof transports the canonical third-component square through the external-product
comparison, then applies Leray to the open projection and restricts to the punctured diagonal.
The required coherence involves two independent derived naturality calculations and is left as a
named obligation for the next proof pass.
(blueprint: restriction-zero-localization-compatibility). -/
theorem restrictionZeroLocalization_compatibility
    {Λ : Type (u + 1)} [CommRing Λ]
    (M : CurveLocalModel k)
    (L K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (P : DerivedCategory.Plus
      (Sheaf M.T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (eP : P.obj ≅ D((M.τ)^*[ModuleCat.{u + 1} Λ]).obj
      (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K))
    (hA : IsZero ((sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) M.a).obj P).obj₂)
    (hB : IsZero ((sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) M.yB).obj
      (D+((M.b)^*[ModuleCat.{u + 1} Λ]).obj P)).obj₂) :
    let F := D((M.T.homOfLE inf_le_right)_!open[ModuleCat.{u + 1} Λ]).obj
      (D(((M.hH.openComplement ⊓ M.v.openComplement).ι)^*[ModuleCat.{u + 1} Λ]).obj
        (D((M.τ)^*[ModuleCat.{u + 1} Λ]).obj
          (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K)))
    let S := (sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) M.a).obj P
    let B := (sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) M.yB).obj
      (D+((M.b)^*[ModuleCat.{u + 1} Λ]).obj P)
    let rho := sectionsWithSupportRestriction (ModuleCat.{u + 1} Λ) M.b M.a M.yB
      M.openComplement_yB_le P
    let r := puncturedRestrictionMap (ModuleCat.{u + 1} Λ) M.b M.a M.yB
      M.openComplement_yB_le P
    let iO : M.O.toScheme ⟶ M.v.openComplement.toScheme := M.T.homOfLE inf_le_right
    let FO := D((iO)^*[ModuleCat.{u + 1} Λ]).obj F
    Nonempty (D((M.ψ)^*[ModuleCat.{u + 1} Λ]).obj FO ≅
      D((M.yB.openComplement.ι ≫ M.b ≫ M.τ)^*[ModuleCat.{u + 1} Λ]).obj
        (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K)) ∧
      ∃ (s : S.obj₃ ≅
          (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) M.O.toScheme).obj FO)
        (t : B.obj₃ ≅
          (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ)
            M.yB.openComplement.toScheme).obj
            (D((M.ψ)^*[ModuleCat.{u + 1} Λ]).obj FO)),
        r ≫ t.hom = s.hom ≫ globalSectionsRestriction M.ψ FO ∧
        (rho = 0 ↔ globalSectionsRestriction M.ψ FO = 0) := by
  sorry

end AlgebraicGeometry.Etale.CurveLocalModel
