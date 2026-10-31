/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StandingExceptionalHomNaturality

/-! # Restricted exceptional adjunction with the specified counit normalization

Source: blueprint thm-sf-ambient-adjoint-class, class-restricted adjunction
(blueprint: def-pur-standing-exceptional-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]

/-- Restrict the fixed-comparison exceptional Hom bijection to full object domains.
Both inverse-image and compact-support data are the existing functors; the adjunction
uses precisely `standingExceptionalHomEquiv`, including its fixed proper/open mate.
Source: blueprint thm-sf-ambient-adjoint-class, class-restricted adjunction
(blueprint: def-pur-standing-exceptional-adjunction). -/
def standingExceptionalAdjunction
    (P : ObjectProperty (_root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))))
    (Q : ObjectProperty (_root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))))
    (hP : P ≤ DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X)
    (hQ : Q ≤ _root_.DerivedCategory.TStructure.t.plus)
    (hF : ∀ M, P M → Q ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj M))
    (hG : ∀ K, Q K → P ((rightDerivedUpperShriek Λ f).obj K)) :=
  Adjunction.mkOfHomEquiv
    (F := Q.lift (P.ι ⋙ rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f)
      (fun M ↦ hF _ M.property))
    (G := P.lift (Q.ι ⋙ rightDerivedUpperShriek Λ f) (fun K ↦ hG _ K.property))
    { homEquiv M K :=
        { toFun a := ObjectProperty.homMk
            (standingExceptionalHomEquiv Λ f (hP _ M.property) (hQ _ K.property) a.hom)
          invFun a := ObjectProperty.homMk
            ((standingExceptionalHomEquiv Λ f (hP _ M.property) (hQ _ K.property)).symm a.hom)
          left_inv a := by
            ext
            exact (standingExceptionalHomEquiv Λ f _ _).symm_apply_apply a.hom
          right_inv a := by
            ext
            exact (standingExceptionalHomEquiv Λ f _ _).apply_symm_apply a.hom }
      homEquiv_naturality_left_symm {M M' K} a b := by
        ext
        exact standingExceptionalHomEquiv_naturality_left_symm Λ f (hP _ M.property)
          (hP _ M'.property) (hQ _ K.property) a.hom b.hom
      homEquiv_naturality_right {M K K'} a b := by
        ext
        exact standingExceptionalHomEquiv_naturality_right Λ f (hP _ M.property)
          (hQ _ K.property) (hQ _ K'.property) a.hom b.hom }

end AlgebraicGeometry.ProEtale
