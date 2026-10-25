/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChange
public import WeilConjectures.TraceFormula.SupportedRestrictionCoefficientChange

/-!

# The supported restriction with `E`-coefficients and its extension to `ℚ̄_ℓ`

For a finite subextension `E ⊆ ℚ̄_ℓ` and a fixed locus `F` of a correspondence, the supported
restriction can be formed with `E`-coefficients from the compact-support base change of the fixed
square (`FixedLocus.supportedRestrictionE`). Under the extension of scalars `T : E ⟶ ℚ̄_ℓ` it
becomes the `ℚ̄_ℓ`-supported restriction of `T P`
(`FixedLocus.map_supportedRestrictionE_comp`), given the compatibility of base change with the
coefficient comparisons (blueprint `sk-thm-sf-compatibility`, (7):
`boundedConstructibleLowerShriekBaseChange_toPadicAlgCl`). With the `f^!` clause of blueprint
`sk-prop-scalar-six` (`isIso_boundedConstructibleUpperShriekToPadicAlgCl`) this transports the
vanishing of a stalk of the supported restriction from `E` to `ℚ̄_ℓ`
(`FixedLocus.upperStar_map_supportedRestriction_eq_zero_of_supportedRestrictionE`).

-/

@[expose] public section


universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {c : Correspondence ℓ K}

namespace Correspondence.FixedLocus

variable (F : c.FixedLocus) (E : FiniteIntermediateField ℓ)

/-- Compact-support base change `Rc_! ⋙ LΔ^* ≅ Lι^* ⋙ Rd_!` in the fixed square, with
`E`-coefficients. -/
noncomputable def lowerShriekBaseChangeIsoE :
    boundedConstructibleLowerShriek (Profinite.continuousMapRingObj E) ℓ c.support ⋙
        boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (diag X) ≅
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ F.ι ⋙
        boundedConstructibleLowerShriek (Profinite.continuousMapRingObj E) ℓ F.d :=
  asIso (boundedConstructibleLowerShriekBaseChange_padicSubfield ℓ E F.isPullback)

/-- The supported restriction `Lι^* Rc^! P ⟶ Rd^! LΔ^* P` with `E`-coefficients: the mate
`Rc^! ⋙ Lι^* ⟶ LΔ^* ⋙ Rd^!` of the inverse of compact-support base change in the fixed square. -/
noncomputable def supportedRestrictionE
    (P : Dᵇc((X ⨯ X).left)⟦Profinite.continuousMapRingObj E⟧) :
    (boundedConstructibleUpperStar _ ℓ F.ι).obj
        ((boundedConstructibleUpperShriek _ ℓ c.support).obj P) ⟶
      (boundedConstructibleUpperShriek _ ℓ F.d).obj
        ((boundedConstructibleUpperStar _ ℓ (diag X)).obj P) :=
  (CategoryTheory.mateEquiv (boundedConstructibleUpperShriekAdjunction _ ℓ c.support)
    (boundedConstructibleUpperShriekAdjunction _ ℓ F.d)
    (TwoSquare.mk _ _ _ _ (F.lowerShriekBaseChangeIsoE E).inv)).natTrans.app P

/-- **The supported restriction under `E ⟶ ℚ̄_ℓ`**: the extension of scalars `T` of the
`E`-supported restriction of `P`, followed by the `f^!`-exchange for `d` and the pullback
comparison for `Δ`, is the pullback comparison for `ι`, then `Lι^*` of the `f^!`-exchange for `c`,
then the `ℚ̄_ℓ`-supported restriction of `T P`. -/
theorem map_supportedRestrictionE_comp
    (P : Dᵇc((X ⨯ X).left)⟦Profinite.continuousMapRingObj E⟧) :
    (boundedConstructibleToPadicAlgCl F.F.left ℓ E).map (F.supportedRestrictionE E P) ≫
        (boundedConstructibleUpperShriekToPadicAlgCl ℓ E F.d).app _ ≫
        (boundedConstructibleUpperShriek _ ℓ F.d).map
          ((boundedConstructibleUpperStarToPadicAlgClIso ℓ E (diag X)).hom.app P) =
      (boundedConstructibleUpperStarToPadicAlgClIso ℓ E F.ι).hom.app _ ≫
        (boundedConstructibleUpperStar _ ℓ F.ι).map
          ((boundedConstructibleUpperShriekToPadicAlgCl ℓ E c.support).app P) ≫
        F.supportedRestriction ((boundedConstructibleToPadicAlgCl (X ⨯ X).left ℓ E).obj P) := by
  have h := Adjunction.map_mateEquiv_app_comp
    (boundedConstructibleUpperShriekAdjunction _ ℓ c.support)
    (boundedConstructibleUpperShriekAdjunction _ ℓ F.d)
    (boundedConstructibleUpperStar _ ℓ F.ι) (boundedConstructibleUpperStar _ ℓ (diag X))
    (F.lowerShriekBaseChangeIsoE E)
    (boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ c.support)
    (boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ F.d)
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F.ι)
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (diag X))
    F.lowerShriekBaseChangeIso
    (boundedConstructibleToPadicAlgCl (X ⨯ X).left ℓ E)
    (boundedConstructibleToPadicAlgCl c.C.left ℓ E)
    (boundedConstructibleToPadicAlgCl F.F.left ℓ E)
    (boundedConstructibleToPadicAlgCl X.left ℓ E)
    (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E c.support)
    (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E F.d)
    (boundedConstructibleUpperStarToPadicAlgClIso ℓ E F.ι)
    (boundedConstructibleUpperStarToPadicAlgClIso ℓ E (diag X))
    (boundedConstructibleLowerShriekBaseChange_toPadicAlgCl ℓ E F.isPullback) P
  have e := F.supportedRestriction_eq_mateEquiv
    ((boundedConstructibleToPadicAlgCl (X ⨯ X).left ℓ E).obj P)
  simp only [supportedRestrictionE, boundedConstructibleUpperShriekToPadicAlgCl_eq_mateEquiv, e]
  dsimp only [Functor.comp_obj] at h ⊢
  with_reducible exact h

/-- **Transport of the vanishing of the supported restriction from `E` to `ℚ̄_ℓ`**: if the stalk
along `z : T ⟶ Fix(c)` of the extension of scalars to `ℚ̄_ℓ` of the `E`-supported restriction of
`P` vanishes, so does the stalk of the `ℚ̄_ℓ`-supported restriction of `ℚ̄_ℓ ⊗ P`. This uses the
`f^!` clause of blueprint `sk-prop-scalar-six` (`isIso_boundedConstructibleUpperShriekToPadicAlgCl`)
for the support `c`. -/
theorem upperStar_map_supportedRestriction_eq_zero_of_supportedRestrictionE
    {T : Over (Spec (.of k))} [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [IsSeparated T.hom] (z : T ⟶ F.F)
    (P : Dᵇc((X ⨯ X).left)⟦Profinite.continuousMapRingObj E⟧)
    (h : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).map
      ((boundedConstructibleToPadicAlgCl F.F.left ℓ E).map (F.supportedRestrictionE E P)) = 0) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).map
      (F.supportedRestriction ((boundedConstructibleToPadicAlgCl (X ⨯ X).left ℓ E).obj P)) = 0 := by
  have := isIso_boundedConstructibleUpperShriekToPadicAlgCl ℓ E c.support
  have h1 := congrArg (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).map
    (F.map_supportedRestrictionE_comp E P)
  simp only [Functor.map_comp, h, Limits.zero_comp] at h1
  exact (Preadditive.IsIso.comp_left_eq_zero _ _).1
    ((Preadditive.IsIso.comp_left_eq_zero _ _).1 h1.symm)

/-- **Transport of the vanishing of a stalk of the supported restriction from `E` to `ℚ̄_ℓ`**: if
the stalk along `z : T ⟶ Fix(c)` of the `E`-supported restriction of `P` vanishes, so does the
stalk of the `ℚ̄_ℓ`-supported restriction of `ℚ̄_ℓ ⊗ P`. -/
theorem upperStar_map_supportedRestriction_eq_zero_of_upperStar_map_supportedRestrictionE
    {T : Over (Spec (.of k))} [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [IsSeparated T.hom] (z : T ⟶ F.F)
    (P : Dᵇc((X ⨯ X).left)⟦Profinite.continuousMapRingObj E⟧)
    (h : (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ z).map
      (F.supportedRestrictionE E P) = 0) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).map
      (F.supportedRestriction ((boundedConstructibleToPadicAlgCl (X ⨯ X).left ℓ E).obj P)) = 0 := by
  refine F.upperStar_map_supportedRestriction_eq_zero_of_supportedRestrictionE E z P ?_
  have h1 := NatIso.map_eq_zero_of_map_eq_zero (boundedConstructibleUpperStarToPadicAlgClIso ℓ E z)
    (f := F.supportedRestrictionE E P) (by
      dsimp only [Functor.comp_map]
      refine (congrArg (boundedConstructibleToPadicAlgCl T.left ℓ E).map ?_).trans
        (Functor.map_zero _ _ _)
      with_reducible exact h)
  dsimp only [Functor.comp_map] at h1
  with_reducible exact h1

end Correspondence.FixedLocus

end AlgebraicGeometry.ProEtale.CondensedRing
