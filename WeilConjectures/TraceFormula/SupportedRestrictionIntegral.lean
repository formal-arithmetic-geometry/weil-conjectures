/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.SupportedRestrictionRational

/-!

# The supported restriction with `𝒪_E`-coefficients and its rationalization

For a finite subextension `E ⊆ ℚ̄_ℓ` with ring of integers `𝒪_E` and a fixed locus `F` of a
correspondence, the supported restriction can be formed with `𝒪_E`-coefficients from the
compact-support base change of the fixed square (`FixedLocus.supportedRestrictionIntegral`).
Under the extension of scalars `T : 𝒪_E ⟶ E` it becomes the `E`-supported restriction of `T P`
(`FixedLocus.map_supportedRestrictionIntegral_comp`), given the compatibility of base change with
the coefficient comparisons (blueprint `sk-thm-sf-package`, (2):
`boundedConstructibleLowerShriekBaseChange_extendScalars`). With the `f^!` clause of blueprint
`sk-prop-scalar-six` (`isIso_boundedConstructibleUpperShriekExtendScalars`) this transports the
vanishing of a stalk of the supported restriction from `𝒪_E` to `E`
(`FixedLocus.upperStar_map_supportedRestrictionE_eq_zero_of_supportedRestrictionIntegral`).

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
`𝒪_E`-coefficients. -/
noncomputable def lowerShriekBaseChangeIsoIntegral :
    boundedConstructibleLowerShriek (Profinite.padicIntegersRingObj ℓ E.1) ℓ c.support ⋙
        boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ (diag X) ≅
      boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ F.ι ⋙
        boundedConstructibleLowerShriek (Profinite.padicIntegersRingObj ℓ E.1) ℓ F.d :=
  haveI := isIso_boundedConstructibleLowerShriekBaseChange_padicIntegers ℓ E.1 F.isPullback
  asIso (boundedConstructibleLowerShriekBaseChange_padicIntegers ℓ E.1 F.isPullback)

/-- The supported restriction `Lι^* Rc^! P ⟶ Rd^! LΔ^* P` with `𝒪_E`-coefficients: the mate
`Rc^! ⋙ Lι^* ⟶ LΔ^* ⋙ Rd^!` of the inverse of compact-support base change in the fixed square. -/
noncomputable def supportedRestrictionIntegral
    (P : Dᵇc((X ⨯ X).left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    (boundedConstructibleUpperStar _ ℓ F.ι).obj
        ((boundedConstructibleUpperShriek _ ℓ c.support).obj P) ⟶
      (boundedConstructibleUpperShriek _ ℓ F.d).obj
        ((boundedConstructibleUpperStar _ ℓ (diag X)).obj P) :=
  (CategoryTheory.mateEquiv (boundedConstructibleUpperShriekAdjunction _ ℓ c.support)
    (boundedConstructibleUpperShriekAdjunction _ ℓ F.d)
    (TwoSquare.mk _ _ _ _ (F.lowerShriekBaseChangeIsoIntegral E).inv)).natTrans.app P

/-- **The supported restriction under `𝒪_E ⟶ E`**: the extension of scalars `T` of the
`𝒪_E`-supported restriction of `P`, followed by the `f^!`-exchange for `d` and the pullback
comparison for `Δ`, is the pullback comparison for `ι`, then `Lι^*` of the `f^!`-exchange for `c`,
then the `E`-supported restriction of `T P`. -/
theorem map_supportedRestrictionIntegral_comp
    (P : Dᵇc((X ⨯ X).left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    (boundedConstructibleExtendScalars F.F.left ℓ E).map (F.supportedRestrictionIntegral E P) ≫
        (boundedConstructibleUpperShriekExtendScalars ℓ E F.d).app _ ≫
        (boundedConstructibleUpperShriek _ ℓ F.d).map
          ((boundedConstructibleUpperStarExtendScalarsIso ℓ E (diag X)).hom.app P) =
      (boundedConstructibleUpperStarExtendScalarsIso ℓ E F.ι).hom.app _ ≫
        (boundedConstructibleUpperStar _ ℓ F.ι).map
          ((boundedConstructibleUpperShriekExtendScalars ℓ E c.support).app P) ≫
        F.supportedRestrictionE E ((boundedConstructibleExtendScalars (X ⨯ X).left ℓ E).obj P) := by
  have h := Adjunction.map_mateEquiv_app_comp
    (boundedConstructibleUpperShriekAdjunction _ ℓ c.support)
    (boundedConstructibleUpperShriekAdjunction _ ℓ F.d)
    (boundedConstructibleUpperStar _ ℓ F.ι) (boundedConstructibleUpperStar _ ℓ (diag X))
    (F.lowerShriekBaseChangeIsoIntegral E)
    (boundedConstructibleUpperShriekAdjunction (Profinite.continuousMapRingObj E) ℓ c.support)
    (boundedConstructibleUpperShriekAdjunction (Profinite.continuousMapRingObj E) ℓ F.d)
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ F.ι)
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (diag X))
    (F.lowerShriekBaseChangeIsoE E)
    (boundedConstructibleExtendScalars (X ⨯ X).left ℓ E)
    (boundedConstructibleExtendScalars c.C.left ℓ E)
    (boundedConstructibleExtendScalars F.F.left ℓ E)
    (boundedConstructibleExtendScalars X.left ℓ E)
    (boundedConstructibleLowerShriekExtendScalarsIso ℓ E c.support)
    (boundedConstructibleLowerShriekExtendScalarsIso ℓ E F.d)
    (boundedConstructibleUpperStarExtendScalarsIso ℓ E F.ι)
    (boundedConstructibleUpperStarExtendScalarsIso ℓ E (diag X))
    (boundedConstructibleLowerShriekBaseChange_extendScalars ℓ E F.isPullback) P
  simp only [supportedRestrictionIntegral, supportedRestrictionE,
    boundedConstructibleUpperShriekExtendScalars_eq_mateEquiv]
  dsimp only [Functor.comp_obj] at h ⊢
  with_reducible exact h

/-- **Transport of the vanishing of the supported restriction from `𝒪_E` to `E`**: if the stalk
along `z : T ⟶ Fix(c)` of the extension of scalars to `E` of the `𝒪_E`-supported restriction of
`P` vanishes, so does the stalk of the `E`-supported restriction of `E ⊗ P`. This uses the `f^!`
clause of blueprint `sk-prop-scalar-six` (`isIso_boundedConstructibleUpperShriekExtendScalars`)
for the support `c`. -/
theorem upperStar_map_supportedRestrictionE_eq_zero_of_supportedRestrictionIntegral
    {T : Over (Spec (.of k))} [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [IsSeparated T.hom] (z : T ⟶ F.F)
    (P : Dᵇc((X ⨯ X).left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)
    (h : (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ z).map
      ((boundedConstructibleExtendScalars F.F.left ℓ E).map
        (F.supportedRestrictionIntegral E P)) = 0) :
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ z).map
      (F.supportedRestrictionE E ((boundedConstructibleExtendScalars (X ⨯ X).left ℓ E).obj P)) =
        0 := by
  have := isIso_boundedConstructibleUpperShriekExtendScalars ℓ E c.support
  have h1 := congrArg (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ z).map
    (F.map_supportedRestrictionIntegral_comp E P)
  simp only [Functor.map_comp, h, Limits.zero_comp] at h1
  exact (Preadditive.IsIso.comp_left_eq_zero _ _).1
    ((Preadditive.IsIso.comp_left_eq_zero _ _).1 h1.symm)

end Correspondence.FixedLocus

end AlgebraicGeometry.ProEtale.CondensedRing
