/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateVCompIsIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldUpperShriekCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek

/-!
# Compatibility of `Rf_!` and `Rf^!` with the extension of scalars along `E ≤ F`

Let `ℓ` be a prime, `E ≤ F` finite subextensions of `ℚ̄_ℓ / ℚ_ℓ`, and `k` a field of
characteristic `p ≠ ℓ`. For a separated `k`-scheme of finite type `X` write
`T_X : Dᵇc(X)⟦E⟧ ⥤ Dᵇc(X)⟦F⟧` for the extension of scalars
(`ProEtale.CondensedRing.boundedConstructibleExtendScalarsSubfield`). For a morphism
`f : X ⟶ Y` of separated `k`-schemes of finite type:

* **(Pull)** `Lf^*_E ⋙ T_X ≅ T_Y ⋙ Lf^*_F`
  (`ProEtale.CondensedRing.boundedConstructibleUpperStarExtendScalarsSubfieldIso`);
* **(Shriek)** `j_!^E ⋙ T_X ≅ T_U ⋙ j_!^F` for an open immersion `j`
  (`ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekExtendScalarsSubfieldIso`),
  and `Rf_!^E ⋙ T_Y ≅ T_X ⋙ Rf_!^F` along the chosen compactification
  (`ProEtale.CondensedRing.boundedConstructibleLowerShriekExtendScalarsSubfieldIso`);
* **the exchange for `f^!`** `Rf^!_E ⋙ T_X ⟶ T_Y ⋙ Rf^!_F`, the mate of the inverse of (Shriek)
  (`ProEtale.CondensedRing.boundedConstructibleUpperShriekExtendScalarsSubfield`), is an
  isomorphism (`ProEtale.CondensedRing.isIso_boundedConstructibleUpperShriekExtendScalarsSubfield`).

## Implementation details

Along a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`, the exchange for `f^!` is the horizontal
composite of the exchanges for the proper part `g` and for the open immersion `i`
(`CategoryTheory.mateEquiv_hcomp`). The former is an isomorphism by
`ProEtale.CondensedRing.isIso_mateEquiv_boundedConstructibleLowerStarExtendScalarsSubfield`, the
latter because `i_!` is fully faithful and `i^*` commutes with `T` by (Pull).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {E F : FiniteIntermediateField ℓ} (h : E ≤ F)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-! ### (Pull) -/

section UpperStar

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- **(Pull)** on bounded constructible complexes, for finite subextensions `E ≤ F`:
`Lf^*_E ⋙ T_X ≅ T_Y ⋙ Lf^*_F`, the restriction of `ProEtale.CondensedRing.derivedPullIso` along
the fully faithful inclusions. -/
noncomputable def boundedConstructibleUpperStarExtendScalarsSubfieldIso :
    boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ f ⋙
        boundedConstructibleExtendScalarsSubfield X.left ℓ h ≅
      boundedConstructibleExtendScalarsSubfield Y.left ℓ h ⋙
        boundedConstructibleUpperStar (Profinite.continuousMapRingObj F) ℓ f :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (boundedConstructibleExtendScalarsSubfieldCompatibility X.left ℓ h) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleUpperStarCompatibility _ ℓ f) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (derivedPullIso (Profinite.padicSubfieldRingObjMap ℓ h) f.left) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (boundedConstructibleExtendScalarsSubfieldCompatibility Y.left ℓ h).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleUpperStarCompatibility _ ℓ f).symm ≪≫
      (Functor.associator _ _ _).symm)

end UpperStar

/-! ### (Shriek) for an open immersion -/

section OpenImmersion

variable {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- **(Shriek)** on bounded constructible complexes, for finite subextensions `E ≤ F` and an open
immersion `j`: `j_!^E ⋙ T_X ≅ T_U ⋙ j_!^F`, the restriction of
`ProEtale.CondensedRing.derivedOpenImmersionShriekIso`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekExtendScalarsSubfieldIso :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ j ⋙
        boundedConstructibleExtendScalarsSubfield X.left ℓ h ≅
      boundedConstructibleExtendScalarsSubfield U.left ℓ h ⋙
        boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj F) ℓ j :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (boundedConstructibleExtendScalarsSubfieldCompatibility X.left ℓ h) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ j) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (derivedOpenImmersionShriekIso (Profinite.padicSubfieldRingObjMap ℓ h) j.left) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (boundedConstructibleExtendScalarsSubfieldCompatibility U.left ℓ h).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ j).symm ≪≫
      (Functor.associator _ _ _).symm)

/-- The exchange `j^*_E ⋙ T_U ⟶ T_X ⋙ j^*_F` for an open immersion `j`: the mate of the inverse
of (Shriek) under the adjunctions `j_! ⊣ j^*`. -/
noncomputable def boundedConstructibleOpenImmersionUpperStarExtendScalarsSubfield :
    boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ j ⋙
        boundedConstructibleExtendScalarsSubfield U.left ℓ h ⟶
      boundedConstructibleExtendScalarsSubfield X.left ℓ h ⋙
        boundedConstructibleUpperStar (Profinite.continuousMapRingObj F) ℓ j :=
  mateEquiv (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
    (boundedConstructibleOpenImmersionLowerShriekExtendScalarsSubfieldIso ℓ h j).inv

/-- The exchange for an open immersion `j` is an isomorphism: `j_!` is fully faithful on both
sides, and `j^*` commutes with the extension of scalars by (Pull). -/
instance isIso_boundedConstructibleOpenImmersionUpperStarExtendScalarsSubfield :
    IsIso (boundedConstructibleOpenImmersionUpperStarExtendScalarsSubfield ℓ h j) :=
  isIso_mateEquiv_of_isIso_unit _ _ _
    (boundedConstructibleUpperStarExtendScalarsSubfieldIso ℓ h j).symm

end OpenImmersion

/-! ### (Shriek) and the exchange for `f^!` -/

section Shriek

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

section OfCompactification

variable {f : X ⟶ Y} (c : Compactification f.left)

/-- **(Shriek)** on bounded constructible complexes along a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, for finite subextensions `E ≤ F`:
`Rf_!(c)^E ⋙ T_Y ≅ T_X ⋙ Rf_!(c)^F`, composed of (Shriek) for the open immersion `i` and (Push)
for the proper `g`. -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationExtendScalarsSubfieldIso :
    ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactification ℓ E c ⋙
        boundedConstructibleExtendScalarsSubfield Y.left ℓ h ≅
      boundedConstructibleExtendScalarsSubfield X.left ℓ h ⋙
        ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactification ℓ F c :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (asIso (boundedConstructibleLowerStarExtendScalarsSubfield ℓ h c.overG)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekExtendScalarsSubfieldIso ℓ h c.overI) _ ≪≫
    Functor.associator _ _ _

/-- The inverse of (Shriek) along a compactification is the vertical composite of the inverses of
(Shriek) for the open immersion and of (Push) for the proper part. -/
lemma boundedConstructibleLowerShriekOfCompactificationExtendScalarsSubfieldIso_inv :
    (boundedConstructibleLowerShriekOfCompactificationExtendScalarsSubfieldIso ℓ h c).inv =
      TwoSquare.vComp
        (boundedConstructibleOpenImmersionLowerShriekExtendScalarsSubfieldIso ℓ h c.overI).inv
        (inv (boundedConstructibleLowerStarExtendScalarsSubfield ℓ h c.overG)) := by
  ext K
  simp [boundedConstructibleLowerShriekOfCompactificationExtendScalarsSubfieldIso,
    TwoSquare.vComp]

/-- The exchange `Rg^!_E ⋙ T_Z ⟶ T_Y ⋙ Rg^!_F` for the proper part `g` of a compactification: the
mate of the inverse of (Push) under the adjunctions `Rg_* ⊣ Rg^!`. -/
noncomputable def boundedConstructibleProperUpperShriekExtendScalarsSubfield :
    (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E c.overG).rightAdjoint ⋙
        boundedConstructibleExtendScalarsSubfield c.overObj.left ℓ h ⟶
      boundedConstructibleExtendScalarsSubfield Y.left ℓ h ⋙
        (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ F c.overG).rightAdjoint :=
  mateEquiv (Adjunction.ofIsLeftAdjoint _) (Adjunction.ofIsLeftAdjoint _)
    (TwoSquare.mk (boundedConstructibleExtendScalarsSubfield c.overObj.left ℓ h)
      (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E c.overG)
      (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ F c.overG)
      (boundedConstructibleExtendScalarsSubfield Y.left ℓ h)
      (inv (boundedConstructibleLowerStarExtendScalarsSubfield ℓ h c.overG)))

/-- The exchange for the proper part of a compactification is an isomorphism. -/
instance isIso_boundedConstructibleProperUpperShriekExtendScalarsSubfield :
    IsIso (boundedConstructibleProperUpperShriekExtendScalarsSubfield ℓ h c) :=
  isIso_mateEquiv_boundedConstructibleLowerStarExtendScalarsSubfield ℓ h c.overG

/-- The exchange `Rf^!(c)_E ⋙ T_X ⟶ T_Y ⋙ Rf^!(c)_F` along a compactification `c`: the mate of
the inverse of (Shriek) under the adjunctions `Rf_!(c) ⊣ Rf^!(c)`. -/
noncomputable def boundedConstructibleUpperShriekOfCompactificationExtendScalarsSubfield :
    ContinuousMapRingObj.boundedConstructibleUpperShriekOfCompactification ℓ E c ⋙
        boundedConstructibleExtendScalarsSubfield X.left ℓ h ⟶
      boundedConstructibleExtendScalarsSubfield Y.left ℓ h ⋙
        ContinuousMapRingObj.boundedConstructibleUpperShriekOfCompactification ℓ F c :=
  mateEquiv
    (ContinuousMapRingObj.boundedConstructibleUpperShriekOfCompactificationAdjunction ℓ E c)
    (ContinuousMapRingObj.boundedConstructibleUpperShriekOfCompactificationAdjunction ℓ F c)
    (boundedConstructibleLowerShriekOfCompactificationExtendScalarsSubfieldIso ℓ h c).inv

/-- `CategoryTheory.mateEquiv_hcomp` for composite adjunctions, functors and a square given by
name, each identified with the composite one by its own equality, so that none of these
identifications unfolds an adjunction. -/
private lemma mateEquiv_heq_hComp_of_heq
    {A₁ A₂ A₃ B₁ B₂ B₃ : Type*} [Category A₁] [Category A₂] [Category A₃] [Category B₁]
    [Category B₂] [Category B₃] {G : A₁ ⥤ B₁} {H : A₂ ⥤ B₂} {K : A₃ ⥤ B₃}
    {L₁ : A₁ ⥤ A₂} {R₁ : A₂ ⥤ A₁} {L₂ : B₁ ⥤ B₂} {R₂ : B₂ ⥤ B₁}
    {L₃ : A₂ ⥤ A₃} {R₃ : A₃ ⥤ A₂} {L₄ : B₂ ⥤ B₃} {R₄ : B₃ ⥤ B₂}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄)
    (α : TwoSquare G L₁ L₂ H) (β : TwoSquare H L₃ L₄ K)
    {L₁₃ : A₁ ⥤ A₃} {R₃₁ : A₃ ⥤ A₁} {L₂₄ : B₁ ⥤ B₃} {R₄₂ : B₃ ⥤ B₁}
    (adj₁₃ : L₁₃ ⊣ R₃₁) (adj₂₄ : L₂₄ ⊣ R₄₂) (γ : TwoSquare G L₁₃ L₂₄ K)
    (hL₁₃ : L₁₃ = L₁ ⋙ L₃) (hR₃₁ : R₃₁ = R₃ ⋙ R₁) (hL₂₄ : L₂₄ = L₂ ⋙ L₄)
    (hR₄₂ : R₄₂ = R₄ ⋙ R₂) (hadj₁₃ : HEq adj₁₃ (adj₁.comp adj₃))
    (hadj₂₄ : HEq adj₂₄ (adj₂.comp adj₄)) (hγ : HEq γ (TwoSquare.vComp α β)) :
    HEq (mateEquiv adj₁₃ adj₂₄ γ)
      (TwoSquare.hComp (mateEquiv adj₃ adj₄ β) (mateEquiv adj₁ adj₂ α)) := by
  subst hL₁₃ hR₃₁ hL₂₄ hR₄₂
  obtain rfl := eq_of_heq hadj₁₃
  obtain rfl := eq_of_heq hadj₂₄
  obtain rfl := eq_of_heq hγ
  exact heq_of_eq (mateEquiv_hcomp adj₁ adj₂ adj₃ adj₄ α β)

/-- The exchange for `f^!` along a compactification `c = (X ⟶[i] Z ⟶[g] Y)` is the horizontal
composite of the exchange for the proper part `g` and of the exchange for the open immersion
`i`. -/
lemma boundedConstructibleUpperShriekOfCompactificationExtendScalarsSubfield_eq :
    boundedConstructibleUpperShriekOfCompactificationExtendScalarsSubfield ℓ h c =
      TwoSquare.hComp (boundedConstructibleProperUpperShriekExtendScalarsSubfield ℓ h c)
        (boundedConstructibleOpenImmersionUpperStarExtendScalarsSubfield ℓ h c.overI) := by
  have h' := boundedConstructibleLowerShriekOfCompactificationExtendScalarsSubfieldIso_inv ℓ h c
  unfold boundedConstructibleUpperShriekOfCompactificationExtendScalarsSubfield
  exact eq_of_heq (mateEquiv_heq_hComp_of_heq
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.continuousMapRingObj E) ℓ c.overI)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.continuousMapRingObj F) ℓ c.overI)
    (Adjunction.ofIsLeftAdjoint (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E c.overG))
    (Adjunction.ofIsLeftAdjoint (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ F c.overG))
    (boundedConstructibleOpenImmersionLowerShriekExtendScalarsSubfieldIso ℓ h c.overI).inv
    (inv (boundedConstructibleLowerStarExtendScalarsSubfield ℓ h c.overG))
    (ContinuousMapRingObj.boundedConstructibleUpperShriekOfCompactificationAdjunction ℓ E c)
    (ContinuousMapRingObj.boundedConstructibleUpperShriekOfCompactificationAdjunction ℓ F c)
    (boundedConstructibleLowerShriekOfCompactificationExtendScalarsSubfieldIso ℓ h c).inv
    rfl rfl rfl rfl (HEq.refl _) (HEq.refl _) (heq_of_eq h'))

/-- The exchange for `f^!` along a compactification `c` is an isomorphism. -/
instance isIso_boundedConstructibleUpperShriekOfCompactificationExtendScalarsSubfield :
    IsIso (boundedConstructibleUpperShriekOfCompactificationExtendScalarsSubfield ℓ h c) := by
  rw [boundedConstructibleUpperShriekOfCompactificationExtendScalarsSubfield_eq]
  exact TwoSquare.isIso_hComp _ _

end OfCompactification

variable (f : X ⟶ Y)

/-- **(Shriek)** on bounded constructible complexes, for finite subextensions `E ≤ F`:
`Rf_!^E ⋙ T_Y ≅ T_X ⋙ Rf_!^F`, along the chosen compactification. -/
noncomputable def boundedConstructibleLowerShriekExtendScalarsSubfieldIso :
    ContinuousMapRingObj.boundedConstructibleLowerShriek ℓ E f ⋙
        boundedConstructibleExtendScalarsSubfield Y.left ℓ h ≅
      boundedConstructibleExtendScalarsSubfield X.left ℓ h ⋙
        ContinuousMapRingObj.boundedConstructibleLowerShriek ℓ F f :=
  boundedConstructibleLowerShriekOfCompactificationExtendScalarsSubfieldIso ℓ h
    (compactificationOverField f)

/-- **The exchange for `f^!`**, for finite subextensions `E ≤ F`: the canonical natural
transformation `Rf^!_E ⋙ T_X ⟶ T_Y ⋙ Rf^!_F`, the mate of the inverse of (Shriek)
(`boundedConstructibleLowerShriekExtendScalarsSubfieldIso`) under the adjunctions `Rf_! ⊣ Rf^!`. -/
noncomputable def boundedConstructibleUpperShriekExtendScalarsSubfield :
    ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ E f ⋙
        boundedConstructibleExtendScalarsSubfield X.left ℓ h ⟶
      boundedConstructibleExtendScalarsSubfield Y.left ℓ h ⋙
        ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ F f :=
  mateEquiv (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
    (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ F f)
    (boundedConstructibleLowerShriekExtendScalarsSubfieldIso ℓ h f).inv

/-- **The exchange for `f^!` is an isomorphism** for finite subextensions `E ≤ F`: the
comparison `Rf^!_E ⋙ T_X ⟶ T_Y ⋙ Rf^!_F` is an isomorphism on bounded constructible
complexes. -/
theorem isIso_boundedConstructibleUpperShriekExtendScalarsSubfield :
    IsIso (boundedConstructibleUpperShriekExtendScalarsSubfield ℓ h f) :=
  isIso_boundedConstructibleUpperShriekOfCompactificationExtendScalarsSubfield ℓ h _

end Shriek

end AlgebraicGeometry.ProEtale.CondensedRing
