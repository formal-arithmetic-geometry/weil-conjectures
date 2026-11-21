/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralUpperShriekCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibility
public import WeilConjectures.TraceFormula.ExternalProductExtendScalars
public import WeilConjectures.TraceFormula.GraphPieces
public import WeilConjectures.TraceFormula.IntegralCompactPullback
public import WeilConjectures.TraceFormula.RationalModel

/-!

# Frobenius operators under the extension of scalars `𝒪_E ⟶ ℚ̄_ℓ`

DOC

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : PadicAlgCl.FiniteIntermediateField ℓ)

-- The coefficient ring `𝒪_E`.
set_option quotPrecheck false in
local notation "𝒪" => Profinite.padicIntegersRingObj ℓ E.1

-- The coefficient ring `ℚ̄_ℓ`.
set_option quotPrecheck false in
local notation "ℚ̄" => Profinite.padicAlgClRingObj ℓ

section Comparison

variable {X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- **(Pull)** for `𝒪_E ⟶ ℚ̄_ℓ` at an object: `T_X (Lf^* K) ≅ Lf^* (T_Y K)`. -/
noncomputable def upperStarIntegersToPadicAlgClObjIso (f : X ⟶ Y)
    (K : Dᵇc(Y.left)⟦𝒪⟧) :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj
        ((boundedConstructibleUpperStar 𝒪 ℓ f).obj K) ≅
      (boundedConstructibleUpperStar ℚ̄ ℓ f).obj
        ((boundedConstructibleIntegersToPadicAlgCl ℓ E Y).obj K) :=
  (boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E f).app K

/-- **(Shriek)** for `𝒪_E ⟶ ℚ̄_ℓ`: `Rf_!^{𝒪_E} ⋙ T_Y ≅ T_X ⋙ Rf_!^{ℚ̄_ℓ}`, the comparison for
`𝒪_E ⟶ E` followed by the one for `E ⟶ ℚ̄_ℓ`. -/
noncomputable def boundedConstructibleLowerShriekIntegersToPadicAlgClIso (f : X ⟶ Y) :
    PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E.1 f ⋙
        boundedConstructibleIntegersToPadicAlgCl ℓ E Y ≅
      boundedConstructibleIntegersToPadicAlgCl ℓ E X ⋙ boundedConstructibleLowerShriek ℓ f :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (boundedConstructibleLowerShriekExtendScalarsIso ℓ E f)
      (constructibleToPadicAlgCl Y.left ℓ E) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (boundedConstructibleExtendScalars X.left ℓ E)
      (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E f) ≪≫
    (Functor.associator _ _ _).symm

/-- **(Shriek)** for `𝒪_E ⟶ ℚ̄_ℓ` at an object: `T_Y (Rf_! K) ≅ Rf_! (T_X K)`. -/
noncomputable def lowerShriekIntegersToPadicAlgClObjIso (f : X ⟶ Y)
    (K : Dᵇc(X.left)⟦𝒪⟧) :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E Y).obj
        ((PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E.1 f).obj K) ≅
      (boundedConstructibleLowerShriek ℓ f).obj
        ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K) :=
  (boundedConstructibleLowerShriekIntegersToPadicAlgClIso E f).app K

theorem upperStarIntegersToPadicAlgClObjIso_hom_id
    (K : Dᵇc(X.left)⟦𝒪⟧) :
    (upperStarIntegersToPadicAlgClObjIso E (𝟙 X) K).hom ≫
        (boundedConstructibleUpperStarId ℚ̄ ℓ X).hom.app
          ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K) =
      (boundedConstructibleIntegersToPadicAlgCl ℓ E X).map
        ((boundedConstructibleUpperStarId 𝒪 ℓ X).hom.app K) := by
  sorry

theorem upperStarIntegersToPadicAlgClObjIso_hom_comp (f : X ⟶ Y)
    (g : Y ⟶ Z) (K : Dᵇc(Z.left)⟦𝒪⟧) :
    (upperStarIntegersToPadicAlgClObjIso E (f ≫ g) K).hom ≫
        (boundedConstructibleUpperStarComp ℚ̄ ℓ f g).hom.app
          ((boundedConstructibleIntegersToPadicAlgCl ℓ E Z).obj K) =
      (boundedConstructibleIntegersToPadicAlgCl ℓ E X).map
          ((boundedConstructibleUpperStarComp 𝒪 ℓ f g).hom.app K) ≫
        (upperStarIntegersToPadicAlgClObjIso E f
          ((boundedConstructibleUpperStar 𝒪 ℓ g).obj K)).hom ≫
        (boundedConstructibleUpperStar ℚ̄ ℓ f).map
          (upperStarIntegersToPadicAlgClObjIso E g K).hom := by
  sorry

lemma upperStarIntegersToPadicAlgClObjIso_hom_eqToHom {f g : X ⟶ Y}
    (e : f = g) (K : Dᵇc(Y.left)⟦𝒪⟧) :
    (upperStarIntegersToPadicAlgClObjIso E f K).hom ≫ eqToHom (by rw [e]) =
      (boundedConstructibleIntegersToPadicAlgCl ℓ E X).map (eqToHom (by rw [e])) ≫
        (upperStarIntegersToPadicAlgClObjIso E g K).hom := by
  subst e
  simp

lemma upperStarIntegersToPadicAlgClObjIso_hom_naturality (f : X ⟶ Y)
    {K L : Dᵇc(Y.left)⟦𝒪⟧} (a : K ⟶ L) :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E X).map
        ((boundedConstructibleUpperStar 𝒪 ℓ f).map a) ≫
        (upperStarIntegersToPadicAlgClObjIso E f L).hom =
      (upperStarIntegersToPadicAlgClObjIso E f K).hom ≫
        (boundedConstructibleUpperStar ℚ̄ ℓ f).map
          ((boundedConstructibleIntegersToPadicAlgCl ℓ E Y).map a) :=
  (boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E f).hom.naturality a

lemma lowerShriekIntegersToPadicAlgClObjIso_hom_naturality (f : X ⟶ Y)
    {K L : Dᵇc(X.left)⟦𝒪⟧} (a : K ⟶ L) :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E Y).map
        ((PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E.1 f).map a) ≫
        (lowerShriekIntegersToPadicAlgClObjIso E f L).hom =
      (lowerShriekIntegersToPadicAlgClObjIso E f K).hom ≫
        (boundedConstructibleLowerShriek ℓ f).map
          ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).map a) :=
  (boundedConstructibleLowerShriekIntegersToPadicAlgClIso E f).hom.naturality a

theorem map_compactPullback_app_integersToPadicAlgCl (h : Y ⟶ X) [IsProper h.left]
    (K : Dᵇc(X.left)⟦𝒪⟧) :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E (point k)).map
          ((PadicIntegersRingObj.compactPullback ℓ E.1 h).app K) ≫
        (lowerShriekIntegersToPadicAlgClObjIso E (toPoint Y)
          ((boundedConstructibleUpperStar 𝒪 ℓ h).obj K)).hom ≫
        (boundedConstructibleLowerShriek ℓ (toPoint Y)).map
          (upperStarIntegersToPadicAlgClObjIso E h K).hom =
      (lowerShriekIntegersToPadicAlgClObjIso E (toPoint X) K).hom ≫
        (compactPullback ℓ h).app ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K) := by
  sorry

lemma upperStarIntegersToPadicAlgClObjIso_hom_comp_assoc (f : X ⟶ Y)
    (g : Y ⟶ Z) (K : Dᵇc(Z.left)⟦𝒪⟧) {W : Dᵇc(X.left)⟦ℚ̄⟧}
    (q : (boundedConstructibleUpperStar ℚ̄ ℓ f).obj
      ((boundedConstructibleUpperStar ℚ̄ ℓ g).obj
        ((boundedConstructibleIntegersToPadicAlgCl ℓ E Z).obj K)) ⟶ W) :
    (upperStarIntegersToPadicAlgClObjIso E (f ≫ g) K).hom ≫
        (boundedConstructibleUpperStarComp ℚ̄ ℓ f g).hom.app
          ((boundedConstructibleIntegersToPadicAlgCl ℓ E Z).obj K) ≫ q =
      (boundedConstructibleIntegersToPadicAlgCl ℓ E X).map
          ((boundedConstructibleUpperStarComp 𝒪 ℓ f g).hom.app K) ≫
        (upperStarIntegersToPadicAlgClObjIso E f
          ((boundedConstructibleUpperStar 𝒪 ℓ g).obj K)).hom ≫
        (boundedConstructibleUpperStar ℚ̄ ℓ f).map
          (upperStarIntegersToPadicAlgClObjIso E g K).hom ≫ q := by
  simp only [← Category.assoc, upperStarIntegersToPadicAlgClObjIso_hom_comp]

lemma upperStarIntegersToPadicAlgClObjIso_hom_eqToHom_assoc {f g : X ⟶ Y}
    (e : f = g) (K : Dᵇc(Y.left)⟦𝒪⟧)
    {W : Dᵇc(X.left)⟦ℚ̄⟧}
    (q : (boundedConstructibleUpperStar ℚ̄ ℓ g).obj
        ((boundedConstructibleIntegersToPadicAlgCl ℓ E Y).obj K) ⟶ W) :
    (upperStarIntegersToPadicAlgClObjIso E f K).hom ≫ eqToHom (by rw [e]) ≫ q =
      (boundedConstructibleIntegersToPadicAlgCl ℓ E X).map (eqToHom (by rw [e])) ≫
        (upperStarIntegersToPadicAlgClObjIso E g K).hom ≫ q := by
  subst e
  simp

lemma map_compactPullback_app_integersToPadicAlgCl_assoc (h : Y ⟶ X) [IsProper h.left]
    (K : Dᵇc(X.left)⟦𝒪⟧)
    {W : Dᵇc((point k).left)⟦ℚ̄⟧}
    (q : (boundedConstructibleLowerShriek ℓ (toPoint Y)).obj
      ((boundedConstructibleUpperStar ℚ̄ ℓ h).obj
        ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K)) ⟶ W) :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E (point k)).map
          ((PadicIntegersRingObj.compactPullback ℓ E.1 h).app K) ≫
        (lowerShriekIntegersToPadicAlgClObjIso E (toPoint Y)
          ((boundedConstructibleUpperStar 𝒪 ℓ h).obj K)).hom ≫
        (boundedConstructibleLowerShriek ℓ (toPoint Y)).map
          (upperStarIntegersToPadicAlgClObjIso E h K).hom ≫ q =
      (lowerShriekIntegersToPadicAlgClObjIso E (toPoint X) K).hom ≫
        (compactPullback ℓ h).app ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K) ≫ q := by
  simp only [← Category.assoc]
  rw [← map_compactPullback_app_integersToPadicAlgCl]
  simp only [Category.assoc]

end Comparison

section Frobenius

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] {Φ : X ⟶ X}

noncomputable def frobeniusCoefficientIntegersToPadicAlgCl
    {K : Dᵇc(X.left)⟦𝒪⟧}
    (θ : (boundedConstructibleUpperStar 𝒪 ℓ Φ).obj K ⟶ K) :
    (boundedConstructibleUpperStar ℚ̄ ℓ Φ).obj
        ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K) ⟶
      (boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K :=
  (upperStarIntegersToPadicAlgClObjIso E Φ K).inv ≫
    (boundedConstructibleIntegersToPadicAlgCl ℓ E X).map θ

lemma map_eqToHom_comp_upperStarId_integersToPadicAlgCl {u : X ⟶ X} (e : u = 𝟙 X)
    (K : Dᵇc(X.left)⟦𝒪⟧) :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E X).map
        (eqToHom (by rw [e]) ≫
          (boundedConstructibleUpperStarId 𝒪 ℓ X).hom.app K) =
      (upperStarIntegersToPadicAlgClObjIso E u K).hom ≫ eqToHom (by rw [e]) ≫
          (boundedConstructibleUpperStarId ℚ̄ ℓ X).hom.app
            ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K) := by
  subst e
  simp only [eqToHom_refl, Category.id_comp]
  exact (upperStarIntegersToPadicAlgClObjIso_hom_id E K).symm

lemma map_frobeniusCoefficientIterate_integersToPadicAlgCl_step {u v : X ⟶ X} (e : u = Φ ≫ v)
    {K : Dᵇc(X.left)⟦𝒪⟧}
    (θ : (boundedConstructibleUpperStar 𝒪 ℓ Φ).obj K ⟶ K)
    (θv : (boundedConstructibleUpperStar 𝒪 ℓ v).obj K ⟶ K)
    (ψv : (boundedConstructibleUpperStar ℚ̄ ℓ v).obj
        ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K) ⟶
      (boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K)
    (h : (boundedConstructibleIntegersToPadicAlgCl ℓ E X).map θv =
      (upperStarIntegersToPadicAlgClObjIso E v K).hom ≫ ψv) :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E X).map
        (eqToHom (by rw [e]) ≫
          (boundedConstructibleUpperStarComp 𝒪 ℓ Φ v).hom.app K ≫
          (boundedConstructibleUpperStar 𝒪 ℓ Φ).map θv ≫ θ) =
      (upperStarIntegersToPadicAlgClObjIso E u K).hom ≫ eqToHom (by rw [e]) ≫
        (boundedConstructibleUpperStarComp ℚ̄ ℓ Φ v).hom.app
          ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K) ≫
        (boundedConstructibleUpperStar ℚ̄ ℓ Φ).map ψv ≫
        frobeniusCoefficientIntegersToPadicAlgCl E θ := by
  subst e
  simp only [eqToHom_refl, Category.id_comp]
  unfold frobeniusCoefficientIntegersToPadicAlgCl
  have hn := upperStarIntegersToPadicAlgClObjIso_hom_naturality E Φ θv
  rw [h, Functor.map_comp] at hn
  conv_rhs => rw [← Category.assoc]
  rw [upperStarIntegersToPadicAlgClObjIso_hom_comp]
  simp only [Category.assoc, Functor.map_comp, ← reassoc_of% hn, Iso.hom_inv_id_assoc]
  rfl

theorem map_frobeniusCoefficientIterate_integersToPadicAlgCl
    {K : Dᵇc(X.left)⟦𝒪⟧}
    (θ : (boundedConstructibleUpperStar 𝒪 ℓ Φ).obj K ⟶ K)
    (m : ℕ) :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E X).map (frobeniusCoefficientIterate θ m) =
      (upperStarIntegersToPadicAlgClObjIso E (frobeniusIterate Φ m) K).hom ≫
        frobeniusCoefficientIterate (frobeniusCoefficientIntegersToPadicAlgCl E θ) m := by
  induction m with
  | zero =>
    rw [frobeniusCoefficientIterate_zero, frobeniusCoefficientIterate_zero]
    simp only [upperStarIterateZeroIso, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
      eqToHom_app]
    exact map_eqToHom_comp_upperStarId_integersToPadicAlgCl E (frobeniusIterate_zero Φ) K
  | succ m ih =>
    rw [frobeniusCoefficientIterate_succ_eq, frobeniusCoefficientIterate_succ_eq]
    simp only [upperStarIterateSuccIso, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
      eqToHom_app, Category.assoc]
    exact map_frobeniusCoefficientIterate_integersToPadicAlgCl_step E (frobeniusIterate_succ Φ m)
      θ _ _ ih

theorem map_frobeniusCompactOperator_integersToPadicAlgCl [IsProper Φ.left]
    {K : Dᵇc(X.left)⟦𝒪⟧}
    (θ : (boundedConstructibleUpperStar 𝒪 ℓ Φ).obj K ⟶ K)
    (m : ℕ) :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E (point k)).map
          (PadicIntegersRingObj.frobeniusCompactOperator θ m) ≫
        (lowerShriekIntegersToPadicAlgClObjIso E (toPoint X) K).hom =
      (lowerShriekIntegersToPadicAlgClObjIso E (toPoint X) K).hom ≫
        frobeniusCompactOperator ℓ (frobeniusCoefficientIntegersToPadicAlgCl E θ) m := by
  unfold PadicIntegersRingObj.frobeniusCompactOperator frobeniusCompactOperator
  simp only [Functor.map_comp, Category.assoc, lowerShriekIntegersToPadicAlgClObjIso_hom_naturality,
    map_frobeniusCoefficientIterate_integersToPadicAlgCl,
    map_compactPullback_app_integersToPadicAlgCl_assoc]

theorem map_graphStalkMap_integersToPadicAlgCl
    (K : Dᵇc(X.left)⟦𝒪⟧) (h : X ⟶ X)
    (v : (boundedConstructibleUpperStar 𝒪 ℓ h).obj K ⟶ K)
    (x : RationalPoint X) (hx : x ≫ h = x) :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E (point k)).map
          (PadicIntegersRingObj.graphStalkMap K h v x hx) ≫
        (upperStarIntegersToPadicAlgClObjIso E x K).hom =
      (upperStarIntegersToPadicAlgClObjIso E x K).hom ≫
        Correspondence.graphStalkMap ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K) h
          ((upperStarIntegersToPadicAlgClObjIso E h K).inv ≫
            (boundedConstructibleIntegersToPadicAlgCl ℓ E X).map v) x hx := by
  unfold PadicIntegersRingObj.graphStalkMap Correspondence.graphStalkMap
  simp only [upperStarIntegersToPadicAlgClObjIso_hom_eqToHom_assoc E hx.symm K,
    upperStarIntegersToPadicAlgClObjIso_hom_comp_assoc, Functor.map_comp,
    Category.assoc, Iso.hom_inv_id_map_assoc, upperStarIntegersToPadicAlgClObjIso_hom_naturality]

end Frobenius

end AlgebraicGeometry.ProEtale.CondensedRing
