/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.Paper.ContinuousIntegralLocalization
import all Sheaf.Paper.ContinuousIntegralScalarExact

/-! # The regular coefficient localization telescope -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

omit [Fact ℓ.Prime] in
/-- Transport a scalar telescope colimit and its specified zeroth leg through an
additive functor and coefficient isomorphisms.
Source: universal properties of colimits and natural isomorphisms.
(blueprint: lem-weil-pbc-integral-regular-telescope).
Proof. Reindex the mapped cocone by the natural isomorphism with constant component
`er.hom`; its inverse changes the zeroth leg by `er.inv`. The given leg equation
then cancels `er.inv` with `er.hom`. -/
theorem transportRegularTelescope
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B]
    (F : A ⥤ B) [F.Additive] {M : A}
    (c : Cocone (integralLocalizationSequence ℓ M))
    (hc : IsColimit (F.mapCocone c)) {N P : B}
    (er : F.obj M ≅ N) (es : F.obj c.pt ≅ P)
    (V : B ⥤ C) (φ : V.obj N ⟶ V.obj P)
    (hz : V.map (F.map (c.ι.app 0) ≫ es.hom) = V.map er.hom ≫ φ) :
    ∃ c' : Cocone (integralLocalizationSequence ℓ N),
      Nonempty (IsColimit c') ∧ ∃ e : c'.pt ≅ P,
        V.map (c'.ι.app 0 ≫ e.hom) = φ := by
  let α : integralLocalizationSequence ℓ M ⋙ F ⟶ integralLocalizationSequence ℓ N :=
    NatTrans.ofSequence (fun _ ↦ er.hom) (by
      intro n
      simp only [integralLocalizationSequence, Functor.comp_map,
        Functor.ofSequence_map_homOfLE_succ]
      change F.map (ℓ • 𝟙 M) ≫ er.hom = er.hom ≫ (ℓ • 𝟙 N)
      rw [F.map_nsmul, F.map_id]
      simp)
  have : ∀ n, IsIso (α.app n) := fun n ↦ by
    change IsIso er.hom
    infer_instance
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let c' := (Cocone.precompose (asIso α).inv).obj (F.mapCocone c)
  refine ⟨c', ⟨(IsColimit.precomposeHomEquiv (asIso α).symm _).symm hc⟩, es, ?_⟩
  have hi : (asIso α).inv.app 0 = er.inv := by
    apply (cancel_mono er.hom).1
    change (asIso α).inv.app 0 ≫ (asIso α).hom.app 0 = er.inv ≫ er.hom
    simp; rfl
  change V.map (((asIso α).inv.app 0 ≫ F.map (c.ι.app 0)) ≫ es.hom) = φ
  rw [hi, Category.assoc, V.map_comp, hz, ← Category.assoc,
    ← V.map_comp, er.inv_hom_id]
  change V.map (𝟙 N) ≫ φ = φ
  rw [V.map_id, Category.id_comp]

/-- The regular restricted E-module is the scalar telescope of the regular integral
module; the zeroth leg is the coefficient inclusion.
Source: Bhatt--Scholze, Lemma 6.8.2, compact-test localization.
(blueprint: lem-weil-pbc-integral-regular-telescope).
Proof. On every compact profinite test, divide by ℓⁿ. Compactness supplies one
common denominator, and injectivity gives the colimit equivalence relation.
Monoidal sheafification and inverse image from the point preserve the resulting
module colimit. Their coefficient isomorphisms identify the zeroth leg with the
original coefficient inclusion. -/
theorem integralRegularTelescope (X : Scheme.{u}) :
    ∃ c : Cocone (integralLocalizationSequence ℓ (Mod.regular
        (condensedRingObj (integralCoeff ℓ E) X))),
      Nonempty (IsColimit c) ∧
      ∃ e : c.pt ≅ (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (coefficientMap (integralScalarMap ℓ E) X)).obj
          (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E) X)),
        (c.ι.app 0 ≫ e.hom).hom = coefficientMap (integralScalarMap ℓ E) X := by
  let := Functor.functorCategoryMonoidalClosed Profinite.{u}ᵒᵖ Ab.{u + 1}
  have : (upperStarFromPoint X).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint
  let L := schemeCoefficientFunctor X
  let R := coefficientPresheaf.{u} (continuousIntegers ℓ E)
  let S := coefficientPresheaf.{u} E
  let A := condensedRingObj (integralCoeff ℓ E) X
  let B := condensedRingObj (Profinite.continuousMapRingObj E) X
  let a := schemeCoefficientIso X (continuousIntegers ℓ E)
  let b := schemeCoefficientIso X E
  let φ := integralPresheafMap.{u} ℓ E
  let ψ := coefficientMap (integralScalarMap ℓ E) X
  have : IsMonHom a.hom := by
    change @IsMonHom _ _ _ _ _ (L.monObjObj R) _ a.hom
    rw [Functor.monObjObj_comp]
    exact Functor.map.instIsMonHom (F := upperStarFromPoint X) _ _
      (pointCoefficientIso (continuousIntegers ℓ E)).hom
  have : IsMonHom a.inv := by infer_instance
  have : IsMonHom b.hom := by
    change @IsMonHom _ _ _ _ _ (L.monObjObj S) _ b.hom
    rw [Functor.monObjObj_comp]
    exact Functor.map.instIsMonHom (F := upperStarFromPoint X) _ _
      (pointCoefficientIso E).hom
  let F := L.mapMod R ⋙ Mod.comap a.inv
  have : L.Additive := by
    exact rightExactFunctor_le_additiveFunctor _ _ _ (by
      rw [rightExactFunctor_iff]
      infer_instance)
  have : (L.mapMod R).Additive := ⟨fun {M N f g} ↦
    Mod.hom_ext _ _ (L.map_add (f := f.hom) (g := g.hom))⟩
  have : PreservesColimitsOfShape ℕ (L.mapMod R) := by
    have : PreservesColimitsOfShape ℕ
        (L.mapMod R ⋙ Mod.forget (L.obj R)) :=
      inferInstanceAs (PreservesColimitsOfShape ℕ (Mod.forget R ⋙ L))
    exact preservesColimitsOfShape_of_reflects_of_preserves _ (Mod.forget (L.obj R))
  let er : F.obj (Mod.regular R) ≅ Mod.regular A :=
    (Mod.comap a.inv).mapIso (mappedRegularIso L R) ≪≫
      restrictedRegularIso a.inv (𝟙 A) a (by exact a.inv_hom_id) ≪≫ (Mod.comapId A).app _
  let es : F.obj ((Mod.comap φ).obj (Mod.regular S)) ≅
      (Mod.comap ψ).obj (Mod.regular B) :=
    (Mod.comap a.inv).mapIso
      ((L.mapModComapIso φ).app (Mod.regular S) ≪≫
        (Mod.comap (L.map φ)).mapIso (mappedRegularIso L S)) ≪≫
      (Mod.comapComp a.inv (L.map φ)).symm.app (Mod.regular (L.obj S)) ≪≫
      restrictedRegularIso (a.inv ≫ L.map φ) ψ b (by
        rw [Category.assoc, schemeCoefficientIso_naturality, Iso.inv_hom_id_assoc])
  apply transportRegularTelescope ℓ F (localizationCocone ℓ E)
    (isColimitOfPreserves F (localizationCoconeIsColimit.{u} ℓ E))
    er es (Mod.forget A) ψ
  change L.map (localizationLegHom ℓ E 0) ≫ b.hom = a.hom ≫ ψ
  have hz : localizationLegHom ℓ E 0 = φ := by
    ext T x
    apply ULift.ext
    ext t
    simp only [localizationLegHom, pow_zero, div_one]
    rfl
  rw [hz]
  exact schemeCoefficientIso_naturality ℓ E X

end AlgebraicGeometry.ProEtale.CondensedRing
