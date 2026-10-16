/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module
public import Sheaf.Paper.ContinuousIntegralCoefficients
import all Sheaf.Paper.ContinuousIntegralScalarExact
/-! # The integral coefficient localization telescope on a scheme -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonObj Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
private instance schemeCoefficientIso_isMonHom (X : Scheme.{u})
    (T : Type) [TopologicalSpace T] [Ring T] [IsTopologicalRing T] :
    IsMonHom (schemeCoefficientIso X T).hom := by
  rw [Functor.monObjObj_comp]
  exact Functor.map.instIsMonHom (F := upperStarFromPoint X) _ _ (pointCoefficientIso T).hom

private instance schemeCoefficientFunctor_additive (X : Scheme.{u}) :
    (schemeCoefficientFunctor X).Additive := by
  have : (upperStarFromPoint X).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint
  exact rightExactFunctor_le_additiveFunctor _ _ _ (by
    rw [rightExactFunctor_iff]
    infer_instance)

private instance schemeCoefficientFunctor_mapMod_additive (X : Scheme.{u}) :
    ((schemeCoefficientFunctor X).mapMod
      (coefficientPresheaf.{u} (continuousIntegers ℓ E))).Additive :=
  ⟨fun {_M _N f g} ↦ Mod.hom_ext _ _
    ((schemeCoefficientFunctor X).map_add (f := f.hom) (g := g.hom))⟩

private noncomputable def coeffSchemeSequence (X : Scheme.{u}) :=
  let L := schemeCoefficientFunctor X
  let R := coefficientPresheaf.{u} (continuousIntegers ℓ E)
  let a := schemeCoefficientIso X (continuousIntegers ℓ E)
  localizationSequence ℓ E ⋙ L.mapMod R ⋙ Mod.comap a.inv
private noncomputable def coeffSchemeCocone (X : Scheme.{u}) :
    Cocone (coeffSchemeSequence ℓ E X) :=
  let L := schemeCoefficientFunctor X
  let R := coefficientPresheaf.{u} (continuousIntegers ℓ E)
  let a := schemeCoefficientIso X (continuousIntegers ℓ E)
  (L.mapMod R ⋙ Mod.comap a.inv).mapCocone (localizationCocone ℓ E)
private theorem coeffScheme_isColimit (X : Scheme.{u}) :
    Nonempty (IsColimit (coeffSchemeCocone ℓ E X)) := by
  let := Functor.functorCategoryMonoidalClosed Profinite.{u}ᵒᵖ Ab.{u + 1}
  have : (upperStarFromPoint X).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint
  let L := schemeCoefficientFunctor X
  let R := coefficientPresheaf.{u} (continuousIntegers ℓ E)
  let a := schemeCoefficientIso X (continuousIntegers ℓ E)
  have : IsMonHom a.hom := by
    change @IsMonHom _ _ _ _ _ (L.monObjObj R) _ a.hom
    rw [Functor.monObjObj_comp]
    exact Functor.map.instIsMonHom (F := upperStarFromPoint X) _ _
      (pointCoefficientIso (continuousIntegers ℓ E)).hom
  have : IsMonHom a.inv := by infer_instance
  have : L.Additive := by
    exact rightExactFunctor_le_additiveFunctor _ _ _ (by
      rw [rightExactFunctor_iff]
      infer_instance)
  have : (L.mapMod R).Additive := ⟨fun {M N f g} ↦
    Mod.hom_ext _ _ (L.map_add (f := f.hom) (g := g.hom))⟩
  have : PreservesColimitsOfShape ℕ (L.mapMod R) := by
    have : PreservesColimitsOfShape ℕ (L.mapMod R ⋙ Mod.forget (L.obj R)) :=
      inferInstanceAs (PreservesColimitsOfShape ℕ (Mod.forget R ⋙ L))
    exact preservesColimitsOfShape_of_reflects_of_preserves _ (Mod.forget (L.obj R))
  exact ⟨isColimitOfPreserves (L.mapMod R ⋙ Mod.comap a.inv)
    (localizationCoconeIsColimit.{u} ℓ E)⟩
private noncomputable def coeffSchemeStageIso (X : Scheme.{u}) (n : ℕ) :
    (coeffSchemeSequence ℓ E X).obj n ≅
      Mod.regular (condensedRingObj (integralCoeff ℓ E) X) :=
  let L := schemeCoefficientFunctor X
  let R := coefficientPresheaf.{u} (continuousIntegers ℓ E)
  let A := condensedRingObj (integralCoeff ℓ E) X
  let a := schemeCoefficientIso X (continuousIntegers ℓ E)
  (Mod.comap a.inv).mapIso (mappedRegularIso L R) ≪≫
    restrictedRegularIso a.inv (𝟙 A) a (by exact a.inv_hom_id) ≪≫ (Mod.comapId A).app _

private noncomputable def coeffSchemePointIso (X : Scheme.{u}) :
    (coeffSchemeCocone ℓ E X).pt ≅
      (Mod.comap (coefficientMap (integralScalarMap ℓ E) X)).obj
        (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E) X)) :=
  let L := schemeCoefficientFunctor X
  let S := coefficientPresheaf.{u} E
  let a := schemeCoefficientIso X (continuousIntegers ℓ E)
  let b := schemeCoefficientIso X E
  let φ := integralPresheafMap.{u} ℓ E
  let ψ := coefficientMap (integralScalarMap ℓ E) X
  (Mod.comap a.inv).mapIso
    ((L.mapModComapIso φ).app (Mod.regular S) ≪≫
      (Mod.comap (L.map φ)).mapIso (mappedRegularIso L S)) ≪≫
    (Mod.comapComp a.inv (L.map φ)).symm.app (Mod.regular (L.obj S)) ≪≫
    restrictedRegularIso (a.inv ≫ L.map φ) ψ b (by
      rw [Category.assoc, schemeCoefficientIso_naturality, Iso.inv_hom_id_assoc])

private theorem coeffScheme_leg_zero (X : Scheme.{u}) :
    ((coeffSchemeStageIso ℓ E X 0).inv ≫
      (coeffSchemeCocone ℓ E X).ι.app 0 ≫ (coeffSchemePointIso ℓ E X).hom).hom =
      coefficientMap (integralScalarMap ℓ E) X := by
  dsimp only [coeffSchemeStageIso, coeffSchemePointIso, coeffSchemeCocone]
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_inv,
    Mod.comp_hom', Mod.comap_map_hom, Iso.app_inv, Iso.app_hom,
    Mod.comapId_inv_app_hom, Mod.comapComp_inv_app_hom, Iso.symm_hom,
    mappedRegularIso, restrictedRegularIso, Mod.isoMk_hom_hom, Mod.isoMk_inv_hom,
    Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.assoc,
    Functor.mapModComapIso_hom_app_hom]
  erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp]
  change (schemeCoefficientIso X (continuousIntegers ℓ E)).inv ≫
      (schemeCoefficientFunctor X).map (localizationLegHom ℓ E 0) ≫
        (schemeCoefficientIso X E).hom = _
  have hzero : localizationLegHom.{u} ℓ E 0 = integralPresheafMap ℓ E := by
    ext S x
    apply ULift.ext
    ext y
    simp [localizationLegHom, integralPresheafMap,
      Profinite.continuousMapRingPresheafMap]
    rfl
  rw [hzero, schemeCoefficientIso_naturality, Iso.inv_hom_id_assoc]

private theorem coeffScheme_leg_pow (X : Scheme.{u}) (n : ℕ) :
    ℓ ^ n • (coeffSchemeCocone ℓ E X).ι.app n =
      (coeffSchemeCocone ℓ E X).ι.app 0 := by
  have hs₀ (k : ℕ) : ℓ • (localizationCocone.{u} ℓ E).ι.app (k + 1) =
      (localizationCocone ℓ E).ι.app k := by
    apply Mod.hom_ext
    ext S x
    apply ULift.ext
    ext s
    change (ℓ • ((x.down s : E) / (ℓ : E) ^ (k + 1))) =
      (x.down s : E) / (ℓ : E) ^ k
    rw [nsmul_eq_mul, pow_succ]
    field_simp [ell_ne_zero ℓ E]
  have hs (k : ℕ) : ℓ • (coeffSchemeCocone ℓ E X).ι.app (k + 1) =
      (coeffSchemeCocone ℓ E X).ι.app k := by
    let F := (schemeCoefficientFunctor X).mapMod
      (coefficientPresheaf.{u} (continuousIntegers ℓ E)) ⋙
        Mod.comap (schemeCoefficientIso X (continuousIntegers ℓ E)).inv
    change ℓ • F.map ((localizationCocone ℓ E).ι.app (k + 1)) =
      F.map ((localizationCocone ℓ E).ι.app k)
    rw [← CategoryTheory.Functor.map_nsmul, hs₀]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_smul, hs, ih]

/-- The restricted rational coefficient module is the localization telescope of the
regular integral module, with stage `n` dividing the canonical inclusion by `ℓ ^ n`.
Source: Bhatt--Scholze, Section 6.8 and Proposition 6.8.14(2).
(blueprint: lem-weil-pbc-continuous-integral-coefficient-telescope)

Proof. On profinite tests the maps are `a ↦ a / ℓ ^ n`. The compact-test localization
lemma supplies a common denominator for every continuous rational section and shows
that this is a colimit. Sheafification and pullback from the profinite point preserve
this colimit. The standard coefficient isomorphisms identify its stages with the
regular integral module and its point with the restricted rational regular module.
At stage zero naturality of these coefficient isomorphisms gives the canonical
coefficient inclusion. Multiplication by `ℓ ^ n` takes the nth leg to the zeroth leg,
first on continuous functions and then after applying the coefficient functor. -/
theorem integralCoefficient_localization_telescope (X : Scheme.{u}) :
    ∃ (D : ℕ ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X)) (c : Cocone D)
      (e : ∀ n, D.obj n ≅ Mod.regular (condensedRingObj (integralCoeff ℓ E) X))
      (p : c.pt ≅ (Mod.comap (coefficientMap (integralScalarMap ℓ E) X)).obj
        (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E) X))),
      Nonempty (IsColimit c) ∧
      (∀ n : ℕ, ℓ ^ n • ((e n).inv ≫ c.ι.app n) = (e 0).inv ≫ c.ι.app 0) ∧
      (((e 0).inv ≫ c.ι.app 0 ≫ p.hom).hom =
        coefficientMap (integralScalarMap ℓ E) X) := by
  refine ⟨coeffSchemeSequence ℓ E X, coeffSchemeCocone ℓ E X,
    coeffSchemeStageIso ℓ E X, coeffSchemePointIso ℓ E X,
    coeffScheme_isColimit ℓ E X, ?_, coeffScheme_leg_zero ℓ E X⟩
  intro n
  rw [← Preadditive.comp_nsmul, coeffScheme_leg_pow]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
