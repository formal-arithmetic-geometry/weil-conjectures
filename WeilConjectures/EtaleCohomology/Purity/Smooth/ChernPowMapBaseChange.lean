/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ChernPowMapNaturality
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerGenerator
public import WeilConjectures.SixFunctors.BaseChange.EtaleDerived
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedPlus

/-!
# Base change of the map of the projective bundle formula

For a commutative square `g' ≫ f = f' ≫ g`, the pullback along `g` of the component
`chernPowMap f h a : Λ(-a)[-2a] ⟶ Rf_* Λ` of the map of the projective bundle formula is, through
the derived base change map `Lg^* Rf_* ⟶ Rf'_* Lg'^*`, the component
`chernPowMap f' (g'^* h) a` (`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_chernPowMap`). For
a cartesian square with `g` étale, for instance an open immersion, the base change map is an
isomorphism, so the projective bundle formula for `f` restricts to the one for `f'`
(`AlgebraicGeometry.Etale.isIso_leftDerivedUpperStar_map_projectiveFormulaMap_iff`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Etale

variable (Λ : Type (u + 1)) [CommRing Λ]
  {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- For a cartesian square `g' ≫ f = f' ≫ g` with `g` étale, the derived base change map
`Lg^* Rf_* Λ ⟶ Rf'_* Lg'^* Λ` at the constant complex is an isomorphism. -/
lemma isIso_derivedBaseChangeMap_app_constantComplex_of_etale (sq : IsPullback g' f' f g)
    [Etale g] :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app (constantComplex Λ X)) := by
  have := Etale.isIso_derivedBaseChangeMapPlus_of_etale Λ sq
  rw [NatTrans.isIso_app_iff_of_iso _ (constantComplexIsoSingleFunctor Λ X)]
  exact (isIso_derivedBaseChangeMap_app_ι_obj_iff _ sq.toCommSq
    ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj _)).2 inferInstance

end Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasKummerClass Λ]

/-- The adjoint of the projective bundle map for a composite `c = e ≫ s` is that for `e`, through
`Lc^* ≅ Le^* Ls^*` and `Ls^* Λ(-a)[-2a] ≅ Λ(-a)[-2a]`. -/
lemma chernPowAdj_comp {P S' S : Scheme.{u}} [HasInvertibleExponent Λ P]
    [HasInvertibleExponent Λ S'] [HasInvertibleExponent Λ S] (e : P ⟶ S') (s : S' ⟶ S)
    (c : P ⟶ S) (hc : c = e ≫ s) (h : constantComplex Λ P ⟶ (tateObject Λ P 1)⟦2 * (1 : ℤ)⟧)
    (a : ℕ) :
    chernPowAdj c h a = (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) e s c hc).hom.app _ ≫
      (L((e)^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateShiftIso Λ s (-(a : ℤ))).hom ≫
      chernPowAdj e h a := by
  rw [chernPowAdj, chernPowAdj, leftDerivedUpperStarTateShiftIso_comp Λ e s c hc]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]

section BaseChange

variable {X' X Y' Y : Scheme.{u}} [HasInvertibleExponent Λ X'] [HasInvertibleExponent Λ X]
  [HasInvertibleExponent Λ Y'] [HasInvertibleExponent Λ Y]
  {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- **Base change of the projective bundle map**: for a commutative square `g' ≫ f = f' ≫ g`,
the pullback along `g` of `chernPowMap f h a : Λ(-a)[-2a] ⟶ Rf_* Λ`, followed by the derived base
change map `Lg^* Rf_* Λ ⟶ Rf'_* Lg'^* Λ ≅ Rf'_* Λ`, is `chernPowMap f' (g'^* h) a`. -/
theorem leftDerivedUpperStar_map_chernPowMap (sq : CommSq g' f' f g)
    (h : constantComplex Λ X ⟶ (tateObject Λ X 1)⟦2 * (1 : ℤ)⟧) (a : ℕ) :
    (L((g)^*[ModuleCat.{u + 1} Λ])).map (chernPowMap f h a) ≫
        (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app (constantComplex Λ X) ≫
        (R((f')_*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ g').hom =
      (leftDerivedUpperStarTateShiftIso Λ g (-(a : ℤ))).hom ≫
        chernPowMap f' (VectorBundle.classRestriction Λ (r := 1) g' h) a := by
  rw [chernPowMap_eq_homEquiv, reassoc_of% (derivedBaseChangeMap_app_homEquiv Λ sq),
    ← Adjunction.homEquiv_naturality_right, chernPowMap_eq_homEquiv,
    ← Adjunction.homEquiv_naturality_left]
  congr 1
  simp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc]
  rw [leftDerivedUpperStar_map_chernPowAdj g' f (g' ≫ f) rfl,
    chernPowAdj_comp f' g (g' ≫ f) sq.w, Iso.inv_hom_id_app_assoc]

/-- **Base change of the map of the projective bundle formula**
(`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_chernPowMap`), through
`Lg^* (⊕ₐ Λ(-a)[-2a]) ≅ ⊕ₐ Lg^* Λ(-a)[-2a]`. -/
theorem mapBiproduct_inv_comp_leftDerivedUpperStar_map_projectiveFormulaMap
    (sq : CommSq g' f' f g) (h : constantComplex Λ X ⟶ (tateObject Λ X 1)⟦2 * (1 : ℤ)⟧)
    (r : ℕ) :
    ((L((g)^*[ModuleCat.{u + 1} Λ])).mapBiproduct _).inv ≫
        (L((g)^*[ModuleCat.{u + 1} Λ])).map (projectiveFormulaMap f h r) ≫
        (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app (constantComplex Λ X) ≫
        (R((f')_*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ g').hom =
      biproduct.map
          (fun a : Fin (r + 1) ↦ (leftDerivedUpperStarTateShiftIso Λ g (-(a : ℤ))).hom) ≫
        projectiveFormulaMap f' (VectorBundle.classRestriction Λ (r := 1) g' h) r := by
  rw [projectiveFormulaMap, ← Category.assoc, biproduct.mapBiproduct_inv_map_desc]
  refine biproduct.hom_ext' _ _ fun a ↦ ?_
  simp only [biproduct.ι_desc_assoc, biproduct.ι_map_assoc, projectiveFormulaMap,
    biproduct.ι_desc]
  exact leftDerivedUpperStar_map_chernPowMap sq h a

/-- **The projective bundle formula restricts along étale maps of the base**: for a cartesian
square `g' ≫ f = f' ≫ g` with `g` étale, the pullback along `g` of the map
`(1, h, …, hʳ) : ⊕ₐ Λ(-a)[-2a] ⟶ Rf_* Λ` is an isomorphism if and only if the map for `f'` and
`g'^* h` is one. -/
theorem isIso_leftDerivedUpperStar_map_projectiveFormulaMap_iff (sq : IsPullback g' f' f g)
    [Etale g] (h : constantComplex Λ X ⟶ (tateObject Λ X 1)⟦2 * (1 : ℤ)⟧) (r : ℕ) :
    IsIso ((L((g)^*[ModuleCat.{u + 1} Λ])).map (projectiveFormulaMap f h r)) ↔
      IsIso (projectiveFormulaMap f' (VectorBundle.classRestriction Λ (r := 1) g' h) r) := by
  have := isIso_derivedBaseChangeMap_app_constantComplex_of_etale Λ sq
  have hb : IsIso (biproduct.map
      (fun a : Fin (r + 1) ↦ (leftDerivedUpperStarTateShiftIso Λ g (-(a : ℤ))).hom)) :=
    (biproduct.mapIso fun a : Fin (r + 1) ↦
      leftDerivedUpperStarTateShiftIso Λ g (-(a : ℤ))).isIso_hom
  have e := mapBiproduct_inv_comp_leftDerivedUpperStar_map_projectiveFormulaMap sq.toCommSq h r
  constructor
  · intro
    rw [← isIso_comp_left_iff (biproduct.map
      fun a : Fin (r + 1) ↦ (leftDerivedUpperStarTateShiftIso Λ g (-(a : ℤ))).hom), ← e]
    infer_instance
  · intro
    rw [← isIso_comp_left_iff ((L((g)^*[ModuleCat.{u + 1} Λ])).mapBiproduct _).inv,
      ← isIso_comp_right_iff _ ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        (constantComplex Λ X) ≫ (R((f')_*[ModuleCat.{u + 1} Λ])).map
          (leftDerivedUpperStarConstantComplexIso Λ g').hom), Category.assoc, e]
    infer_instance

end BaseChange

end Etale

end AlgebraicGeometry
