/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionOrientation
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionUpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeComposition
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeProper
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.CompUnit
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit

/-!
# The canonical identification `Ψ ω_f ≅ ω'_f` and the orientation under reduction

Let `ρ : Λ →+* Λ'` be a surjective morphism of finite coefficient rings with principal kernel and
`Ψ` the derived extension of scalars. For `f : X ⟶ Y` admitting a compactification, over a
quasi-compact `Y`, such that `Ψ` commutes with `Rf_!` (the comparison
`AlgebraicGeometry.Etale.derivedExtendScalarsLowerShriekMap` is an isomorphism), the comparison
`c_f : Ψ Rf^! ⟶ Rf^! Ψ` (`AlgebraicGeometry.Etale.derivedExtendScalarsRightDerivedUpperShriekMap`)
at the unit, followed by an identification `Ψ Λ_Y ≅ Λ'_Y`, is a canonical comparison
`Ψ ω_f ⟶ ω'_f` of the dualizing complexes
(`AlgebraicGeometry.Etale.derivedExtendScalarsDualizingComplexMap`).

For a closed immersion `i`, `Ψ` commutes with `Ri_!` and `c_i` is the comparison
`AlgebraicGeometry.Etale.derivedExtendScalarsUpperShriekMap` used by the reduction of
coefficients with supports. With these, we prove:

* `AlgebraicGeometry.Etale.map_rightDerivedUpperShriekDualizingComplexIsoOfCompEqId_hom_comp`: for
  a section `s` of `g`, the composition isomorphisms `Rs^! ω_g ≅ Λ` over `Λ` and `Λ'` correspond
  under `c_s` and the comparison of the dualizing complexes of `g`;
* `AlgebraicGeometry.Etale.map_dualizingComplexBaseChangeMap_comp`: the base change maps
  `Lg'^* ω_f ⟶ ω_{f'}` of the dualizing complexes correspond;
* `AlgebraicGeometry.Etale.derivedExtendScalarsDualizingComplexPullbackFstIso_hom_eq`: for `p₁`
  the first projection of `X ×_Y X`, the identification `Ψ ω_{p₁} ≅ ω'_{p₁}` induced by the
  comparison of `f` through smooth base change is the comparison of `p₁`;
* `AlgebraicGeometry.Etale.hε_derivedExtendScalarsDualizingComplexIso`: the hypothesis `hε` of
  `AlgebraicGeometry.Etale.map_dualizingComplexTwistShiftIso_reduction` holds for the canonical
  comparison;
* `AlgebraicGeometry.Etale.map_dualizingComplexTwistShiftIso_reduction_canonical_of_isIso`: hence
  the
  canonical orientation `ω_f ≅ Λ_X(d)[2d]` is compatible with `Ψ` through the canonical comparison
  `Ψ ω_f ≅ ω'_f`, as soon as the frame classes and the section invariant construction are.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a})

section ClosedImmersion

variable [Finite Λ] {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [CompactSpace X]

/-- **For a closed immersion `i`, the comparison `β_i : Ψ Ri_! ⟶ Ri_! Ψ` is the isomorphism
`AlgebraicGeometry.Etale.derivedExtendScalarsLowerShriekIso`.** -/
lemma derivedExtendScalarsLowerShriekMap_eq_derivedExtendScalarsLowerShriekIso_hom :
    derivedExtendScalarsLowerShriekMap hρ ha i =
      (derivedExtendScalarsLowerShriekIso hρ ha i).hom := by
  obtain ⟨d, hd⟩ :=
    exists_isZero_rightDerived_lowerStar_of_isProper_of_compactSpace Λ isAddTorsion_of_finite i
  exact derivedExtendScalarsLowerShriekMap_eq hρ ha i d hd
    (coeffCompatible_rightDerivedLowerShriekIsoRightDerivedLowerStar ρ i d hd)

/-- For a closed immersion, `Ψ` commutes with `Ri_!`. -/
instance isIso_derivedExtendScalarsLowerShriekMap_of_isClosedImmersion :
    IsIso (derivedExtendScalarsLowerShriekMap hρ ha i) := by
  rw [derivedExtendScalarsLowerShriekMap_eq_derivedExtendScalarsLowerShriekIso_hom]
  infer_instance

variable [Finite Λ']

omit [CompactSpace X] in
/-- The comparison `Ψ Ri^! ⟶ Ri^! Ψ` of a closed immersion used by the reduction of coefficients
with supports, as a mate. -/
lemma derivedExtendScalarsUpperShriekMap_eq_mateEquiv :
    derivedExtendScalarsUpperShriekMap hρ ha i =
      mateEquiv (rightDerivedUpperShriekAdjunction Λ i) (rightDerivedUpperShriekAdjunction Λ' i)
        (TwoSquare.mk _ _ _ _ (derivedExtendScalarsLowerShriekIso hρ ha i).inv) :=
  rfl

/-- **For a closed immersion `i`, the comparison `c_i : Ψ Ri^! ⟶ Ri^! Ψ` is
`AlgebraicGeometry.Etale.derivedExtendScalarsUpperShriekMap`.** -/
lemma derivedExtendScalarsRightDerivedUpperShriekMap_eq_derivedExtendScalarsUpperShriekMap :
    derivedExtendScalarsRightDerivedUpperShriekMap hρ ha i =
      derivedExtendScalarsUpperShriekMap hρ ha i := by
  have h : inv (derivedExtendScalarsLowerShriekMap hρ ha i) =
      (derivedExtendScalarsLowerShriekIso hρ ha i).inv := by
    rw [IsIso.inv_eq_of_hom_inv_id]
    rw [derivedExtendScalarsLowerShriekMap_eq_derivedExtendScalarsLowerShriekIso_hom,
      Iso.hom_inv_id]
  rw [derivedExtendScalarsUpperShriekMap_eq_mateEquiv,
    derivedExtendScalarsRightDerivedUpperShriekMap, coeffUpperMate, h]

end ClosedImmersion

section Identity

variable [Finite Λ] (X : Scheme.{u}) [CompactSpace X]

/-- `Ψ` commutes with `R(𝟙 X)_! ≅ 𝟭`. -/
instance isIso_derivedExtendScalarsLowerShriekMap_id :
    IsIso (derivedExtendScalarsLowerShriekMap hρ ha (𝟙 X)) :=
  isIso_coeffMate_of_coeffCompatible_unitors _ (coeffCompatible_rightDerivedLowerShriekIdIso ρ X)

end Identity

section Section

variable [Finite Λ] [Finite Λ']

/-- **The composition isomorphisms of a section are compatible with `Ψ`.** For a section `s` of
`g` along which `Ψ` commutes with `R_!`, the isomorphisms `Rs^! Rg^! ≅ R(𝟙)^! ≅ 𝟭` over `Λ` and
`Λ'` (conjugate to the composition isomorphism `R(𝟙)_! ≅ Rs_! ⋙ Rg_!`) correspond under `c_s` and
`c_g`, for any `φ : Ψ N ⟶ N'`. -/
theorem map_conjugateIsoEquiv_hom_app_comp_rightDerivedUpperShriekIdIso_hom_app_comp
    {V B : Scheme.{u}} (g : V ⟶ B) [HasCompactification g] (s : B ⟶ V) [HasCompactification s]
    (hs : s ≫ g = 𝟙 B) [CompactSpace V] [CompactSpace B]
    [IsIso (derivedExtendScalarsLowerShriekMap hρ ha g)]
    [IsIso (derivedExtendScalarsLowerShriekMap hρ ha s)] (N : 𝐃(B, Λ)) {N' : 𝐃(B, Λ')}
    (φ : (derivedExtendScalars hρ ha B).obj N ⟶ N') :
    (derivedExtendScalars hρ ha B).map ((conjugateIsoEquiv
          ((rightDerivedUpperShriekAdjunction Λ s).comp (rightDerivedUpperShriekAdjunction Λ g))
          (rightDerivedUpperShriekAdjunction Λ (𝟙 B))
          (rightDerivedLowerShriekCompIsoOfEq Λ s g (𝟙 B) hs)).hom.app N ≫
        (rightDerivedUpperShriekIdIso Λ B).hom.app N) ≫ φ =
      ((derivedExtendScalarsRightDerivedUpperShriekMap hρ ha s).app ((R(g)^![Λ]).obj N) ≫
        (R(s)^![Λ']).map ((derivedExtendScalarsRightDerivedUpperShriekMap hρ ha g).app N ≫
          (R(g)^![Λ']).map φ)) ≫
        (conjugateIsoEquiv ((rightDerivedUpperShriekAdjunction Λ' s).comp
          (rightDerivedUpperShriekAdjunction Λ' g)) (rightDerivedUpperShriekAdjunction Λ' (𝟙 B))
          (rightDerivedLowerShriekCompIsoOfEq Λ' s g (𝟙 B) hs)).hom.app N' ≫
        (rightDerivedUpperShriekIdIso Λ' B).hom.app N' := by
  have hc := map_conjugateIsoEquiv_comp_derivedExtendScalarsRightDerivedUpperShriekMap hρ ha s g
    (𝟙 B) hs (coeffCompatible_rightDerivedLowerShriekCompIsoOfEq ρ s g (𝟙 B) hs) N
  have hi := map_rightDerivedUpperShriekIdIso_hom_app hρ ha B
    (coeffCompatible_rightDerivedLowerShriekIdIso ρ B) N
  have n₁ := (conjugateIsoEquiv ((rightDerivedUpperShriekAdjunction Λ' s).comp
    (rightDerivedUpperShriekAdjunction Λ' g)) (rightDerivedUpperShriekAdjunction Λ' (𝟙 B))
    (rightDerivedLowerShriekCompIsoOfEq Λ' s g (𝟙 B) hs)).hom.naturality φ
  have n₂ := (rightDerivedUpperShriekIdIso Λ' B).hom.naturality φ
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at n₁ n₂
  rw [Functor.map_comp, Category.assoc, hi, Category.assoc, reassoc_of% hc, ← n₂,
    ← reassoc_of% n₁, Functor.map_comp, Category.assoc, Category.assoc]

/-- The isomorphism `Rs^! ω_g ≅ Λ_B` of a section `s` of `g`, unfolded. -/
lemma rightDerivedUpperShriekDualizingComplexIsoOfCompEqId_eq {V B : Scheme.{u}} (g : V ⟶ B)
    [HasCompactification g] (s : B ⟶ V) [HasCompactification s] (hs : s ≫ g = 𝟙 B) :
    rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ g s hs =
      (conjugateIsoEquiv ((rightDerivedUpperShriekAdjunction Λ s).comp
          (rightDerivedUpperShriekAdjunction Λ g)) (rightDerivedUpperShriekAdjunction Λ (𝟙 B))
          (rightDerivedLowerShriekCompIsoOfEq Λ s g (𝟙 B) hs)).app (constantComplex Λ B) ≪≫
        (rightDerivedUpperShriekIdIso Λ B).app (constantComplex Λ B) :=
  rfl

/-- **The composition isomorphism `Rs^! ω_g ≅ Λ_B` of a section is compatible with `Ψ`.** For a
section `s` of `g` along which `Ψ` commutes with `R_!`, and an identification
`e : Ψ Λ_B ≅ Λ'_B`, the isomorphisms `Rs^! ω_g ≅ Λ_B` over `Λ` and `Λ'`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekDualizingComplexIsoOfCompEqId`) correspond under
`c_s` and the comparison `c_g ≫ Rg^!(e)` of the dualizing complexes of `g`. -/
theorem map_rightDerivedUpperShriekDualizingComplexIsoOfCompEqId_hom_comp {V B : Scheme.{u}}
    (g : V ⟶ B) [HasCompactification g] (s : B ⟶ V) [HasCompactification s] (hs : s ≫ g = 𝟙 B)
    [CompactSpace V] [CompactSpace B] [IsIso (derivedExtendScalarsLowerShriekMap hρ ha g)]
    [IsIso (derivedExtendScalarsLowerShriekMap hρ ha s)]
    (e : (derivedExtendScalars hρ ha B).obj (constantComplex Λ B) ≅ constantComplex Λ' B) :
    (derivedExtendScalars hρ ha B).map
        (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ g s hs).hom ≫ e.hom =
      ((derivedExtendScalarsRightDerivedUpperShriekMap hρ ha s).app (dualizingComplex Λ g) ≫
        (R(s)^![Λ']).map ((derivedExtendScalarsRightDerivedUpperShriekMap hρ ha g).app
          (constantComplex Λ B) ≫ (R(g)^![Λ']).map e.hom)) ≫
        (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ' g s hs).hom := by
  rw [rightDerivedUpperShriekDualizingComplexIsoOfCompEqId_eq,
    rightDerivedUpperShriekDualizingComplexIsoOfCompEqId_eq, Iso.trans_hom, Iso.trans_hom,
    Iso.app_hom, Iso.app_hom, Iso.app_hom, Iso.app_hom]
  exact map_conjugateIsoEquiv_hom_app_comp_rightDerivedUpperShriekIdIso_hom_app_comp hρ ha g s hs
    (constantComplex Λ B) e.hom

end Section

section BaseChange

variable [Finite Λ] [Finite Λ']

/-- **The base change maps of `R^!` are compatible with `Ψ`**, in a form adapted to the base
change maps of the dualizing complexes: for `u : Lg^* N ⟶ M` and `u' : Lg^* N' ⟶ M'` related by
`φ : Ψ N ⟶ N'` and `φ' : Ψ M ⟶ M'`, the composites `Lg'^* Rf^! N ⟶ Rf'^! Lg^* N ⟶ Rf'^! M` over
`Λ` and `Λ'` correspond under `c_f ≫ Rf^!(φ)` and `c_{f'} ≫ Rf'^!(φ')`. -/
theorem map_rightDerivedUpperShriekBaseChangeMap_app_comp {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} [HasCompactification f]
    [HasCompactification f'] [QuasiCompact f'] [CompactSpace Y] [CompactSpace Y']
    [IsIso (derivedExtendScalarsLowerShriekMap hρ ha f)]
    [IsIso (derivedExtendScalarsLowerShriekMap hρ ha f')] (sq : IsPullback g' f' f g)
    (N : 𝐃(Y, Λ)) {M : 𝐃(Y', Λ)} (v : (L((g)^*[ModuleCat.{u + 1} Λ])).obj N ⟶ M) {N' : 𝐃(Y, Λ')}
    (φ : (derivedExtendScalars hρ ha Y).obj N ⟶ N') {M' : 𝐃(Y', Λ')}
    (φ' : (derivedExtendScalars hρ ha Y').obj M ⟶ M')
    (v' : (L((g)^*[ModuleCat.{u + 1} Λ'])).obj N' ⟶ M')
    (he : (derivedExtendScalars hρ ha Y').map v ≫ φ' =
      (derivedExtendScalarsPullbackMap hρ ha g).app N ≫ (L((g)^*[ModuleCat.{u + 1} Λ'])).map φ ≫
        v') :
    (derivedExtendScalars hρ ha X').map
        ((rightDerivedUpperShriekBaseChangeMap Λ sq).app N ≫ (R(f')^![Λ]).map v) ≫
        (derivedExtendScalarsRightDerivedUpperShriekMap hρ ha f').app M ≫ (R(f')^![Λ']).map φ' =
      (derivedExtendScalarsPullbackMap hρ ha g').app ((R(f)^![Λ]).obj N) ≫
        (L((g')^*[ModuleCat.{u + 1} Λ'])).map
          ((derivedExtendScalarsRightDerivedUpperShriekMap hρ ha f).app N ≫ (R(f)^![Λ']).map φ) ≫
          (rightDerivedUpperShriekBaseChangeMap Λ' sq).app N' ≫ (R(f')^![Λ']).map v' := by
  have hbc := derivedExtendScalarsRightDerivedUpperShriekMap_baseChange hρ ha sq N
  have n₁ := (derivedExtendScalarsRightDerivedUpperShriekMap hρ ha f').naturality v
  have n₂ := (rightDerivedUpperShriekBaseChangeMap Λ' sq).naturality φ
  simp only [Functor.comp_obj, Functor.comp_map] at n₁ n₂
  rw [Functor.map_comp, Category.assoc, reassoc_of% n₁, ← Functor.map_comp, he, Functor.map_comp,
    Functor.map_comp, ← reassoc_of% hbc, ← reassoc_of% n₂,
    Functor.map_comp, Category.assoc]

/-- **The base change maps of the dualizing complexes are compatible with `Ψ`.** For a cartesian
square `g' ≫ f = f' ≫ g` along whose vertical maps `Ψ` commutes with `R_!`, and identifications
`e_Y : Ψ Λ_Y ≅ Λ'_Y`, `e_{Y'} : Ψ Λ_{Y'} ≅ Λ'_{Y'}` compatible with `Lg^*`, the base change maps
`Lg'^* ω_f ⟶ ω_{f'}` (`AlgebraicGeometry.Etale.dualizingComplexBaseChangeMap`) over `Λ` and `Λ'`
correspond under the comparisons `c ≫ R^!(e)` of the dualizing complexes. -/
theorem map_dualizingComplexBaseChangeMap_comp {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} [HasCompactification f] [HasCompactification f']
    [QuasiCompact f'] [CompactSpace Y] [CompactSpace Y']
    [IsIso (derivedExtendScalarsLowerShriekMap hρ ha f)]
    [IsIso (derivedExtendScalarsLowerShriekMap hρ ha f')] (sq : IsPullback g' f' f g)
    (eY : (derivedExtendScalars hρ ha Y).obj (constantComplex Λ Y) ≅ constantComplex Λ' Y)
    (eY' : (derivedExtendScalars hρ ha Y').obj (constantComplex Λ Y') ≅ constantComplex Λ' Y')
    (he : (derivedExtendScalars hρ ha Y').map (leftDerivedUpperStarUnitIso _ g).hom ≫ eY'.hom =
      (derivedExtendScalarsPullbackMap hρ ha g).app (constantComplex Λ Y) ≫
        (L((g)^*[ModuleCat.{u + 1} Λ'])).map eY.hom ≫ (leftDerivedUpperStarUnitIso _ g).hom) :
    (derivedExtendScalars hρ ha X').map (dualizingComplexBaseChangeMap Λ sq) ≫
        (derivedExtendScalarsRightDerivedUpperShriekMap hρ ha f').app (constantComplex Λ Y') ≫
          (R(f')^![Λ']).map eY'.hom =
      (derivedExtendScalarsPullbackMap hρ ha g').app (dualizingComplex Λ f) ≫
        (L((g')^*[ModuleCat.{u + 1} Λ'])).map
          ((derivedExtendScalarsRightDerivedUpperShriekMap hρ ha f).app (constantComplex Λ Y) ≫
            (R(f)^![Λ']).map eY.hom) ≫ dualizingComplexBaseChangeMap Λ' sq :=
  map_rightDerivedUpperShriekBaseChangeMap_app_comp hρ ha sq (constantComplex Λ Y)
    (leftDerivedUpperStarUnitIso _ g).hom eY.hom eY'.hom (leftDerivedUpperStarUnitIso _ g).hom he

end BaseChange

section ConstantComplex

/-- The identification `Lf^* Λ_Y ≅ Λ_X` of the constant complexes is the identification of the
units `AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso`. -/
lemma leftDerivedUpperStarConstantComplexIso_hom_eq (Γ : Type (u + 1)) [CommRing Γ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (leftDerivedUpperStarConstantComplexIso Γ f).hom =
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Γ) f).hom := by
  have h := leftDerivedUpperStarUnitIso_hom_comp_ε (ModuleCat.{u + 1} Γ) f
  rw [leftDerivedUpperStarConstantComplexIso, asIso_hom, leftDerivedUpperStar_η_eq]
  simp only [← Category.assoc]
  rw [IsIso.comp_inv_eq, h]
  simp only [Category.assoc]
  rfl

end ConstantComplex

section Dualizing

variable [Finite Λ] [Finite Λ']

/-- **The comparison of the dualizing complexes** `Ψ ω_f ⟶ ω'_f` attached to an identification
`e : Ψ Λ_Y ≅ Λ'_Y`: the comparison `c_f : Ψ Rf^! ⟶ Rf^! Ψ`
(`AlgebraicGeometry.Etale.derivedExtendScalarsRightDerivedUpperShriekMap`) at `Λ_Y`, followed by
`Rf^!(e)`. -/
noncomputable def derivedExtendScalarsDualizingComplexMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [CompactSpace Y] [IsIso (derivedExtendScalarsLowerShriekMap hρ ha f)]
    (e : (derivedExtendScalars hρ ha Y).obj (constantComplex Λ Y) ≅ constantComplex Λ' Y) :
    (derivedExtendScalars hρ ha X).obj (dualizingComplex Λ f) ⟶ dualizingComplex Λ' f :=
  (derivedExtendScalarsRightDerivedUpperShriekMap hρ ha f).app (constantComplex Λ Y) ≫
    (R(f)^![Λ']).map e.hom

/-- The comparison of the dualizing complexes, unfolded. -/
lemma derivedExtendScalarsDualizingComplexMap_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [CompactSpace Y] [IsIso (derivedExtendScalarsLowerShriekMap hρ ha f)]
    (e : (derivedExtendScalars hρ ha Y).obj (constantComplex Λ Y) ≅ constantComplex Λ' Y) :
    derivedExtendScalarsDualizingComplexMap hρ ha f e =
      (derivedExtendScalarsRightDerivedUpperShriekMap hρ ha f).app (constantComplex Λ Y) ≫
        (R(f)^![Λ']).map e.hom :=
  rfl

/-- The comparison of the dualizing complexes is an isomorphism as soon as `c_f` is one at
`Λ_Y`. -/
instance isIso_derivedExtendScalarsDualizingComplexMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [CompactSpace Y] [IsIso (derivedExtendScalarsLowerShriekMap hρ ha f)]
    (e : (derivedExtendScalars hρ ha Y).obj (constantComplex Λ Y) ≅ constantComplex Λ' Y)
    [IsIso ((derivedExtendScalarsRightDerivedUpperShriekMap hρ ha f).app (constantComplex Λ Y))] :
    IsIso (derivedExtendScalarsDualizingComplexMap hρ ha f e) := by
  unfold derivedExtendScalarsDualizingComplexMap
  infer_instance

/-- **The canonical identification `Ψ ω_f ≅ ω'_f`**, when the comparison `c_f` is an isomorphism
at `Λ_Y` (`AlgebraicGeometry.Etale.derivedExtendScalarsDualizingComplexMap`). -/
noncomputable def derivedExtendScalarsDualizingComplexIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [CompactSpace Y] [IsIso (derivedExtendScalarsLowerShriekMap hρ ha f)]
    (e : (derivedExtendScalars hρ ha Y).obj (constantComplex Λ Y) ≅ constantComplex Λ' Y)
    [IsIso ((derivedExtendScalarsRightDerivedUpperShriekMap hρ ha f).app (constantComplex Λ Y))] :
    (derivedExtendScalars hρ ha X).obj (dualizingComplex Λ f) ≅ dualizingComplex Λ' f :=
  asIso (derivedExtendScalarsDualizingComplexMap hρ ha f e)

@[simp]
lemma derivedExtendScalarsDualizingComplexIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [CompactSpace Y] [IsIso (derivedExtendScalarsLowerShriekMap hρ ha f)]
    (e : (derivedExtendScalars hρ ha Y).obj (constantComplex Λ Y) ≅ constantComplex Λ' Y)
    [IsIso ((derivedExtendScalarsRightDerivedUpperShriekMap hρ ha f).app (constantComplex Λ Y))] :
    (derivedExtendScalarsDualizingComplexIso hρ ha f e).hom =
      derivedExtendScalarsDualizingComplexMap hρ ha f e :=
  rfl

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasInvertibleExponent Λ X]
  [HasInvertibleExponent Λ' X] [HasCompactification f] [QuasiSeparatedSpace Y] [QuasiCompact f]

/-- The identification `ω_{p₁} ≅ Lp₂^* ω_f`, unfolded. -/
lemma dualizingComplexPullbackFstIso_inv_eq (Γ : Type (u + 1)) [CommRing Γ] [Finite Γ]
    [HasInvertibleExponent Γ X] (d : ℕ) [SmoothOfRelativeDimension d f] :
    (dualizingComplexPullbackFstIso Γ f d).inv =
      dualizingComplexBaseChangeMap Γ (IsPullback.of_hasPullback f f).flip :=
  rfl

/-- The identification `Ψ ω_{p₁} ≅ ω'_{p₁}` induced by `vω`, unfolded. -/
lemma derivedExtendScalarsDualizingComplexPullbackFstIso_hom_eq_comp (d : ℕ)
    [SmoothOfRelativeDimension d f]
    (vω : (derivedExtendScalars hρ ha X).obj (dualizingComplex Λ f) ≅ dualizingComplex Λ' f) :
    (derivedExtendScalarsDualizingComplexPullbackFstIso hρ ha f d vω).hom =
      (derivedExtendScalars hρ ha (pullback f f)).map (dualizingComplexPullbackFstIso Λ f d).hom ≫
        (derivedExtendScalarsPullbackMap hρ ha (pullback.snd f f)).app _ ≫
          (L((pullback.snd f f)^*[ModuleCat.{u + 1} Λ'])).map vω.hom ≫
            (dualizingComplexPullbackFstIso Λ' f d).inv :=
  rfl

/-- **The identification `Ψ ω_{p₁} ≅ ω'_{p₁}` induced through smooth base change by the canonical
comparison of `f` is the canonical comparison of the first projection `p₁`**, for
identifications `e_X : Ψ Λ_X ≅ Λ'_X` and `e_Y : Ψ Λ_Y ≅ Λ'_Y` compatible with `Lf^*`. -/
theorem derivedExtendScalarsDualizingComplexPullbackFstIso_hom_eq (d : ℕ)
    [SmoothOfRelativeDimension d f] [CompactSpace Y] [CompactSpace X]
    [IsIso (derivedExtendScalarsLowerShriekMap hρ ha f)]
    [IsIso (derivedExtendScalarsLowerShriekMap hρ ha (pullback.fst f f))]
    (eX : (derivedExtendScalars hρ ha X).obj (constantComplex Λ X) ≅ constantComplex Λ' X)
    (eY : (derivedExtendScalars hρ ha Y).obj (constantComplex Λ Y) ≅ constantComplex Λ' Y)
    (he : (derivedExtendScalars hρ ha X).map (leftDerivedUpperStarUnitIso _ f).hom ≫ eX.hom =
      (derivedExtendScalarsPullbackMap hρ ha f).app (constantComplex Λ Y) ≫
        (L((f)^*[ModuleCat.{u + 1} Λ'])).map eY.hom ≫ (leftDerivedUpperStarUnitIso _ f).hom)
    (vω : (derivedExtendScalars hρ ha X).obj (dualizingComplex Λ f) ≅ dualizingComplex Λ' f)
    (hvω : vω.hom = derivedExtendScalarsDualizingComplexMap hρ ha f eY) :
    (derivedExtendScalarsDualizingComplexPullbackFstIso hρ ha f d vω).hom =
      derivedExtendScalarsDualizingComplexMap hρ ha (pullback.fst f f) eX := by
  have hb := map_dualizingComplexBaseChangeMap_comp hρ ha (IsPullback.of_hasPullback f f).flip
    eY eX he
  rw [derivedExtendScalarsDualizingComplexPullbackFstIso_hom_eq_comp,
    dualizingComplexPullbackFstIso_inv_eq, hvω, derivedExtendScalarsDualizingComplexMap,
    derivedExtendScalarsDualizingComplexMap, ← hb, ← Functor.map_comp_assoc,
    ← dualizingComplexPullbackFstIso_inv_eq f Λ d, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- **The hypothesis `hε` of `AlgebraicGeometry.Etale.map_dualizingComplexTwistShiftIso_reduction`
holds for the canonical comparison.** Let `vω : Ψ ω_f ≅ ω'_f` be the comparison
`c_f ≫ Rf^!(e_Y)` of the dualizing complexes, for identifications `e_X : Ψ Λ_X ≅ Λ'_X` and
`e_Y : Ψ Λ_Y ≅ Λ'_Y` compatible with `Lf^*`. Then the composition isomorphisms
`RΔ^! ω_{p₁} ≅ Λ_X` over `Λ` and `Λ'` correspond under the comparison
`AlgebraicGeometry.Etale.derivedExtendScalarsUpperShriekMap` of the diagonal and the
identification `Ψ ω_{p₁} ≅ ω'_{p₁}` induced by `vω` through smooth base change. -/
theorem map_rightDerivedUpperShriekDualizingComplexIsoOfCompEqId_diagonal_hom_comp (d : ℕ)
    [SmoothOfRelativeDimension d f] [IsSeparated f] [CompactSpace Y] [CompactSpace X]
    [IsIso (derivedExtendScalarsLowerShriekMap hρ ha f)]
    [IsIso (derivedExtendScalarsLowerShriekMap hρ ha (pullback.fst f f))]
    (eX : (derivedExtendScalars hρ ha X).obj (constantComplex Λ X) ≅ constantComplex Λ' X)
    (eY : (derivedExtendScalars hρ ha Y).obj (constantComplex Λ Y) ≅ constantComplex Λ' Y)
    (he : (derivedExtendScalars hρ ha X).map (leftDerivedUpperStarUnitIso _ f).hom ≫ eX.hom =
      (derivedExtendScalarsPullbackMap hρ ha f).app (constantComplex Λ Y) ≫
        (L((f)^*[ModuleCat.{u + 1} Λ'])).map eY.hom ≫ (leftDerivedUpperStarUnitIso _ f).hom)
    (vω : (derivedExtendScalars hρ ha X).obj (dualizingComplex Λ f) ≅ dualizingComplex Λ' f)
    (hvω : vω.hom = derivedExtendScalarsDualizingComplexMap hρ ha f eY) :
    (derivedExtendScalars hρ ha X).map (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ
          (pullback.fst f f) (pullback.diagonal f) (pullback.diagonal_fst f)).hom ≫ eX.hom =
      ((derivedExtendScalarsUpperShriekMap hρ ha (pullback.diagonal f)).app
          (dualizingComplex Λ (pullback.fst f f)) ≫
          (R(pullback.diagonal f)^![Λ']).map
            (derivedExtendScalarsDualizingComplexPullbackFstIso hρ ha f d vω).hom) ≫
        (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ' (pullback.fst f f)
          (pullback.diagonal f) (pullback.diagonal_fst f)).hom := by
  have : CompactSpace (pullback f f : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f)
  rw [derivedExtendScalarsDualizingComplexPullbackFstIso_hom_eq hρ ha f d eX eY he vω hvω,
    ← derivedExtendScalarsRightDerivedUpperShriekMap_eq_derivedExtendScalarsUpperShriekMap]
  exact map_rightDerivedUpperShriekDualizingComplexIsoOfCompEqId_hom_comp hρ ha (pullback.fst f f)
    (pullback.diagonal f) (pullback.diagonal_fst f) eX

end Dualizing

section Orientation

variable [Finite Λ] [Finite Λ'] {X Y : Scheme.{u}} (f : X ⟶ Y) [HasInvertibleExponent Λ X]
  [HasInvertibleExponent Λ' X] [HasCompactification f] [QuasiSeparatedSpace Y] [QuasiCompact f]

omit [Finite Λ] [Finite Λ'] [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X]
  [HasCompactification f] [QuasiSeparatedSpace Y] [QuasiCompact f] in
/-- The identifications `Ψ Λ ≅ Λ'`
(`AlgebraicGeometry.Etale.derivedExtendScalarsConstantComplexIso`) are compatible with the
identifications `Lf^* Λ_Y ≅ Λ_X` of the units. -/
lemma derivedExtendScalarsConstantComplexIso_hom_pullback_unit :
    (derivedExtendScalars hρ ha X).map (leftDerivedUpperStarUnitIso _ f).hom ≫
        (derivedExtendScalarsConstantComplexIso hρ ha X).hom =
      (derivedExtendScalarsPullbackMap hρ ha f).app (constantComplex Λ Y) ≫
        (L((f)^*[ModuleCat.{u + 1} Λ'])).map (derivedExtendScalarsConstantComplexIso hρ ha Y).hom ≫
          (leftDerivedUpperStarUnitIso _ f).hom := by
  have h := derivedExtendScalarsConstantComplexIso_hom_pullback hρ ha f
  rwa [leftDerivedUpperStarConstantComplexIso_hom_eq, leftDerivedUpperStarConstantComplexIso_hom_eq,
    derivedExtendScalarsPullbackIso_hom] at h

variable [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] [HasKummerClass Λ']
  [HasKummerClass.IsNormalized Λ'] (τ : DerivedExtendScalarsTateShiftData Λ Λ' hρ ha)

/-- Blueprint `thm-pur-diagonal-dualizing-object`, `det-sp-purity-coefficient-change`

**The canonical orientation `ω_f ≅ Λ_X(d)[2d]` is compatible with the reduction of coefficients
through the canonical comparison `Ψ ω_f ≅ ω'_f`.** Let `f : X ⟶ Y` be smooth separated of
relative dimension `d` over a quasi-compact `Y`, separated and locally of finite type over a
field, such that `Ψ` commutes with `Rf_!` and with `Rp₁_!` for the first projection
`p₁ : X ×_Y X ⟶ X`, and such that the comparison `c_f : Ψ Rf^! ⟶ Rf^! Ψ` is an isomorphism at
`Λ_Y`. Let `vω : Ψ ω_f ≅ ω'_f` be the canonical comparison
(`AlgebraicGeometry.Etale.derivedExtendScalarsDualizingComplexIso`). If the derived extension of
scalars carries the frame classes of the diagonal over `Λ` to those over `Λ'` (`hframe`) and
preserves the section invariant construction at the diagonal (`hL`), then
`vω ≫ θ'_f = Ψ θ_f ≫ (Ψ(Λ_X(d)[2d]) ≅ Λ'_X(d)[2d])`. The remaining hypothesis `hε` of
`AlgebraicGeometry.Etale.map_dualizingComplexTwistShiftIso_reduction` holds by
`map_rightDerivedUpperShriekDualizingComplexIsoOfCompEqId_diagonal_hom_comp`. -/
theorem map_dualizingComplexTwistShiftIso_reduction_canonical_of_isIso (d : ℕ)
    [SmoothOfRelativeDimension d f] [IsSeparated f] {k : Type u} [Field k]
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    [HasInvertibleExponent Λ (pullback f f)] [HasInvertibleExponent Λ' (pullback f f)]
    [CompactSpace Y] [CompactSpace X] [IsIso (derivedExtendScalarsLowerShriekMap hρ ha f)]
    [IsIso (derivedExtendScalarsLowerShriekMap hρ ha (pullback.fst f f))]
    [IsIso ((derivedExtendScalarsRightDerivedUpperShriekMap hρ ha f).app (constantComplex Λ Y))]
    (hframe : ∀ F : (pullback.diagonal f).EtaleFrame d, IsOpenImmersion F.e →
      (reductionSupportedCoefficientChange hρ ha τ).mapSupportedClass _
        ((reductionSupportedCoefficientChange hρ ha τ).tateShiftIso F.U d) (frameClass Λ F) =
          frameClass Λ' F)
    (hL : (reductionSupportedCoefficientChange hρ ha τ).PreservesSectionInvariantIso
      (pullback.diagonal f)) :
    (derivedExtendScalars hρ ha X).map (dualizingComplexTwistShiftIso Λ f d aY).hom ≫
        ((reductionSupportedCoefficientChange hρ ha τ).twistShiftConstantComplexIso X d).hom =
      (derivedExtendScalarsDualizingComplexIso hρ ha f
          (derivedExtendScalarsConstantComplexIso hρ ha Y)).hom ≫
        (dualizingComplexTwistShiftIso Λ' f d aY).hom :=
  map_dualizingComplexTwistShiftIso_reduction hρ ha f τ d aY _ hframe
    (map_rightDerivedUpperShriekDualizingComplexIsoOfCompEqId_diagonal_hom_comp hρ ha f d
      (derivedExtendScalarsConstantComplexIso hρ ha X)
      (derivedExtendScalarsConstantComplexIso hρ ha Y)
      (derivedExtendScalarsConstantComplexIso_hom_pullback_unit hρ ha f) _ rfl) hL

end Orientation

end Etale

end AlgebraicGeometry
