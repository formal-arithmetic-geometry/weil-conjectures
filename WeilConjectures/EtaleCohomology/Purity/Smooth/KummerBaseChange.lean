/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange

/-!
# Base change of the Kummer boundary

The Kummer boundary `∂κ(f) ∈ H²_{V(f)}(U, Λ(1))` of a global function `f` is compatible with
pullback: for `e : U' ⟶ U`, the restriction of `∂κ(f)` to `U'`, through the restriction of
supports `Le^* Ri_! Ri^! ⟶ Ri'_! Ri'^! Le^*` (`AlgebraicGeometry.Etale.supportedRestriction`),
is `∂κ(e^* f)`. This is the naturality of the Kummer class
(`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_kummerClass`) combined with the base change of
the supported localization triangle
(`AlgebraicGeometry.Etale.supportedLocalizationBoundary_baseChange`).

## Main statements

- `AlgebraicGeometry.Etale.kummerBoundary_baseChange`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Twist

variable {Λ : Type (u + 1)} [CommRing Λ] [HasTateTwist Λ]

/-- The pullback identifications of the twisting objects are compatible with composition, for
a composite given up to an equality. -/
lemma leftDerivedUpperStarTateObjectIso_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (fg : X ⟶ S) (h : fg = f ≫ g) (m : ℤ) :
    leftDerivedUpperStarTateObjectIso fg m =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f g fg h).app (tateObject Λ S m) ≪≫
        (L((f)^*[ModuleCat.{u + 1} Λ])).mapIso (leftDerivedUpperStarTateObjectIso g m) ≪≫
          leftDerivedUpperStarTateObjectIso f m := by
  subst h
  exact HasTateTwist.leftDerivedUpperStarTwistObjectIso_comp f g m

variable (Λ) in
/-- The pullback identifications of the constant complexes are compatible with composition. -/
lemma leftDerivedUpperStarConstantComplexIso_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (fg : X ⟶ S) (h : fg = f ≫ g) :
    leftDerivedUpperStarConstantComplexIso Λ fg =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f g fg h).app (constantComplex Λ S) ≪≫
        (L((f)^*[ModuleCat.{u + 1} Λ])).mapIso (leftDerivedUpperStarConstantComplexIso Λ g) ≪≫
          leftDerivedUpperStarConstantComplexIso Λ f := by
  have := leftDerivedUpperStarTateObjectIso_comp (Λ := Λ) f g fg h 0
  ext
  simp only [leftDerivedUpperStarConstantComplexIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Functor.map_comp, Category.assoc]
  change _ ≫ (leftDerivedUpperStarTateObjectIso fg 0).hom ≫ _ = _
  rw [this]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc, Iso.symm_hom]
  erw [(leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f g fg h).hom.naturality_assoc]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

variable {X Y X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The derived square isomorphism of a commutative square `g' ≫ f = f' ≫ g` is compatible with
the pullback identifications of the twisting objects. -/
lemma derivedSquareUpperStarIso_hom_app_tateObject (sq : CommSq g' f' f g) (m : ℤ) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app (tateObject Λ Y m) ≫
        (L((g')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateObjectIso f m).hom ≫
          (leftDerivedUpperStarTateObjectIso g' m).hom =
      (L((f')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateObjectIso g m).hom ≫
        (leftDerivedUpperStarTateObjectIso f' m).hom := by
  have h₁ := leftDerivedUpperStarTateObjectIso_comp (Λ := Λ) g' f (g' ≫ f) rfl m
  have h₂ := leftDerivedUpperStarTateObjectIso_comp (Λ := Λ) f' g (g' ≫ f) sq.w m
  rw [h₁] at h₂
  have h₃ := congrArg Iso.hom h₂
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at h₃
  simp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, h₃, Iso.inv_hom_id_app_assoc]

variable (Λ) in
/-- The derived square isomorphism of a commutative square `g' ≫ f = f' ≫ g` is compatible with
the pullback identifications of the constant complexes. -/
lemma derivedSquareUpperStarIso_hom_app_constantComplex (sq : CommSq g' f' f g) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app (constantComplex Λ Y) ≫
        (L((g')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ f).hom ≫
          (leftDerivedUpperStarConstantComplexIso Λ g').hom =
      (L((f')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ g).hom ≫
        (leftDerivedUpperStarConstantComplexIso Λ f').hom := by
  have h₁ := leftDerivedUpperStarConstantComplexIso_comp Λ g' f (g' ≫ f) rfl
  have h₂ := leftDerivedUpperStarConstantComplexIso_comp Λ f' g (g' ≫ f) sq.w
  rw [h₁] at h₂
  have h₃ := congrArg Iso.hom h₂
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at h₃
  simp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, h₃, Iso.inv_hom_id_app_assoc]

variable (Λ) in
/-- The constant-complex form of `derivedSquareUpperStarIso_hom_app_constantComplex`, solved
for the identification along `f'`. -/
lemma leftDerivedUpperStarConstantComplexIso_square (sq : CommSq g' f' f g) :
    (L((f')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ g).inv ≫
        (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app (constantComplex Λ Y) ≫
        (L((g')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ f).hom ≫
          (leftDerivedUpperStarConstantComplexIso Λ g').hom =
      (leftDerivedUpperStarConstantComplexIso Λ f').hom := by
  rw [derivedSquareUpperStarIso_hom_app_constantComplex, ← Functor.map_comp_assoc,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The twist form of `derivedSquareUpperStarIso_hom_app_tateObject`, solved for the inverse
identification along `f'`. -/
lemma leftDerivedUpperStarTateObjectIso_square (sq : CommSq g' f' f g) (m : ℤ) :
    (leftDerivedUpperStarTateObjectIso g' m).inv ≫
        (L((g')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateObjectIso f m).inv ≫
        (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).inv.app (tateObject Λ Y m) ≫
          (L((f')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateObjectIso g m).hom =
      (leftDerivedUpperStarTateObjectIso f' m).inv := by
  have h := derivedSquareUpperStarIso_hom_app_tateObject (Λ := Λ) sq m
  rw [← cancel_mono (leftDerivedUpperStarTateObjectIso f' m).hom, Iso.inv_hom_id,
    Category.assoc, Category.assoc, Category.assoc, ← h, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id]

end Twist

section Kummer

variable (Λ : Type (u + 1)) [CommRing Λ] [HasKummerClass Λ]

variable {U U' D D' : Scheme.{u}} {e₁ : D' ⟶ D} {j' : D' ⟶ U'} {j : D ⟶ U} {e : U' ⟶ U}

/-- The Kummer class `κ(u)` on `D ⊆ U`, read on `U` through `Lj^* Λ_U ≅ Λ_D` and
`Lj^* Λ_U(1) ≅ Λ_D(1)`, is compatible with a commutative square `e₁ ≫ j = j' ≫ e`: its pullback
along `e₁`, read through the derived square isomorphism, is the Kummer class of the pulled back
unit on `D'`. -/
lemma kummerClass_square (sq : CommSq e₁ j' j e) (u : Γ(D, ⊤)ˣ) (u' : Γ(D', ⊤)ˣ)
    (hu : Units.map e₁.appTop.hom.toMonoidHom u = u') :
    (L((j')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ e).inv ≫
        (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app (constantComplex Λ U) ≫
        (L((e₁)^*[ModuleCat.{u + 1} Λ])).map
          ((leftDerivedUpperStarConstantComplexIso Λ j).hom ≫ kummerClass Λ u ≫
            (leftDerivedUpperStarTateObjectIso j 1).inv⟦(1 : ℤ)⟧') ≫
        ((L((e₁)^*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app _ ≫
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).inv.app (tateObject Λ U 1) ≫
          (L((j')^*[ModuleCat.{u + 1} Λ])).map
            (leftDerivedUpperStarTateObjectIso e 1).hom)⟦(1 : ℤ)⟧' =
      (leftDerivedUpperStarConstantComplexIso Λ j').hom ≫ kummerClass Λ u' ≫
        (leftDerivedUpperStarTateObjectIso j' 1).inv⟦(1 : ℤ)⟧' := by
  have hκ := leftDerivedUpperStar_map_kummerClass Λ e₁ u
  rw [hu] at hκ
  have hκ' : (L((e₁)^*[ModuleCat.{u + 1} Λ])).map (kummerClass Λ u) ≫
      ((L((e₁)^*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app _ =
        (leftDerivedUpperStarConstantComplexIso Λ e₁).hom ≫ kummerClass Λ u' ≫
          (leftDerivedUpperStarTateObjectIso e₁ 1).inv⟦(1 : ℤ)⟧' := by
    rw [← cancel_mono ((leftDerivedUpperStarTateObjectIso e₁ 1).hom⟦(1 : ℤ)⟧'),
      Category.assoc, hκ, Category.assoc, Category.assoc, ← Functor.map_comp,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  erw [((L((e₁)^*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.naturality_assoc]
  rw [reassoc_of% hκ', reassoc_of% (leftDerivedUpperStarConstantComplexIso_square Λ sq)]
  simp only [Functor.comp_map, ← Functor.map_comp]
  rw [leftDerivedUpperStarTateObjectIso_square]

variable [Finite Λ]

omit [HasKummerClass Λ] in
variable [HasKummerClass Λ] in
/-- The Kummer boundary `∂κ(f)` as the adjoint `Λ_U ⟶ (Rj_* Lj^* Λ_U(1))[1]` of the Kummer class
of `f` on `U_f`, followed by the boundary of the supported localization triangle. -/
lemma kummerBoundary_eq (f : Γ(U, ⊤)) :
    kummerBoundary Λ f =
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (U.basicOpen f).ι).unit.app _ ≫
        (R(((U.basicOpen f).ι)_*[ModuleCat.{u + 1} Λ])).map
          ((leftDerivedUpperStarConstantComplexIso Λ (U.basicOpen f).ι).hom ≫
            kummerClass Λ (U.basicOpenUnit f) ≫
              (leftDerivedUpperStarTateObjectIso (U.basicOpen f).ι 1).inv⟦(1 : ℤ)⟧') ≫
        ((R(((U.basicOpen f).ι)_*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app _) ≫
      ((supportedLocalizationBoundary (ModuleCat.{u + 1} Λ) _ _
          (range_zeroLocusSubschemeι_singleton f) (tateObject Λ U 1))⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd' _ (1 : ℤ) 1 2 rfl).inv.app _) := by
  rw [kummerBoundary, Adjunction.homEquiv_unit]
  simp only [Category.assoc]

set_option maxHeartbeats 1600000 in
-- the composites of derived functors between the derived categories of the two bases are large
-- and their instance arguments are expensive to unify
/-- **Base change of the Kummer boundary.** For `e : U' ⟶ U` and a global function `f` on `U`, the
restriction of `∂κ(f) ∈ H²_{V(f)}(U, Λ(1))` to `U'` — the pullback `Le^* ∂κ(f)` read through
`Λ_{U'} ≅ Le^* Λ_U`, the shift compatibility of `Le^*` and the restriction of supports
`Le^* Ri_! Ri^! Λ_U(1) ⟶ Ri'_! Ri'^! Λ_{U'}(1)` (`AlgebraicGeometry.Etale.supportedRestriction`)
— is `∂κ(e^* f)`. This is the step "the Kummer class is compatible with the pullback" of the
proof of `prop-pur-affine-line-orientation-base-change`: the naturality of the Kummer class
(`AlgebraicGeometry.Etale.kummerClass_square`) combined with the base change of the supported
localization triangle (`AlgebraicGeometry.Etale.supportedLocalizationBoundary_baseChange`). -/
theorem kummerBoundary_baseChange (e : U' ⟶ U) (f : Γ(U, ⊤))
    (g : U'.zeroLocusSubscheme {e.appTop f} ⟶ U.zeroLocusSubscheme {f})
    (hg : IsPullback g (U'.zeroLocusSubschemeι {e.appTop f}) (U.zeroLocusSubschemeι {f}) e) :
    (leftDerivedUpperStarConstantComplexIso Λ e).inv ≫
        (L((e)^*[ModuleCat.{u + 1} Λ])).map (kummerBoundary Λ f) ≫
        ((L((e)^*[ModuleCat.{u + 1} Λ])).commShiftIso (2 : ℤ)).hom.app _ ≫
        (supportedRestriction (ModuleCat.{u + 1} Λ) e _ _ g hg _ _
          (leftDerivedUpperStarTateObjectIso e 1))⟦(2 : ℤ)⟧' =
      kummerBoundary Λ (e.appTop f) := by
  let e₁ : (U'.basicOpen (e.appTop f) : Scheme.{u}) ⟶ U.basicOpen f :=
    e.resLE _ _ (Scheme.preimage_basicOpen_top e f).ge
  have sq : CommSq e₁ (U'.basicOpen (e.appTop f)).ι (U.basicOpen f).ι e :=
    ⟨Scheme.Hom.resLE_comp_ι _ _⟩
  have hu : Units.map e₁.appTop.hom.toMonoidHom (U.basicOpenUnit f) =
      U'.basicOpenUnit (e.appTop f) := by
    ext
    simp only [Units.coe_map, Scheme.basicOpenUnit, IsUnit.unit_spec]
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← sq.w, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply]
    rfl
  have hG1 := supportedLocalizationBoundary_baseChange (ModuleCat.{u + 1} Λ) e
    (U.zeroLocusSubschemeι {f}) (U.basicOpen f).ι (U'.zeroLocusSubschemeι {e.appTop f})
    (U'.basicOpen (e.appTop f)).ι g e₁ (range_zeroLocusSubschemeι_singleton f)
    (range_zeroLocusSubschemeι_singleton _) hg sq (tateObject Λ U 1) (tateObject Λ U' 1)
    (leftDerivedUpperStarTateObjectIso e 1)
  have hK := kummerClass_square Λ sq (U.basicOpenUnit f) _ hu
  have hA := comp_leftDerivedUpperStar_map_adjoint_comp_derivedBaseChangeMap
    (ModuleCat.{u + 1} Λ) sq (constantComplex Λ U) (constantComplex Λ U')
    (leftDerivedUpperStarConstantComplexIso Λ e).inv _
    ((leftDerivedUpperStarConstantComplexIso Λ (U.basicOpen f).ι).hom ≫
      kummerClass Λ (U.basicOpenUnit f) ≫
        (leftDerivedUpperStarTateObjectIso (U.basicOpen f).ι 1).inv⟦(1 : ℤ)⟧') _
    ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).inv.app (tateObject Λ U 1) ≫
      (L(((U'.basicOpen (e.appTop f)).ι)^*[ModuleCat.{u + 1} Λ])).map
        (leftDerivedUpperStarTateObjectIso e 1).hom)
  conv_rhs at hG1 => rw [← Category.assoc]
  rw [kummerBoundary_eq, kummerBoundary_eq, Functor.map_comp, Category.assoc, Category.assoc,
    Functor.map_shift_comp_shiftFunctorAdd'_inv, hG1,
    Functor.map_comp
      (shiftFunctor (DerivedCategory (Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (1 : ℤ)),
    Category.assoc, reassoc_of% hA, hK]
  simp only [Category.assoc]

end Kummer

end Etale

end AlgebraicGeometry
