/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerEtaleNaturality
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerExchangeShift
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerCoefficientCoherence
public import WeilConjectures.Algebra.Homology.DerivedCategory.Ext.MapExactFunctorHom

/-! # Naturality of the pro-étale Kummer class under derived pullback

Source: blueprint lem-pur-relative-kummer-exchange-from-conclusions (auxiliary lemmas).
-/

@[expose] public section
set_option autoImplicit false
universe w w' t t' v v' u'' u' u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace CategoryTheory.Abelian.Ext

variable {C : Type u''} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D] [HasExt.{w} C] [HasExt.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {Φ : DerivedCategory C ⥤ DerivedCategory D} [Φ.CommShift ℤ]
  (θ : Φ ≅ F.mapDerivedCategory) [NatTrans.CommShift θ.hom ℤ]

/-- Naturality of `Ext`-classes under a functor `Φ` identified with `F.mapDerivedCategory`:
if `e'` is the pushforward of `e` along `F` read through the isomorphisms `φX`, `φY`, then
`Φ(e)` read through the induced isomorphisms `ψX`, `ψY` is `e'`. The morphisms `ψX`, `ψY`
are given up to equality, so that this applies to morphisms defined by such composites. -/
theorem map_hom_comp_commShiftIso_eq {X Y : C} {X' Y' : D} {φX : F.obj X ⟶ X'}
    {φY : F.obj Y ⟶ Y'} [IsIso φX] [IsIso φY]
    {ψX : Φ.obj ((DerivedCategory.singleFunctor C 0).obj X) ⟶
      (DerivedCategory.singleFunctor D 0).obj X'}
    {ψY : Φ.obj ((DerivedCategory.singleFunctor C 0).obj Y) ⟶
      (DerivedCategory.singleFunctor D 0).obj Y'}
    (hψX : ψX = θ.hom.app _ ≫ (F.mapDerivedCategorySingleFunctor 0).hom.app X ≫
      (DerivedCategory.singleFunctor D 0).map φX)
    (hψY : ψY = θ.hom.app _ ≫ (F.mapDerivedCategorySingleFunctor 0).hom.app Y ≫
      (DerivedCategory.singleFunctor D 0).map φY)
    {n : ℕ} {e : Ext.{w} X Y n} {e' : Ext.{w'} X' Y' n}
    (he : (e.mapExactFunctor F).comp (mk₀ φY) (add_zero n) = (mk₀ φX).comp e' (zero_add n)) :
    Φ.map e.hom ≫ (Φ.commShiftIso (n : ℤ)).hom.app _ ≫ ψY⟦(n : ℤ)⟧' =
      ψX ≫ e'.hom := by
  have : IsIso ψX := by
    rw [hψX]
    infer_instance
  have : IsIso ψY := by
    rw [hψY]
    infer_instance
  have key := mapExactFunctor_conj_hom F θ (asIso φX) (asIso φY) (asIso ψX) (asIso ψY)
    hψX hψY e
  rw [asIso_hom, he, asIso_inv, ← comp_assoc_of_second_deg_zero, mk₀_comp_mk₀,
    IsIso.inv_hom_id,
    mk₀_id_comp, asIso_inv, asIso_hom] at key
  rw [key, IsIso.hom_inv_id_assoc]

/-- `map_hom_comp_commShiftIso_eq` in degree one, with the shift written as the integer `1`. -/
theorem map_hom_comp_commShiftIso_one_eq {X Y : C} {X' Y' : D} {φX : F.obj X ⟶ X'}
    {φY : F.obj Y ⟶ Y'} [IsIso φX] [IsIso φY]
    {ψX : Φ.obj ((DerivedCategory.singleFunctor C 0).obj X) ⟶
      (DerivedCategory.singleFunctor D 0).obj X'}
    {ψY : Φ.obj ((DerivedCategory.singleFunctor C 0).obj Y) ⟶
      (DerivedCategory.singleFunctor D 0).obj Y'}
    (hψX : ψX = θ.hom.app _ ≫ (F.mapDerivedCategorySingleFunctor 0).hom.app X ≫
      (DerivedCategory.singleFunctor D 0).map φX)
    (hψY : ψY = θ.hom.app _ ≫ (F.mapDerivedCategorySingleFunctor 0).hom.app Y ≫
      (DerivedCategory.singleFunctor D 0).map φY)
    {e : Ext.{w} X Y 1} {e' : Ext.{w'} X' Y' 1}
    (he : (e.mapExactFunctor F).comp (mk₀ φY) (add_zero 1) = (mk₀ φX).comp e' (zero_add 1)) :
    Φ.map e.hom ≫ (Φ.commShiftIso (1 : ℤ)).hom.app _ ≫ ψY⟦(1 : ℤ)⟧' =
      ψX ≫ e'.hom :=
  map_hom_comp_commShiftIso_eq F θ hψX hψY he

end CategoryTheory.Abelian.Ext

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The comparison of `Lg^*` with `g^*` on objects in degree zero, through `Lg^* ≅ D(g^*)`. -/
lemma singleFunctorCompLeftDerivedUpperStarIso_hom_app {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (F : Sheaf (Scheme.ProEt.topology Y) A) :
    (singleFunctorCompLeftDerivedUpperStarIso A g).hom.app F =
      (leftDerivedUpperStarIsoMapDerivedCategory A g).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj F) ≫
        ((g)^*[A].mapDerivedCategorySingleFunctor 0).hom.app F :=
  rfl

end AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

variable (P : PurityFiniteSetting.{u}) (h : P.ramificationIndex ∣ P.level)

/-- Naturality of the pro-étale Kummer class. -/
theorem kummer_upperStar {X T : Scheme.{u}} (f : X ⟶ T)
    (hT : IsUnit (P.exponent : Γ(T, ⊤))) (hX : IsUnit (P.exponent : Γ(X, ⊤)))
    (s : Γ(T, ⊤)ˣ) :
    ((P.kummer h T hT s).mapExactFunctor
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f)).comp
        (Abelian.Ext.mk₀ (P.twistPullback h f)) (add_zero 1) =
      (Abelian.Ext.mk₀ (P.constantPullback f)).comp
        (P.kummer h X hX (Units.map f.appTop.hom s)) (zero_add 1) := by
  have e2 := kummerEtale_upperStar P h f hT hX s
  unfold kummer
  rw [Abelian.Ext.mapExactFunctor_mapExactFunctor,
    Abelian.Ext.mapExactFunctor_eq_of_iso
      (ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} P.Coefficient) f).symm,
    ← Abelian.Ext.mapExactFunctor_mapExactFunctor]
  simp only [twistPullback, constantPullback, Iso.symm_inv, Iso.symm_hom,
    Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
    Iso.inv_hom_id_app_assoc]
  rw [← Abelian.Ext.mapExactFunctor_mk₀, ← Abelian.Ext.mapExactFunctor_comp, e2,
    Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.mk₀_comp_mk₀_assoc]

lemma isIso_constantPullback {X Y : Scheme.{u}} (f : X ⟶ Y) : IsIso (P.constantPullback f) := by
  unfold constantPullback
  infer_instance

lemma isIso_twistPullback {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (P.exponent : Γ(Y, ⊤))) :
    IsIso (P.twistPullback h f) := by
  have : IsIso (P.twistEtalePullback h f) := P.isIso_twistEtalePullback h f hY
  unfold twistPullback
  infer_instance

/-- The derived coefficient pullbacks are isomorphisms when the exponent is invertible. -/
lemma isIso_derivedCoefficientPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (P.exponent : Γ(Y, ⊤))) (t : Bool) :
    IsIso (P.derivedCoefficientPullback h f t) := by
  have : IsIso (P.coefficientPullback h f t) := by
    cases t
    · exact P.isIso_constantPullback f
    · exact P.isIso_twistPullback h f hY
  rw [derivedCoefficientPullback_eq]
  infer_instance

/-- `derivedCoefficientPullback` through `Lf^* ≅ D(f^*)`. -/
lemma derivedCoefficientPullback_eq_mapDerivedCategory {X T : Scheme.{u}} (f : X ⟶ T)
    (twisted : Bool) :
    P.derivedCoefficientPullback h f twisted =
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} P.Coefficient)
          f).hom.app ((DerivedCategory.singleFunctor _ 0).obj (P.coefficientSheaf h T twisted)) ≫
        ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).mapDerivedCategorySingleFunctor
          0).hom.app (P.coefficientSheaf h T twisted) ≫
        (DerivedCategory.singleFunctor _ 0).map (P.coefficientPullback h f twisted) := by
  rw [derivedCoefficientPullback_eq, ProEtale.singleFunctorCompLeftDerivedUpperStarIso_hom_app,
    Category.assoc]

/-- `leftDerived_map_kummer_hom` with the shifted object written as a sheaf in degree zero. -/
theorem leftDerived_map_kummer_hom_aux {X T : Scheme.{u}} (f : X ⟶ T)
    (hT : IsUnit (P.exponent : Γ(T, ⊤))) (hX : IsUnit (P.exponent : Γ(X, ⊤)))
    (s : Γ(T, ⊤)ˣ) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.map
        (P.kummer h T hT s).hom ≫
      ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.commShiftIso
        (1 : ℤ)).hom.app ((DerivedCategory.singleFunctor _ 0).obj
          (P.coefficientSheaf h T true)) ≫
      (P.derivedCoefficientPullback h f true)⟦(1 : ℤ)⟧' =
    P.derivedCoefficientPullback h f false ≫
      (P.kummer h X hX (Units.map f.appTop.hom s)).hom := by
  have : IsIso (P.coefficientPullback h f false) := P.isIso_constantPullback f
  have : IsIso (P.coefficientPullback h f true) := P.isIso_twistPullback h f hT
  exact Abelian.Ext.map_hom_comp_commShiftIso_one_eq _
    (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} P.Coefficient) f)
    (P.derivedCoefficientPullback_eq_mapDerivedCategory h f false)
    (P.derivedCoefficientPullback_eq_mapDerivedCategory h f true)
    (P.kummer_upperStar h f hT hX s)

-- keeps the elaborator from unfolding the shift structure when matching objects
attribute [local irreducible] ProEtale.commShiftLeftDerivedUpperStar in
/-- Naturality of the derived pro-étale Kummer class. -/
theorem leftDerived_map_kummer_hom {X T : Scheme.{u}} (f : X ⟶ T)
    (hT : IsUnit (P.exponent : Γ(T, ⊤))) (hX : IsUnit (P.exponent : Γ(X, ⊤)))
    (s : Γ(T, ⊤)ˣ) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.map
        (P.kummer h T hT s).hom ≫
      ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.commShiftIso
        (1 : ℤ)).hom.app (P.derivedSheaf h T true) ≫
      (P.derivedCoefficientPullback h f true)⟦(1 : ℤ)⟧' =
    P.derivedCoefficientPullback h f false ≫
      (P.kummer h X hX (Units.map f.appTop.hom s)).hom :=
  P.leftDerived_map_kummer_hom_aux h f hT hX s

end WeilConjectures.PurityFiniteSetting
