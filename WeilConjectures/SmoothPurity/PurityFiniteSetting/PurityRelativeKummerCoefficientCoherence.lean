/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerDefs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStarCoherence
public import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-! # Coherence of the canonical coefficient pullbacks

The canonical pullback maps of the constant coefficient sheaf, underived and derived, are
compatible with composition and with commutative squares.

Source: blueprint lem-pur-relative-kummer-exchange-from-conclusions (auxiliary lemmas).
-/

@[expose] public section
set_option autoImplicit false
universe u' u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The two descriptions of the commutation of `ν^*` with pullbacks agree. -/
lemma comparisonUpperStarCompUpperStarIso_eq {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    comparisonUpperStarCompUpperStarIso A g = comparisonUpperStarUpperStarIso A g := by
  rw [comparisonUpperStarCompUpperStarIso, lowerStarCompComparisonLowerStarIso_eq]
  rfl

/-- The commutation of `ν^*` with pullbacks is compatible with composition. -/
lemma comparisonUpperStarCompUpperStarIso_comp {X Y Z : Scheme.{u}} (p : X ⟶ Y) (q : Y ⟶ Z)
    (M : Sheaf Z.smallEtaleTopology A) :
    (upperStarComp A p q).hom.app ((comparisonUpperStar A Z).obj M) ≫
        (upperStar A p).map ((comparisonUpperStarCompUpperStarIso A q).hom.app M) ≫
        (comparisonUpperStarCompUpperStarIso A p).hom.app ((Etale.upperStar A q).obj M) =
      (comparisonUpperStarCompUpperStarIso A (p ≫ q)).hom.app M ≫
        (comparisonUpperStar A X).map ((Etale.upperStarComp A p q).hom.app M) := by
  have H := comparisonUpperStarUpperStarIso_compCoherence A p q M
  simp only [comparisonUpperStarCompUpperStarIso_eq, Iso.symm_hom] at H ⊢
  rw [← cancel_epi ((comparisonUpperStarUpperStarIso A (p ≫ q)).inv.app M), reassoc_of% H]
  simp [← Functor.map_comp_assoc]

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The derived composition isomorphism on a sheaf in degree zero is the composition
isomorphism of the pullbacks. -/
lemma leftDerivedUpperStarComp_hom_app_singleFunctor_obj {T S R : Scheme.{u}}
    (g₁ : T ⟶ S) (g₂ : S ⟶ R) (F : Sheaf (Scheme.ProEt.topology R) A) :
    (leftDerivedUpperStarComp A g₁ g₂).hom.app ((DerivedCategory.singleFunctor _ 0).obj F) ≫
      (L((g₁)^*[A])).map ((singleFunctorCompLeftDerivedUpperStarIso A g₂).hom.app F) ≫
      (singleFunctorCompLeftDerivedUpperStarIso A g₁).hom.app ((g₂)^*[A].obj F) =
    (singleFunctorCompLeftDerivedUpperStarIso A (g₁ ≫ g₂)).hom.app F ≫
      (DerivedCategory.singleFunctor _ 0).map ((upperStarComp A g₁ g₂).hom.app F) := by
  simp only [leftDerivedUpperStarComp, singleFunctorCompLeftDerivedUpperStarIso, Iso.trans_hom,
    NatTrans.comp_app, Category.assoc]
  rw [Functor.leftDerivedFunctorCompIso_hom_app_singleFunctor_obj]
  exact Functor.leftDerivedFunctorNatIso_hom_app_singleFunctor_obj _ _ _ F

/-- Composition of two pullback maps of sheaves placed in degree zero. -/
lemma leftDerivedUpperStarComp_hom_app_singleFunctor_map {T S R : Scheme.{u}}
    (g₁ : T ⟶ S) (g₂ : S ⟶ R) {F : Sheaf (Scheme.ProEt.topology R) A}
    {G : Sheaf (Scheme.ProEt.topology S) A} {H : Sheaf (Scheme.ProEt.topology T) A}
    (φ₂ : (g₂)^*[A].obj F ⟶ G) (φ₁ : (g₁)^*[A].obj G ⟶ H) :
    (leftDerivedUpperStarComp A g₁ g₂).hom.app ((DerivedCategory.singleFunctor _ 0).obj F) ≫
      (L((g₁)^*[A])).map ((singleFunctorCompLeftDerivedUpperStarIso A g₂).hom.app F ≫
        (DerivedCategory.singleFunctor _ 0).map φ₂) ≫
      (singleFunctorCompLeftDerivedUpperStarIso A g₁).hom.app G ≫
        (DerivedCategory.singleFunctor _ 0).map φ₁ =
    (singleFunctorCompLeftDerivedUpperStarIso A (g₁ ≫ g₂)).hom.app F ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((upperStarComp A g₁ g₂).hom.app F ≫ (g₁)^*[A].map φ₂ ≫ φ₁) := by
  have hs := (singleFunctorCompLeftDerivedUpperStarIso A g₁).hom.naturality φ₂
  simp only [Functor.comp_map] at hs
  rw [Functor.map_comp, Category.assoc, reassoc_of% hs,
    reassoc_of% leftDerivedUpperStarComp_hom_app_singleFunctor_obj, Functor.map_comp,
    Functor.map_comp]

/-- `leftDerivedUpperStarComp_hom_app_singleFunctor_map` for morphisms given up to equality.
Stated this way so that it applies to morphisms defined by such composites without the kernel
having to compare different presentations of their sources and targets. -/
lemma leftDerivedUpperStarComp_hom_app_comp_eq {T S R : Scheme.{u}}
    (g₁ : T ⟶ S) (g₂ : S ⟶ R) {F : Sheaf (Scheme.ProEt.topology R) A}
    {G : Sheaf (Scheme.ProEt.topology S) A} {H : Sheaf (Scheme.ProEt.topology T) A}
    {φ₂ : (g₂)^*[A].obj F ⟶ G} {φ₁ : (g₁)^*[A].obj G ⟶ H}
    {φ : (g₁ ≫ g₂)^*[A].obj F ⟶ H}
    {ψ₂ : (L((g₂)^*[A])).obj ((DerivedCategory.singleFunctor _ 0).obj F) ⟶
      (DerivedCategory.singleFunctor _ 0).obj G}
    {ψ₁ : (L((g₁)^*[A])).obj ((DerivedCategory.singleFunctor _ 0).obj G) ⟶
      (DerivedCategory.singleFunctor _ 0).obj H}
    {ψ : (L((g₁ ≫ g₂)^*[A])).obj ((DerivedCategory.singleFunctor _ 0).obj F) ⟶
      (DerivedCategory.singleFunctor _ 0).obj H}
    (h₂ : ψ₂ = (singleFunctorCompLeftDerivedUpperStarIso A g₂).hom.app F ≫
      (DerivedCategory.singleFunctor _ 0).map φ₂)
    (h₁ : ψ₁ = (singleFunctorCompLeftDerivedUpperStarIso A g₁).hom.app G ≫
      (DerivedCategory.singleFunctor _ 0).map φ₁)
    (h : ψ = (singleFunctorCompLeftDerivedUpperStarIso A (g₁ ≫ g₂)).hom.app F ≫
      (DerivedCategory.singleFunctor _ 0).map φ)
    (hφ : (upperStarComp A g₁ g₂).hom.app F ≫ (g₁)^*[A].map φ₂ ≫ φ₁ = φ) :
    (leftDerivedUpperStarComp A g₁ g₂).hom.app ((DerivedCategory.singleFunctor _ 0).obj F) ≫
      (L((g₁)^*[A])).map ψ₂ ≫ ψ₁ = ψ := by
  subst h₂ h₁ h hφ
  exact leftDerivedUpperStarComp_hom_app_singleFunctor_map A g₁ g₂ φ₂ φ₁

end AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

variable (P : PurityFiniteSetting.{u}) (h : P.ramificationIndex ∣ P.level)

/-- The canonical pullback of constant coefficients is compatible with composition. -/
lemma constantPullback_comp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
    (ProEtale.upperStarComp (ModuleCat.{u + 1} P.Coefficient) a b).hom.app (P.constant Z) ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).map (P.constantPullback b) ≫
        P.constantPullback a = P.constantPullback (a ≫ b) := by
  have hc := ProEtale.comparisonUpperStarCompUpperStarIso_comp (ModuleCat.{u + 1} P.Coefficient)
    a b (P.constantEtale Z)
  have hn := (ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} P.Coefficient)
    a).hom.naturality ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient)
      b).hom.app (ModuleCat.of P.Coefficient P.Coefficient))
  have hu := Scheme.upperStarConstantSheafIso_comp (ModuleCat.{u + 1} P.Coefficient) a b
    (ModuleCat.of P.Coefficient P.Coefficient)
  simp only [Functor.comp_map] at hn
  simp only [constantPullback, Functor.map_comp, Category.assoc]
  erw [reassoc_of% hn, reassoc_of% hc]
  rw [← Functor.map_comp, ← Functor.map_comp]
  erw [hu]

/-- The canonical pullback map of the degree-zero coefficient sheaves, as used in
`derivedCoefficientPullback`. -/
noncomputable def coefficientPullback {X Y : Scheme.{u}} (f : X ⟶ Y) (twisted : Bool) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj
        (P.coefficientSheaf h Y twisted) ⟶
      P.coefficientSheaf h X twisted :=
  match twisted with
  | true => P.twistPullback h f
  | false => P.constantPullback f

lemma derivedCoefficientPullback_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (twisted : Bool) :
    P.derivedCoefficientPullback h f twisted =
      (ProEtale.singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} P.Coefficient)
        f).hom.app (P.coefficientSheaf h Y twisted) ≫
      (DerivedCategory.singleFunctor _ 0).map (P.coefficientPullback h f twisted) := by
  rfl

/-- `constantPullback_comp` for the coefficient sheaves. -/
lemma coefficientPullback_false_comp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
    (ProEtale.upperStarComp (ModuleCat.{u + 1} P.Coefficient) a b).hom.app
        (P.coefficientSheaf h Z false) ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).map
        (P.coefficientPullback h b false) ≫ P.coefficientPullback h a false =
      P.coefficientPullback h (a ≫ b) false :=
  constantPullback_comp P a b

/-- The derived pullback of constant coefficients is compatible with composition. -/
lemma derivedCoefficientPullback_false_comp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
    (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) a b).hom.app
        (P.derivedSheaf h Z false) ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor.map
        (P.derivedCoefficientPullback h b false) ≫ P.derivedCoefficientPullback h a false =
      P.derivedCoefficientPullback h (a ≫ b) false := by
  exact ProEtale.leftDerivedUpperStarComp_hom_app_comp_eq _ a b
    (derivedCoefficientPullback_eq P h b false) (derivedCoefficientPullback_eq P h a false)
    (derivedCoefficientPullback_eq P h (a ≫ b) false) (coefficientPullback_false_comp P h a b)

/-- The derived pullbacks of constant coefficients along a commutative square agree. -/
lemma derivedCoefficientPullback_false_square {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g) :
    (ProEtale.leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} P.Coefficient) sq).hom.app
        (P.derivedSheaf h Y false) ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) g').leftDerivedFunctor.map
        (P.derivedCoefficientPullback h f false) ≫ P.derivedCoefficientPullback h g' false =
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f').leftDerivedFunctor.map
        (P.derivedCoefficientPullback h g false) ≫ P.derivedCoefficientPullback h f' false := by
  have hcongr {a b : X' ⟶ Y} (e : a = b) :
      (ProEtale.leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient) e).hom.app
        (P.derivedSheaf h Y false) ≫ P.derivedCoefficientPullback h b false =
        P.derivedCoefficientPullback h a false := by
    subst e
    simp
  have h1 := derivedCoefficientPullback_false_comp P h f' g
  have h2 := derivedCoefficientPullback_false_comp P h g' f
  simp only [ProEtale.leftDerivedUpperStarSquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [h2, hcongr, ← h1, Iso.inv_hom_id_app_assoc]

end WeilConjectures.PurityFiniteSetting
