/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactSupportScalarLimitReduction
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Compactification.RefinementCategory

import all WeilConjectures.AlgebraicGeometry.OrdinaryOpenScalarComposition
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.AlgebraicGeometry.StrictProperRestrictionComposition

/-! # Composition of strict compact-support scalar mates

Source: Stacks Tags 07A6 (lemma-adjoint), 0E8I and 0941; the auxiliary
composition calculation in returned comparison Step 11.
(blueprint: lem-pur-compact-support-strict-scalar-composition).

The tensor associators below are conjugates of the identity-on-sections restriction
comparisons. Arithmetic reassociation is the localization of the actual index equality.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (j : F →ₐ[ℚ_[l]] L)

/-- The actual constant coefficient maps compose, including identity embeddings.
Source: tensor balancing, auxiliary proof Steps 1 and 6
(blueprint: lem-pur-compact-support-strict-scalar-composition).
Proof: the integral inclusions compose on elements of the fields; functoriality
of the constant sheaf and the universe lift preserves that equality. -/
theorem constantMap_composition (W : Scheme.{u}) :
    constantMap l E F i W ≫ constantMap l F L j W =
      constantMap l E L (j.comp i) W := by
  unfold constantMap
  rw [← Functor.map_comp]
  congr 1

/-- Ordinary constant tensor associativity, normalized by the tensor-unit adjunctions.
Source: Stacks 07A6; auxiliary proof Steps 1--2
(blueprint: lem-pur-compact-support-strict-scalar-composition). -/
def compositionOrdinary (W : Scheme.{u}) :
    pbcExtend (constantMap l E F i W) ⋙ pbcExtend (constantMap l F L j W) ≅
      pbcExtend (constantMap l E L (j.comp i) W) :=
  (((pbcScalarAdjunction (constantMap l E F i W)).comp
      (pbcScalarAdjunction (constantMap l F L j W))).ofNatIsoRight
    (pbcRestrictComp _ _ _ (constantMap_composition l E F i L j W))).leftAdjointUniq
      (pbcScalarAdjunction (constantMap l E L (j.comp i) W))

/-- Tensor associativity on derived constant-coefficient module sheaves.
Source: Stacks 06YY; auxiliary proof Step 7
(blueprint: lem-pur-compact-support-strict-scalar-composition). -/
def compositionBase (W : Scheme.{u}) :
    baseTensor l E F i W ⋙ baseTensor l F L j W ≅ baseTensor l E L (j.comp i) W :=
  haveI := (baseTensor_exact l E F i W).1
  haveI := (baseTensor_exact l E F i W).2
  haveI := (baseTensor_exact l F L j W).1
  haveI := (baseTensor_exact l F L j W).2
  haveI := (baseTensor_exact l E L (j.comp i) W).1
  haveI := (baseTensor_exact l E L (j.comp i) W).2
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (compositionOrdinary l E F i L j W)

/-- The same ordinary associator on whole strict towers.
Source: Stacks 0940; auxiliary proof Step 2
(blueprint: lem-pur-compact-support-strict-scalar-composition). -/
def compositionTowerOrdinary (W : Scheme.{u}) :
    tensor l E F i W ⋙ tensor l F L j W ≅ tensor l E L (j.comp i) W :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (compositionOrdinary l E F i L j W)

/-- The associator alpha in the strict derived diagram category, before taking limits.
Source: Stacks 0940; auxiliary proof Steps 2--5
(blueprint: lem-pur-compact-support-strict-scalar-composition). -/
def compositionTower (W : Scheme.{u}) :
    T l E F i W ⋙ T l F L j W ≅ T l E L (j.comp i) W :=
  haveI := (tensor_exact l E F i W).1
  haveI := (tensor_exact l E F i W).2
  haveI := (tensor_exact l F L j W).1
  haveI := (tensor_exact l F L j W).2
  haveI := (tensor_exact l E L (j.comp i) W).1
  haveI := (tensor_exact l E L (j.comp i) W).2
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (compositionTowerOrdinary l E F i L j W)

/-- Ordinary completed tensor associativity with the published scalar adjunction units.
Source: Stacks 07A6; auxiliary proof Step 9
(blueprint: lem-pur-compact-support-strict-scalar-composition). -/
def compositionCompleted (W : Scheme.{u}) :
    pbcDerivedExtend (completedCoefficientMap l E F i W) ⋙
        pbcDerivedExtend (completedCoefficientMap l F L j W) ≅
      pbcDerivedExtend (completedCoefficientMap l E L (j.comp i) W) :=
  PurCompactSupport.tensorComposition _ _ _
    (PurCompactSupport.completedMap_composition l E F i L j W)

/-- Exact tensor commutes with selection of arithmetic levels by the identity square.
Source: Stacks 0940; auxiliary proof Step 5
(blueprint: lem-pur-compact-support-strict-scalar-composition). -/
def compositionSelection (W : Scheme.{u}) (e : ℕ) :
    subsequence l F W e ⋙ T l F L j W ≅ T l F L j W ⋙ subsequence l L W e :=
  haveI := (tensor_exact l F L j W).1
  haveI := (tensor_exact l F L j W).2
  Functor.mapDerivedCategorySquareIso (Iso.refl _)

/-- Nested selections retain precisely the same objects and composite transitions.
Source: arithmetic level calculation, auxiliary proof Steps 1 and 5
(blueprint: lem-pur-compact-support-strict-scalar-composition).
Proof: the predecessor of h(e(n+1)) is h*e*(n+1)-1. Positivity of e and h
permits cancellation of each predecessor/successor pair. Arrows agree because
natural-number order categories have at most one arrow between two objects. -/
theorem compositionSelectionOrdinary (W : Scheme.{u}) (e h : ℕ)
    (he : 1 ≤ e) (hh : 1 ≤ h) :
    ordinarySubsequence l L W h ⋙ ordinarySubsequence l L W e =
      ordinarySubsequence l L W (h * e) := by
  have _hhpos := hh
  have hi : CategoryTheory.StrictTowerArithmetic.index e ⋙
      CategoryTheory.StrictTowerArithmetic.index h =
        CategoryTheory.StrictTowerArithmetic.index (h * e) := by
    apply CategoryTheory.Functor.ext
    · intro a b f
      apply Subsingleton.elim
    · intro n
      cases n with
      | op n =>
        apply congrArg op
        change h * (e * (n + 1) - 1 + 1) - 1 = (h * e) * (n + 1) - 1
        rw [Nat.sub_add_cancel (Nat.mul_pos he (Nat.succ_pos n)), Nat.mul_assoc]
  change CategoryTheory.StrictTowerArithmetic.restriction _ h ⋙
    CategoryTheory.StrictTowerArithmetic.restriction _ e = _
  simp only [CategoryTheory.StrictTowerArithmetic.restriction]
  change (Functor.whiskeringLeft _ _ _).obj
    (CategoryTheory.StrictTowerArithmetic.index e ⋙
      CategoryTheory.StrictTowerArithmetic.index h) = _
  rw [hi]

/-- Canonical reassociation between the two retained strict derived towers.
Source: Stacks 0940; auxiliary proof Step 5
(blueprint: lem-pur-compact-support-strict-scalar-composition). -/
def compositionRetained (W : Scheme.{u}) (e h : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) :
    subsequence l L W h ⋙ subsequence l L W e ≅ subsequence l L W (h * e) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (eqToIso (compositionSelectionOrdinary l L W e h he hh))

/-- The ramification ideal equality for the composite inclusion.
Source: auxiliary proof Step 1
(blueprint: lem-pur-compact-support-strict-scalar-composition).
Proof: map the first ideal equality through the second integer inclusion, then
use preservation of ideal powers and the second equality. The exponent is h*e. -/
theorem compositionRamification (e h : ℕ)
    (he : PurCompactSupport.Ramification l E F i e)
    (hh : PurCompactSupport.Ramification l F L j h) :
    PurCompactSupport.Ramification l E L (j.comp i) (h * e) := by
  have hc : integralScalarIntegerInclusion l E L (j.comp i) =
      (integralScalarIntegerInclusion l F L j).comp
        (integralScalarIntegerInclusion l E F i) := by
    ext x
    rfl
  change Ideal.map _ _ = _
  rw [hc, ← Ideal.map_map, he]
  change Ideal.map _ (Ideal.span {Padic.coefficientExtensionUniformizer l F} ^ e) = _
  rw [Ideal.map_pow]
  have hh' := hh
  change Ideal.map _ (Ideal.span {Padic.coefficientExtensionUniformizer l F} ^ 1) =
    Ideal.span {Padic.coefficientExtensionUniformizer l L} ^ h at hh'
  rw [pow_one] at hh'
  rw [hh', ← pow_mul]
  rfl

attribute [local irreducible] scalarAdj properRestriction

private def properScalarMate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {r : B ⥤ A} {G : C ⥤ D} {s : D ⥤ C}
    (a : F ⊣ r) (b : G ⊣ s) {I : A ⥤ C} {J : B ⥤ D}
    (α : r ⋙ I ⟶ J ⋙ s) : I ⋙ G ⟶ F ⋙ J :=
  ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ α)).natTrans

private theorem inverse_restriction_cocycle
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C]
    [Category A'] [Category B'] [Category C']
    {r : B ⥤ A} {s : C ⥤ B} {t : C ⥤ A}
    {r' : B' ⥤ A'} {s' : C' ⥤ B'} {t' : C' ⥤ A'}
    {I : A ⥤ A'} {J : B ⥤ B'} {K : C ⥤ C'}
    (c : s ⋙ r ≅ t) (c' : s' ⋙ r' ≅ t')
    (a : J ⋙ r' ≅ r ⋙ I) (b : K ⋙ s' ≅ s ⋙ J) (e : K ⋙ t' ≅ t ⋙ I)
    (he : ∀ M, r'.map (b.hom.app M) ≫ a.hom.app (s.obj M) ≫
      I.map (c.hom.app M) = c'.hom.app (K.obj M) ≫ e.hom.app M) (M : C) :
    I.map (c.hom.app M) ≫ e.inv.app M =
      a.inv.app (s.obj M) ≫ r'.map (b.inv.app M) ≫ c'.hom.app (K.obj M) := by
  have hd := congrArg (fun z ↦
    a.inv.app (s.obj M) ≫ r'.map (b.inv.app M) ≫ z ≫ e.inv.app M) (he M)
  simp only [Category.assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, Iso.hom_inv_id_app] at hd
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app_assoc, Category.comp_id] at hd
  exact hd

private theorem proper_mate_tower_square
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C]
    [Category A'] [Category B'] [Category C']
    {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
    {r : B ⥤ A} {s : C ⥤ B} {t : C ⥤ A}
    {F' : A' ⥤ B'} {G' : B' ⥤ C'} {H' : A' ⥤ C'}
    {r' : B' ⥤ A'} {s' : C' ⥤ B'} {t' : C' ⥤ A'}
    (dF : F ⊣ r) (dG : G ⊣ s) (dH : H ⊣ t)
    (dF' : F' ⊣ r') (dG' : G' ⊣ s') (dH' : H' ⊣ t')
    {I : A ⥤ A'} {J : B ⥤ B'} {K : C ⥤ C'}
    (c : s ⋙ r ≅ t) (c' : s' ⋙ r' ≅ t')
    (a : r ⋙ I ⟶ J ⋙ r') (b : s ⋙ J ⟶ K ⋙ s') (e : t ⋙ I ⟶ K ⋙ t')
    (he : ∀ M, I.map (c.hom.app M) ≫ e.app M =
      a.app (s.obj M) ≫ r'.map (b.app M) ≫ c'.hom.app (K.obj M)) (M : A) :
    (Adjunction.leftAdjointCompIso dF' dG' dH' c').hom.app (I.obj M) ≫
        (properScalarMate dH dH' e).app M =
      G'.map ((properScalarMate dF dF' a).app M) ≫ (properScalarMate dG dG' b).app (F.obj M) ≫
        K.map ((Adjunction.leftAdjointCompIso dF dG dH c).hom.app M) := by
  let x : TwoSquare I (F ⋙ G) (F' ⋙ G') K :=
    TwoSquare.vComp (properScalarMate dF dF' a) (properScalarMate dG dG' b)
  let y : TwoSquare I (F ⋙ G) (F' ⋙ G') K :=
    ((TwoSquare.mk _ _ _ _ (properScalarMate dH dH' e)).whiskerLeft
      (Adjunction.leftAdjointCompIso dF dG dH c).inv).whiskerRight
        (Adjunction.leftAdjointCompIso dF' dG' dH' c').hom
  have h : x = y := by
    apply (mateEquiv (dF.comp dG) (dF'.comp dG')).injective
    dsimp only [x, y]
    rw [mateEquiv_hcomp]
    rw [mateEquiv_conjugateEquiv_vcomp (dF.comp dG) dH' (dF'.comp dG')]
    rw [conjugateEquiv_mateEquiv_vcomp (dF.comp dG) dH dH']
    simp only [properScalarMate, Equiv.apply_symm_apply,
      Adjunction.conjugateEquiv_leftAdjointCompIso_inv,
      Adjunction.leftAdjointCompIso_hom, Adjunction.leftAdjointCompNatTrans,
      Equiv.apply_symm_apply, TwoSquare.mk, TwoSquare.natTrans]
    ext N
    simp only [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id]
    apply (cancel_mono (c'.hom.app (K.obj N))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact (he N).symm
  have hh := congrArg (fun z ↦ z.app M) h
  dsimp only [x, y, TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app] at hh
  simp only [Category.id_comp, Category.comp_id] at hh
  apply (cancel_mono (K.map ((Adjunction.leftAdjointCompIso dF dG dH c).inv.app M))).1
  simp only [Category.assoc, ← K.map_comp, Iso.hom_inv_id_app]
  erw [K.map_id, Category.comp_id]
  exact hh.symm

/-- The strict scalar proper mates compose under ordinary tensor associativity.
Source: Stacks 07A6; auxiliary proof Steps 2--3
(blueprint: lem-pur-compact-support-strict-scalar-composition).
Proof: ordinary coefficient restriction and proper image commute by the identity
on underlying sections. Whole-complex unit normalization carries their cocycle
through right derivation. The localized ordinary tensor associator is the
canonical composite-adjunction comparison. Invert the restriction cocycle and
apply mate pasting with these normalized scalar adjunctions. -/
theorem compositionProper {Z W : Scheme.{u}} (g : Z ⟶ W)
    (K : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Z) :
    (compositionTower l E F i L j W).hom.app
          ((R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj K) ≫
        (proper l E L (j.comp i) g).app K =
      (T l F L j W).map ((proper l E F i g).app K) ≫
        (proper l F L j g).app ((T l E F i Z).obj K) ≫
        (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l L)) g).map
          ((compositionTower l E F i L j Z).hom.app K) := by
  have hα (V : Scheme.{u}) :
      compositionTower l E F i L j V =
        Adjunction.leftAdjointCompIso (scalarAdj l E F i V) (scalarAdj l F L j V)
          (scalarAdj l E L (j.comp i) V)
          (towerScalarRestrictionComposition l E F i L j V) :=
    scalarTowerAssociator_normalization l E F i L j V
  rw [hα Z, hα W]
  exact proper_mate_tower_square
    (scalarAdj l E F i Z) (scalarAdj l F L j Z)
    (scalarAdj l E L (j.comp i) Z)
    (scalarAdj l E F i W) (scalarAdj l F L j W)
    (scalarAdj l E L (j.comp i) W)
    (towerScalarRestrictionComposition l E F i L j Z)
    (towerScalarRestrictionComposition l E F i L j W)
    (properRestriction l E F i g).inv (properRestriction l F L j g).inv
    (properRestriction l E L (j.comp i) g).inv
    (inverse_restriction_cocycle
      (towerScalarRestrictionComposition l E F i L j Z)
      (towerScalarRestrictionComposition l E F i L j W)
      (properRestriction l E F i g) (properRestriction l F L j g)
      (properRestriction l E L (j.comp i) g)
      (properRestriction_composition l E F i L j g)) K

attribute [local irreducible] pbcScalarAdjunction pbcDerivedScalarAdjunction
  ordinaryOpenTensor ordinaryBaseOpenTensor PurCompactSupport.openAdjunction
  proEtaleRingRestrictionPullbackInv in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Open scalar balancing uses the same associator as the proper square.
Source: Stacks 0E8I; auxiliary proof Step 4
(blueprint: lem-pur-compact-support-strict-scalar-composition).
Proof: on objects in the open both paths multiply the two scalar factors; off
the open both are zero. This commutes with differentials and quotient transitions.
Sheafification and exact localization preserve the equality. -/
theorem compositionOpen {Z W : Scheme.{u}} (g : Z ⟶ W) [IsOpenImmersion g]
    (K : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Z) :
    (compositionTower l E F i L j W).hom.app
          ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj K) ≫
        (openTensor l E L (j.comp i) g).app K =
      (T l F L j W).map ((openTensor l E F i g).app K) ≫
        (openTensor l F L j g).app ((T l E F i Z).obj K) ≫
        (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l L)) g).map
          ((compositionTower l E F i L j Z).hom.app K) := by
  have hordinary (N : Towers
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Z) :
      (tensor l F L j W).map ((ordinaryOpenTensor l E F i g).app N) ≫
          (ordinaryOpenTensor l F L j g).app ((tensor l E F i Z).obj N) ≫
          (towerJ (ULift.{u + 1} (Padic.coefficientExtensionIntegers l L)) g).map
            ((compositionTowerOrdinary l E F i L j Z).hom.app N) =
        (compositionTowerOrdinary l E F i L j W).hom.app
            ((towerJ (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj N) ≫
          (ordinaryOpenTensor l E L (j.comp i) g).app N := by
    simp only [ordinaryOpenTensor_eq]
    apply NatTrans.ext
    funext n
    exact (ordinaryBaseOpenTensor_composition l E F i L j g (N.obj n)).symm
  exact localizedOpenTensor_composition l E F i L j g
    (compositionTowerOrdinary l E F i L j Z)
    (compositionTowerOrdinary l E F i L j W) hordinary K

end WeilConjectures.PurStrictScalar
