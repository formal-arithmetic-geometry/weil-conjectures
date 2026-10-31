/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableCompatibleTower
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerCompositionPasting
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.SixFunctors.Supporting.OperationCoefficientActionData
public import WeilConjectures.AlgebraicGeometry.RelativeCompactSupport.RelativeCompactSupportPasting
public import WeilConjectures.AlgebraicGeometry.StrictTower.MateEvaluationScalars.TowerMateEvaluationScalars
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
import WeilConjectures.AlgebraicGeometry.DirectScalar.ConstantScalarPullbackSquare
import WeilConjectures.SmoothPurity.Supporting.BasicOperationCoefficientCoherence
import WeilConjectures.CategoryTheory.Adjunction.ProperBaseChange.CoefficientExchange
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.OpenScalarExchangeMate
import all WeilConjectures.AlgebraicGeometry.RelativeCompactSupport.RelativeCompactSupportPasting
import WeilConjectures.AlgebraicGeometry.StrictTower.TowerOpenBetaNormalization
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerCompositionPasting
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
import WeilConjectures.AlgebraicGeometry.StrictTower.SingleLevelFiniteProperOpenTransport
import all WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport

/-! # Finite semilinear compactification exchange coherence

Source: blueprint, prop-pur-weil-equivariance-compatibilities, constituent assembly;
Stacks Tags 07A7, 0E47, 0F7J, 0D6D and 0FPI
(blueprint: lem-pur-isomorphism-finite-exchange-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
open AlgebraicGeometry.ProEtale.ConstantCompactificationExchange
open AlgebraicGeometry.ProEtale.RelativeCompactSupport
open WeilConjectures

namespace WeilConjectures.FiniteExchangeCoherence

/-- Finiteness of the already constructed positive coefficient quotient.
Source: def-pur-conventions (blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
instance ringFinite (P : PurityFiniteSetting.{u}) : Finite P.Ring :=
  Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos

/-- The standard site-size lift retains finiteness.
Source: def-pur-conventions (blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
instance coefficientFinite (P : PurityFiniteSetting.{u}) : Finite P.Coefficient :=
  inferInstanceAs (Finite (ULift.{u + 1} P.Ring))

/-- Package the already specified constant ring sheaves and constant-section pullbacks.
Source: Stacks 0H7J (blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
def constantSystem (B : Type (u + 1)) [CommRing B] : PurCompactSupport.Coefficients.{u} where
  ring := coefficients B
  pull := constantRingIso B

/-- The actual constant-sheaf coefficient change, with its canonical square.
Source: Stacks 0D6D (blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
def constantChange {B C : Type (u + 1)} [CommRing B] [CommRing C] (φ : B →+* C) :
    PurCompactSupport.Change (constantSystem B) (constantSystem C) where
  map := MateEvaluationScalars.coefficientMap φ
  square := MateEvaluationScalars.coefficient_square φ

/-- The pullback identity comparison descends the existing unit-normalized module map.
Source: Stacks 07A7 (blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
def pullId (B : Type (u + 1)) [CommRing B] (X : Scheme.{u}) :
    ordinaryG B (𝟙 X) ≅ 𝟭 (DerivedCategory (Modules B X)) :=
  Functor.mapDerivedCategoryNatIso (openBetaModuleGId B X) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The canonical proper-image compositor, conjugate to pullback composition.
Source: Stacks 0D6E (blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
def pushComp (B : Type (u + 1)) [CommRing B] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ordinaryR B f ⋙ ordinaryR B g ≅ ordinaryR B (f ≫ g) :=
  conjugateIsoEquiv ((ordinaryAdj B g).comp (ordinaryAdj B f))
    (ordinaryAdj B (f ≫ g)) (ordinaryGComp B f g)

/-- Exact open composition with the same open-adjunction normalization.
Source: Stacks 03DI (blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
def openComp (B : Type (u + 1)) [CommRing B] {X Y Z : Scheme.{u}}
    (j : X ⟶ Y) (k : Y ⟶ Z) [IsOpenImmersion j] [IsOpenImmersion k] :
    ordinaryJ B j ⋙ ordinaryJ B k ≅ ordinaryJ B (j ≫ k) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (openBetaModuleJComp B j k)

/-- The specified finite proper/open composition arrow, with both compositors.
Source: Stacks 0F7J (blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
def composition (B : Type (u + 1)) [CommRing B]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
    (T : Compactification.Triangle f h)
    [QuasiCompact T.cf.i] [QuasiCompact T.cg.i] [QuasiCompact T.q] :
    (ordinaryJ B T.cf.i ⋙ ordinaryR B T.cf.g) ⋙
        (ordinaryJ B T.cg.i ⋙ ordinaryR B T.cg.g) ⟶
      ordinaryJ B T.cfg.i ⋙ ordinaryR B T.cfg.g :=
  Functor.whiskerLeft (ordinaryJ B T.cf.i)
    (Functor.whiskerRight
      (MateEvaluationScalars.singleDerivedGamma B T.q T.cf.g T.p T.cg.i
        T.isPullback.w.symm) (ordinaryR B T.cg.g)) ≫
  Functor.whiskerRight
    ((openComp B T.cf.i T.q).hom ≫
      (Functor.mapDerivedCategoryNatIso (singleJCongr B T.i_q)).hom)
    (ordinaryR B T.p ⋙ ordinaryR B T.cg.g) ≫
  Functor.whiskerLeft (ordinaryJ B T.cfg.i)
    ((pushComp B T.p T.cg.g).hom ≫
      (eqToIso (congrArg (ordinaryR B) T.p_g)).hom)

private theorem ordinaryPullId_eq (B : Type (u + 1)) [CommRing B] (X : Scheme.{u}) :
    pullId B X = Functor.mapDerivedCategoryNatIso (moduleGId B X) ≪≫
      Functor.mapDerivedCategoryIdIso _ := by
  unfold pullId openBetaModuleGId moduleGId
  rfl

private theorem ordinaryComp_id_left (B : Type (u + 1)) [CommRing B]
    {U X : Scheme.{u}} (j : U ⟶ X) :
    (ordinaryGComp B (𝟙 U) j).hom ≫
        Functor.whiskerLeft (ordinaryG B j) (pullId B U).hom =
      (eqToIso (congrArg (ordinaryG B) (Category.id_comp j))).hom := by
  rw [ordinaryPullId_eq]
  change (_ ≫ _) ≫ Functor.whiskerLeft (modulePullback B j).mapDerivedCategory
    ((Functor.mapDerivedCategoryNatIso (moduleGId B U)).hom ≫
      (Functor.mapDerivedCategoryIdIso _).hom) = _
  rw [Category.assoc]
  exact (derived_unit_left (modulePullback B j) (modulePullback B ((𝟙 U) ≫ j))
    (modulePullback B (𝟙 U)) (moduleGComp B (𝟙 U) j) (moduleGId B U)
    (eqToIso (congrArg (modulePullback B) (Category.id_comp j)))
    (moduleGComp_id_left B j)).trans (derived_eqToIso _ _)

private theorem ordinaryComp_id_right (B : Type (u + 1)) [CommRing B]
    {U X : Scheme.{u}} (j : U ⟶ X) :
    (ordinaryGComp B j (𝟙 X)).hom ≫
        Functor.whiskerRight (pullId B X).hom (ordinaryG B j) =
      (eqToIso (congrArg (ordinaryG B) (Category.comp_id j))).hom := by
  rw [ordinaryPullId_eq]
  change (_ ≫ _) ≫ Functor.whiskerRight
    ((Functor.mapDerivedCategoryNatIso (moduleGId B X)).hom ≫
      (Functor.mapDerivedCategoryIdIso _).hom) (modulePullback B j).mapDerivedCategory = _
  rw [Category.assoc]
  exact (derived_unit_right (modulePullback B j) (modulePullback B (j ≫ 𝟙 X))
    (modulePullback B (𝟙 X)) (moduleGComp B j (𝟙 X)) (moduleGId B X)
    (eqToIso (congrArg (modulePullback B) (Category.comp_id j)))
    (moduleGComp_id_right B j)).trans (derived_eqToIso _ _)

private theorem ordinarySquare_identity (B : Type (u + 1)) [CommRing B]
    {U X : Scheme.{u}} (j : U ⟶ X)
    (h : (𝟙 U) ≫ j = j ≫ 𝟙 X) (N : DerivedCategory (Modules B X)) :
    (ordinarySquare B (𝟙 U) j j (𝟙 X) h).inv.app N ≫
        (ordinaryG B j).map ((pullId B X).hom.app N) =
      (pullId B U).hom.app ((ordinaryG B j).obj N) := by
  have hl := congr_app (ordinaryComp_id_left B j) N
  have hr := congr_app (ordinaryComp_id_right B j) N
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hl hr
  have ht : (eqToIso (congrArg (ordinaryG B) h)).hom ≫
      (eqToIso (congrArg (ordinaryG B) (Category.comp_id j))).hom =
        (eqToIso (congrArg (ordinaryG B) (Category.id_comp j))).hom := by
    simp only [eqToIso.hom, eqToHom_trans]
  have htN := congr_app ht N
  simp only [NatTrans.comp_app] at htN
  rw [ordinarySquare_eq B (𝟙 U) j j (𝟙 X) h]
  simp only [ordinaryGCompEq, Iso.trans_inv, Iso.symm_inv, Iso.trans_hom,
    NatTrans.comp_app, eqToIso_refl, Iso.refl_hom, Category.id_comp, Category.assoc]
  change (ordinaryGComp B (𝟙 U) j).inv.app N ≫
      (eqToIso (congrArg (ordinaryG B) h)).hom.app N ≫
      (ordinaryGComp B j (𝟙 X)).hom.app N ≫
      (ordinaryG B j).map ((pullId B X).hom.app N) = _
  rw [hr, htN, ← hl]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

private theorem mate_identity_normalized
    {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    {I : C ⥤ C} {H : D ⥤ D} (eI : I ≅ 𝟭 C) (eH : H ≅ 𝟭 D)
    (s : I ⋙ L ≅ L ⋙ H)
    (hs : ∀ N, s.inv.app N ≫ L.map (eI.hom.app N) = eH.hom.app (L.obj N))
    (M : D) :
    (mateEquiv a a s.hom).natTrans.app M ≫ R.map (eH.hom.app M) =
      eI.hom.app (R.obj M) := by
  apply (a.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_symm_apply, Functor.map_comp, Category.assoc]
  erw [a.counit.naturality]
  have hm := mateEquiv_counit a a s.hom M
  erw [reassoc_of% hm]
  apply (cancel_epi (s.inv.app (R.obj M))).1
  erw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  erw [reassoc_of% (hs (R.obj M))]
  exact eH.hom.naturality (a.counit.app M)

/-- Change only the positive coefficient level of the fixed datum.
Source: blueprint quotient-coefficient clause
(blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
def lower (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) : PurityFiniteSetting.{u} :=
  { P with level := m, level_pos := hm }

/-- The quotient A_n to A_m induced by identity on the valuation ring, with the site lift.
Source: blueprint quotient-coefficient clause
(blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
def quotient (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (h : m ≤ P.level) :
    P.Coefficient →+* (lower P m hm).Coefficient :=
  ULift.ringEquiv.symm.toRingHom.comp
    ((Ideal.Quotient.factor (Ideal.pow_le_pow_right h)).comp ULift.ringEquiv.toRingHom)

/-- The actual derived coefficient extension for the quotient ring map.
Source: Stacks 06YY (blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
def tensorQuotient (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (h : m ≤ P.level) (X : Scheme.{u}) :=
  pbcDerivedExtend ((constantChange (quotient P m hm h)).map X)

section Geometry
variable (P : PurityFiniteSetting.{u})
variable {X Y : Scheme.{u}} [Xbase : X.Over (Spec (.of P.field.k))]
  [Ybase : Y.Over (Spec (.of P.field.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of P.field.k))]
  [Xsep : IsSeparated (X ↘ Spec (.of P.field.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [Ysep : IsSeparated (Y ↘ Spec (.of P.field.k))]
variable {f : X ⟶ Y} [fbase : f.IsOver (Spec (.of P.field.k))]
  [fsep : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
include P Xbase Ybase Xft Xqc Xsep Yft Yqc Ysep fbase fsep fft fqc

/-- Identity for the actual finite exchange, with the canonical identity pullbacks.
Source: Stacks 07A7; blueprint constituent assembly
(blueprint: lem-pur-isomorphism-finite-exchange-coherence).
Proof: work over S=Y, so all underlying isomorphisms are S-maps. Mate-pasting gives
identity for the proper factor. Tower-open-beta-normalization, evaluated at finite
coefficients, gives identity for the open factor. Substitution in the recorded
mate-followed-by-open formula gives the displayed identity. -/
theorem identity (c : Compactification f)
    (sp : IsPullback (𝟙 c.Z) c.g c.g (𝟙 Y))
    (sj : IsPullback (𝟙 X) c.i c.i (𝟙 c.Z)) :
    ordinaryH P.Coefficient c c (𝟙 Y) (𝟙 X) (𝟙 c.Z) sp sj =
      Functor.whiskerLeft (ordinaryJ P.Coefficient c.i ⋙ ordinaryR P.Coefficient c.g)
          (pullId P.Coefficient Y).hom ≫
        (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight (pullId P.Coefficient X).inv
          (ordinaryJ P.Coefficient c.i ⋙ ordinaryR P.Coefficient c.g) := by
  have he (N : DerivedCategory (Modules P.Coefficient c.Z)) :=
    mate_identity_normalized (ordinaryAdj P.Coefficient c.g)
      (pullId P.Coefficient Y) (pullId P.Coefficient c.Z)
      (ordinarySquare P.Coefficient (𝟙 c.Z) c.g c.g (𝟙 Y) sp.w)
      (ordinarySquare_identity P.Coefficient c.g sp.w) N
  have hb (M : DerivedCategory (Modules P.Coefficient X)) :
      (ordinaryBeta P.Coefficient (𝟙 X) c.i c.i (𝟙 c.Z) sj).hom.app M ≫
          (ordinaryJ P.Coefficient c.i).map ((pullId P.Coefficient X).hom.app M) =
        (pullId P.Coefficient c.Z).hom.app ((ordinaryJ P.Coefficient c.i).obj M) := by
    have hi : (ordinaryBeta P.Coefficient (𝟙 X) c.i c.i (𝟙 c.Z) sj).inv.app M ≫
        (pullId P.Coefficient c.Z).hom.app ((ordinaryJ P.Coefficient c.i).obj M) =
      (ordinaryJ P.Coefficient c.i).map ((pullId P.Coefficient X).hom.app M) := by
      apply ((ordinaryJAdj P.Coefficient c.i).homEquiv _ _).injective
      rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit]
      rw [ordinaryBetaInv_unit]
      rw [Category.assoc, ordinarySquare_identity]
      exact ((pullId P.Coefficient X).hom.naturality
        ((ordinaryJAdj P.Coefficient c.i).unit.app M)).trans
          ((ordinaryJAdj P.Coefficient c.i).unit.naturality
            ((pullId P.Coefficient X).hom.app M))
    apply (cancel_epi
      ((ordinaryBeta P.Coefficient (𝟙 X) c.i c.i (𝟙 c.Z) sj).inv.app M)).1
    rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp, hi]
  apply NatTrans.ext
  funext M
  simp only [ordinaryH, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_hom_app,
    Functor.leftUnitor_inv_app, Functor.comp_obj, Functor.comp_map,
    Category.id_comp, Category.comp_id]
  apply (cancel_mono ((ordinaryR P.Coefficient c.g).map
    ((ordinaryJ P.Coefficient c.i).map ((pullId P.Coefficient X).hom.app M)))).1
  rw [Category.assoc, ← Functor.map_comp, hb]
  erw [he]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.comp_id]
  rfl

/-- Horizontal pasting for the specified finite exchange under successive isomorphisms.
Source: Stacks 0E47; blueprint constituent assembly
(blueprint: lem-pur-isomorphism-finite-exchange-coherence).
Proof: use ordinaryPasting of lem-pur-relative-compact-support-pasting with B=A_n,
a=g, b=h, over S=Y. Its E, beta and H are the actual specified factors. The
unique projection-preserving fibre-product identifications give the displayed
compositors. No k-linearity of either isomorphism is used. -/
theorem horizontal {X' X'' Y' Y'' : Scheme.{u}}
    {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    [X'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [IsSeparated (X' ↘ Spec (.of P.field.k))]
    [X''.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X'' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X'' ↘ Spec (.of P.field.k))]
    [IsSeparated (X'' ↘ Spec (.of P.field.k))]
    [Y'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    [IsSeparated (Y' ↘ Spec (.of P.field.k))]
    [Y''.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y'' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y'' ↘ Spec (.of P.field.k))]
    [IsSeparated (Y'' ↘ Spec (.of P.field.k))]
    (c : Compactification f) (c' : Compactification f') (c'' : Compactification f'')
    (g : Y' ⟶ Y) (h : Y'' ⟶ Y') [IsIso g] [IsIso h]
    (x : X' ⟶ X) (x' : X'' ⟶ X') (z : c'.Z ⟶ c.Z) (z' : c''.Z ⟶ c'.Z)
    (sp : IsPullback z c'.g c.g g) (sp' : IsPullback z' c''.g c'.g h)
    (sj : IsPullback x c'.i c.i z) (sj' : IsPullback x' c''.i c'.i z') :
    ordinaryH P.Coefficient c c'' (h ≫ g) (x' ≫ x) (z' ≫ z)
        (sp'.paste_horiz sp) (sj'.paste_horiz sj) =
      paste (ordinaryGComp P.Coefficient h g) (ordinaryGComp P.Coefficient x' x)
        (ordinaryH P.Coefficient c c' g x z sp sj)
        (ordinaryH P.Coefficient c' c'' h x' z' sp' sj') := by
  let : QuasiCompact c.i := c.quasiCompact_openImmersion fqc
  exact (ordinaryPasting P.Coefficient c c' c'' g h x x' z z' sp sp' sj sj').2.2

/-- Vertical pasting is an equality of the ordinary constituent transformations.
Source: Stacks 0F7J; blueprint constituent assembly
(blueprint: lem-pur-isomorphism-finite-exchange-coherence).
Proof: use normalizedProperOpenCalculus base-change for the central square of T,
whiskered by the outer proper image and inner open extension. Mate-pasting combines
proper exchanges, and open-beta-normalization combines the open comparisons.
This gives compositionPastingCoherence before evaluation. Evaluate on constant
strict towers: tower-mate-evaluation-scalars preserves the specified adjunctions,
clopen projector, mates and compositors. No faithfulness of evaluation is used. -/
theorem vertical {Z X' Y' Z' : Scheme.{u}} {h : Y ⟶ Z}
    {f' : X' ⟶ Y'} {h' : Y' ⟶ Z'}
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    [X'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [IsSeparated (X' ↘ Spec (.of P.field.k))]
    [Y'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    [IsSeparated (Y' ↘ Spec (.of P.field.k))]
    [Z'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z' ↘ Spec (.of P.field.k))]
    [IsSeparated (Z' ↘ Spec (.of P.field.k))]
    [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (T : Compactification.Triangle f h) (T' : Compactification.Triangle f' h')
    [QuasiCompact T.cf.i] [QuasiCompact T.cg.i] [QuasiCompact T.q]
    [QuasiCompact T'.cf.i] [QuasiCompact T'.cg.i] [QuasiCompact T'.q]
    (x : X' ⟶ X) (y : Y' ⟶ Y) (g : Z' ⟶ Z) [IsIso g]
    (A : CompositionBaseChange T T' x y g) :
    Functor.whiskerRight (composition P.Coefficient T) (ordinaryG P.Coefficient g) ≫
        ordinaryH P.Coefficient T.cfg T'.cfg g x A.s A.cfg_g A.cfg_i =
      Functor.whiskerLeft (ordinaryJ P.Coefficient T.cf.i ⋙ ordinaryR P.Coefficient T.cf.g)
          (ordinaryH P.Coefficient T.cg T'.cg g y A.t A.cg_g A.cg_i) ≫
        Functor.whiskerRight
          (ordinaryH P.Coefficient T.cf T'.cf y x A.d A.cf_g A.cf_i)
          (ordinaryJ P.Coefficient T'.cg.i ⋙ ordinaryR P.Coefficient T'.cg.g) ≫
        Functor.whiskerLeft (ordinaryG P.Coefficient x) (composition P.Coefficient T') := by
  sorry

end Geometry
private theorem leftUniq_hom_of_conjugate
    {C D : Type*} [Category* C] [Category* D]
    {L L' : C ⥤ D} {R R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (d : R ≅ R') (γ : L' ⟶ L)
    (hγ : conjugateEquiv a b γ = d.hom) :
    ((b.ofNatIsoRight d.symm).leftAdjointUniq a).hom = γ := by
  ext N
  apply ((b.ofNatIsoRight d.symm).homEquiv N _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_unit]
  have hu := unit_conjugateEquiv a b γ N
  rw [hγ] at hu
  simp only [← hu, Category.assoc, Iso.symm_hom, Iso.hom_inv_id_app]
  erw [Category.comp_id]

private theorem scalarPull_eq_reduction {R S : PurCompactSupport.Coefficients.{u}}
    (a : PurCompactSupport.Change R S) {U V : Scheme.{u}} (f : U ⟶ V) :
    (PurCompactSupport.scalarPull a f).hom =
      proEtaleReductionPullbackInv f (R.ring V) (S.ring V) (R.ring U) (S.ring U)
        (a.map V) (a.map U) (R.pull f) (S.pull f) (a.square f) := by
  let av := pbcDerivedScalarAdjunction (a.map V)
  let au := pbcDerivedScalarAdjunction (a.map U)
  let ar := proEtaleRingDerivedAdjunction f (R.ring V) (R.ring U) (R.pull f)
  let az := proEtaleRingDerivedAdjunction f (S.ring V) (S.ring U) (S.pull f)
  let b := proEtaleRingRestrictionDerivedPullback f
    (R.ring V) (S.ring V) (R.ring U) (S.ring U)
    (a.map V) (a.map U) (R.pull f) (S.pull f) (a.square f)
  let d := proEtaleRingRestrictionDerivedDirectImage f
    (R.ring V) (S.ring V) (R.ring U) (S.ring U)
    (a.map V) (a.map U) (R.pull f) (S.pull f) (a.square f)
  let α := TwoSquare.mk _ _ _ _ b.inv
  have hmate : (mateEquiv az ar α).natTrans = d.hom := by
    apply NatTrans.ext
    funext N
    have h := (proEtaleRingSheafChangeAdjunction
      f (R.ring V) (S.ring V) (R.ring U) (S.ring U)
      (a.map V) (a.map U) (R.pull f) (S.pull f) (a.square f)).2.2
      ((proEtaleRingDerivedDirectImage f (S.ring V) (S.ring U) (S.pull f)).obj N)
      N (az.counit.app N)
    have hid : az.homEquiv _ _ (az.counit.app N) = 𝟙 _ := by
      rw [← az.homEquiv_symm_id N]
      exact (az.homEquiv _ _).apply_symm_apply _
    change ar.homEquiv _ _ (b.inv.app _ ≫
      (proEtaleRingRestrictScalars (a.map U)).mapDerivedCategory.map
        (az.counit.app N)) =
      (proEtaleRingRestrictScalars (a.map V)).mapDerivedCategory.map
        (az.homEquiv _ _ (az.counit.app N)) ≫ d.hom.app N at h
    rw [hid, CategoryTheory.Functor.map_id, Category.id_comp] at h
    rw [← h]
    simp only [α, mateEquiv_apply, TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app,
      Functor.comp_obj, Functor.comp_map, Functor.rightUnitor_inv_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.leftUnitor_hom_app, Category.id_comp,
      Adjunction.homEquiv_unit, Functor.map_comp]
    erw [Category.comp_id]
  let γ := (mateEquiv av au).symm α
  have hc : conjugateEquiv (av.comp az) (ar.comp au) γ.natTrans = d.hom := by
    rw [← iterated_mateEquiv_conjugateEquiv av au ar az γ,
      (mateEquiv av au).apply_symm_apply α]
    exact hmate
  exact leftUniq_hom_of_conjugate (av.comp az) (ar.comp au) d γ.natTrans hc

private theorem scalarPull_ulift {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (f : U ⟶ V) :
    (PurCompactSupport.scalarPull
      (constantChange (RingHom.ulift.{u + 1, u + 1} φ)) f).hom =
      (ProEtale.directImageScalarPullbackIso φ f).inv := by
  exact scalarPull_eq_reduction _ _

private theorem scalarPull_cube {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {V W S T : Scheme.{u}}
    (z : V ⟶ W) (p' : V ⟶ S) (p : W ⟶ T) (g : S ⟶ T)
    (sp : IsPullback z p' p g)
    (N : DerivedCategory (Modules (ULift.{u + 1} A) T)) :
    (pbcDerivedExtend ((constantChange (RingHom.ulift.{u + 1, u + 1} φ)).map V)).map
        ((ordinarySquare (ULift.{u + 1} A) z p' p g sp.w).hom.app N) ≫
      (PurCompactSupport.scalarPull
        (constantChange (RingHom.ulift.{u + 1, u + 1} φ)) z).hom.app
        ((ordinaryG (ULift.{u + 1} A) p).obj N) ≫
      (ordinaryG (ULift.{u + 1} B) z).map
        ((PurCompactSupport.scalarPull
          (constantChange (RingHom.ulift.{u + 1, u + 1} φ)) p).hom.app N) =
    (PurCompactSupport.scalarPull
      (constantChange (RingHom.ulift.{u + 1, u + 1} φ)) p').hom.app
        ((ordinaryG (ULift.{u + 1} A) g).obj N) ≫
      (ordinaryG (ULift.{u + 1} B) p').map
        ((PurCompactSupport.scalarPull
          (constantChange (RingHom.ulift.{u + 1, u + 1} φ)) g).hom.app N) ≫
      (ordinarySquare (ULift.{u + 1} B) z p' p g sp.w).hom.app
        ((pbcDerivedExtend ((constantChange (RingHom.ulift.{u + 1, u + 1} φ)).map T)).obj N) := by
  let sq : ChosenCartesianSquare z p' p g :=
    { toCommSq := sp.toCommSq
      isoPullback := sp.isoPullback
      hom_fst := sp.isoPullback_hom_fst
      hom_snd := sp.isoPullback_hom_snd }
  have hc := ProEtale.DirectScalar.scalarTensorPullbackSquare φ z p' p g sq N
  simp only [← scalarPull_ulift] at hc
  change
    (pbcDerivedExtend ((constantChange
      (RingHom.ulift.{u + 1, u + 1} φ)).map V)).map
        ((ordinarySquare (ULift.{u + 1} A) z p' p g sp.w).inv.app N) ≫
      (PurCompactSupport.scalarPull (constantChange (RingHom.ulift φ)) p').hom.app
        ((ordinaryG (ULift.{u + 1} A) g).obj N) ≫
      (ordinaryG (ULift.{u + 1} B) p').map
        ((PurCompactSupport.scalarPull (constantChange (RingHom.ulift φ)) g).hom.app N) =
    (PurCompactSupport.scalarPull (constantChange (RingHom.ulift φ)) z).hom.app
        ((ordinaryG (ULift.{u + 1} A) p).obj N) ≫
      (ordinaryG (ULift.{u + 1} B) z).map
        ((PurCompactSupport.scalarPull (constantChange (RingHom.ulift φ)) p).hom.app N) ≫
      (ordinarySquare (ULift.{u + 1} B) z p' p g sp.w).inv.app
        ((pbcDerivedExtend ((constantChange (RingHom.ulift φ)).map T)).obj N) at hc
  apply (cancel_epi
    ((pbcDerivedExtend ((constantChange (RingHom.ulift.{u + 1, u + 1} φ)).map V)).map
      ((ordinarySquare (ULift.{u + 1} A) z p' p g sp.w).inv.app N))).1
  simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  have hc' := congrArg (fun f ↦ f ≫
    (ordinarySquare (ULift.{u + 1} B) z p' p g sp.w).hom.app
      ((pbcDerivedExtend ((constantChange
        (RingHom.ulift.{u + 1, u + 1} φ)).map T)).obj N)) hc
  simp only [Category.assoc, Iso.inv_hom_id_app] at hc'
  erw [Category.comp_id] at hc'
  simpa only [Category.assoc] using hc'.symm

private theorem coefficientMateEquations (P : PurityFiniteSetting.{u}) :
    coefficientOperationMateEquations.{u} := by
  let : ∀ x : (∅ : Scheme.{u}), Invertible (P.coefficients.l : (∅ : Scheme.{u}).residueField x) :=
    fun x ↦ PEmpty.elim x
  intro R S a X Y f
  exact (basicOperationCoefficientCoherence.{u, u, u, u, u, u, u}
    P.coefficients.l P.extension P.coefficients.Qbar
    (∅ : Scheme.{u}) (∅ : Scheme.{u}) (𝟙 _)).1 a f

private theorem inverse_open_scalar_unit
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {J : C ⥤ D} {G : D ⥤ C} {J' : C' ⥤ D'} {G' : D' ⥤ C'}
    {S : C ⥤ C'} {R : C' ⥤ C} {T : D ⥤ D'} {Q : D' ⥤ D}
    (a : J ⊣ G) (a' : J' ⊣ G') (b : S ⊣ R) (b' : T ⊣ Q)
    (q : G' ⋙ R ≅ Q ⋙ G) (r : R ⋙ J ⟶ J' ⋙ Q)
    (l : G ⋙ S ⟶ T ⋙ G') (d : J ⋙ T ≅ S ⋙ J')
    (hr : ∀ N, a.unit.app (R.obj N) ≫ G.map (r.app N) =
      R.map (a'.unit.app N) ≫ q.hom.app (J'.obj N))
    (hl : ∀ N, G.map (b'.unit.app N) ≫ q.inv.app (T.obj N) =
      b.unit.app (G.obj N) ≫ R.map (l.app N))
    (hd : ∀ M, J.map (b.unit.app M) ≫ r.app (S.obj M) =
      b'.unit.app (J.obj M) ≫ Q.map (d.hom.app M))
    (M : C) :
    a'.unit.app (S.obj M) ≫ G'.map (d.inv.app M) =
      S.map (a.unit.app M) ≫ l.app (J.obj M) := by
  apply (cancel_mono (G'.map (d.hom.app M))).1
  rw [Category.assoc, ← G'.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  apply (b.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  have hn := b.unit.naturality (a.unit.app M)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [reassoc_of% hn.symm, ← reassoc_of% (hl (J.obj M))]
  have hq := q.inv.naturality (d.hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hq
  rw [← hq, ← G.map_comp_assoc, ← hd]
  rw [G.map_comp]
  have ha := a.unit.naturality (b.unit.app M)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at ha
  simp only [Category.assoc]
  rw [reassoc_of% ha.symm, reassoc_of% (hr (S.obj M))]
  simp only [Iso.hom_inv_id_app]
  erw [Category.comp_id]

private theorem scalar_open_restriction_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U W : Scheme.{u}} (j : U ⟶ W) [IsOpenImmersion j]
    (N : DerivedCategory (Modules B U)) :
    (ordinaryJAdj A j).unit.app ((MateEvaluationScalars.Res φ U).obj N) ≫
        (ordinaryG A j).map
          ((PurCompactSupport.openRestriction (constantChange φ) j).hom.app N) =
      (MateEvaluationScalars.Res φ U).map ((ordinaryJAdj B j).unit.app N) ≫
        (MateEvaluationScalars.scalarG φ j).hom.app ((ordinaryJ B j).obj N) := by
  let : IsIso (MateEvaluationScalars.scalarJInv φ j) :=
    MateEvaluationScalars.scalarJInv_isIso φ j
  have hm : PurCompactSupport.openRestrictionMap (constantChange φ) j =
      MateEvaluationScalars.scalarJInv φ j := by
    simp only [PurCompactSupport.openRestrictionMap, MateEvaluationScalars.scalarJInv,
      MateEvaluationScalars.scalarGModule, Iso.symm_hom, asIso_inv]
    rfl
  have hs : Functor.mapDerivedCategoryNatIso
      (asIso (MateEvaluationScalars.scalarJInv φ j)).symm =
      (Functor.mapDerivedCategoryNatIso
        (asIso (MateEvaluationScalars.scalarJInv φ j))).symm :=
    Iso.ext (Functor.mapDerivedCategoryNatIso_symm _)
  have hr : (PurCompactSupport.openRestriction (constantChange φ) j).hom =
      (MateEvaluationScalars.scalarJ φ j).inv := by
    simp only [PurCompactSupport.openRestriction, hm, MateEvaluationScalars.scalarJ,
      MateEvaluationScalars.scalarJModule, Functor.mapDerivedCategorySquareIso,
      Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv]
    rw [hs]
    simp only [Iso.symm_inv, Category.assoc]
    rfl
  rw [hr]
  apply (cancel_mono ((ordinaryG A j).map
    ((MateEvaluationScalars.scalarJ φ j).hom.app N))).1
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  simpa only [ordinaryJAdj, exactAdj, MateEvaluationScalars.dJAdj] using
    ((MateEvaluationScalars.scalar_open_normalized φ j).2.1 N).symm

private theorem scalar_open_inverse_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U W : Scheme.{u}} (j : U ⟶ W) [IsOpenImmersion j]
    (d : ordinaryJ A j ⋙ pbcDerivedExtend ((constantChange φ).map W) ≅
      pbcDerivedExtend ((constantChange φ).map U) ⋙ ordinaryJ B j)
    (he : d.hom = PurCompactSupport.openComparison (constantChange φ) j)
    (M : DerivedCategory (Modules A U)) :
    (ordinaryJAdj B j).unit.app
        ((pbcDerivedExtend ((constantChange φ).map U)).obj M) ≫
      (ordinaryG B j).map
        (d.inv.app M) =
    (pbcDerivedExtend ((constantChange φ).map U)).map ((ordinaryJAdj A j).unit.app M) ≫
      (PurCompactSupport.scalarPull (constantChange φ) j).hom.app
        ((ordinaryJ A j).obj M) := by
  let a := constantChange φ
  let av := pbcDerivedScalarAdjunction (a.map W)
  let au := pbcDerivedScalarAdjunction (a.map U)
  let q := MateEvaluationScalars.scalarG φ j
  have hl (N : DerivedCategory (Modules A W)) :
      (ordinaryG A j).map (av.unit.app N) ≫ q.inv.app
        ((pbcDerivedExtend (a.map W)).obj N) =
      au.unit.app ((ordinaryG A j).obj N) ≫
        (MateEvaluationScalars.Res φ U).map
          ((PurCompactSupport.scalarPull a j).hom.app N) := by
    rw [scalarPull_eq_reduction]
    exact unit_mateEquiv_symm av au (TwoSquare.mk _ _ _ _ q.inv) N
  have hd (N : DerivedCategory (Modules A U)) :
      (ordinaryJ A j).map (au.unit.app N) ≫
          (PurCompactSupport.openRestriction a j).hom.app
            ((pbcDerivedExtend (a.map U)).obj N) =
        av.unit.app ((ordinaryJ A j).obj N) ≫
          (MateEvaluationScalars.Res φ W).map (d.hom.app N) := by
    rw [he]
    exact unit_mateEquiv_symm au av
      (TwoSquare.mk _ _ _ _ (PurCompactSupport.openRestriction a j).hom) N
  exact inverse_open_scalar_unit (ordinaryJAdj A j) (ordinaryJAdj B j) au av q
    (PurCompactSupport.openRestriction a j).hom (PurCompactSupport.scalarPull a j).hom
    d (scalar_open_restriction_unit φ j) hl hd M

private theorem rotated_iso_cube {C : Type*} [Category* C]
    {A B C₀ D E F : C} (a : A ≅ B) (b : B ≅ C₀) (c : C₀ ⟶ D)
    (d : A ⟶ E) (e : E ≅ F) (f : F ≅ D)
    (h : a.hom ≫ b.hom ≫ c = d ≫ e.hom ≫ f.hom) :
    c ≫ f.inv ≫ e.inv = b.inv ≫ a.inv ≫ d := by
  apply (cancel_epi (a.hom ≫ b.hom)).1
  simp only [Category.assoc]
  rw [reassoc_of% h]
  simp

private theorem iso_triple_of_inverse {C : Type*} [Category* C]
    {A B C₀ D E F : C} (a : A ≅ B) (b : B ≅ C₀) (c : C₀ ≅ D)
    (d : A ≅ E) (e : E ≅ F) (f : F ≅ D)
    (h : c.inv ≫ b.inv ≫ a.inv = f.inv ≫ e.inv ≫ d.inv) :
    a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.hom ≫ f.hom := by
  have he : (a ≪≫ b ≪≫ c) = (d ≪≫ e ≪≫ f) := by
    apply Iso.ext_inv
    simpa only [Iso.trans_inv, Category.assoc] using h
  exact congrArg Iso.hom he

attribute [local irreducible] PurCompactSupport.scalarPull PurCompactSupport.properComparison
  Functor.mapDerivedCategory Functor.leftAdjoint

section Coefficients
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (h : m ≤ P.level)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The counit-defined proper projection commutes with the actual proper exchange.
Source: Stacks 07A7, 0FPI; blueprint constituent assembly
(blueprint: lem-pur-isomorphism-finite-exchange-coherence).
Proof: ringed-derived-monoidal-comparisons gives the pull-comparison cube for the
quotient map. The two exchanges satisfy their defining counit equations. The
properComparison maps are the counit-defined coefficient projection mates by
coefficientOperationMateEquations. Apply coefficient_exchange_of_counit to that
cube. Neither proper coefficient map is inverted. -/
theorem properCoefficient {V W S T : Scheme.{u}}
    (z : V ⟶ W) (p' : V ⟶ S) (p : W ⟶ T) (g : S ⟶ T) [IsIso g]
    [IsProper p] [IsProper p'] (sp : IsPullback z p' p g)
    (K : DerivedCategory (Modules P.Coefficient W)) :
    (tensorQuotient P m hm h S).map ((ordinaryE P.Coefficient z p' p g sp.w).app K) ≫
        (PurCompactSupport.properComparison (constantChange (quotient P m hm h)) p').app
          ((ordinaryG P.Coefficient z).obj K) ≫
        (ordinaryR (lower P m hm).Coefficient p').map
          ((PurCompactSupport.scalarPull (constantChange (quotient P m hm h)) z).hom.app K) =
      (PurCompactSupport.scalarPull (constantChange (quotient P m hm h)) g).hom.app
          ((ordinaryR P.Coefficient p).obj K) ≫
        (ordinaryG (lower P m hm).Coefficient g).map
          ((PurCompactSupport.properComparison (constantChange (quotient P m hm h)) p).app K) ≫
        (ordinaryE (lower P m hm).Coefficient z p' p g sp.w).app
          ((tensorQuotient P m hm h W).obj K) := by
  let a := constantChange (quotient P m hm h)
  let φ : P.Ring →+* (lower P m hm).Ring := Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal P.coefficients.l P.extension P.level)
    (T := Padic.coefficientExtensionIdeal P.coefficients.l P.extension m)
    (Ideal.pow_le_pow_right h)
  have hc := scalarPull_cube (A := P.Ring) (B := (lower P m hm).Ring) φ
    z p' p g sp
  have hm₁ := (coefficientMateEquations P) a p
  have hm₂ := (coefficientMateEquations P) a p'
  have result := Adjunction.coefficient_exchange_of_counit
    (G := ordinaryG P.Coefficient g) (H := ordinaryG P.Coefficient z)
    (Ge := ordinaryG (lower P m hm).Coefficient g)
    (He := ordinaryG (lower P m hm).Coefficient z)
    (T₁ := tensorQuotient P m hm h T) (T₂ := tensorQuotient P m hm h W)
    (T₃ := tensorQuotient P m hm h S) (T₄ := tensorQuotient P m hm h V)
    (ordinaryAdj P.Coefficient p) (ordinaryAdj P.Coefficient p')
    (ordinaryAdj (lower P m hm).Coefficient p) (ordinaryAdj (lower P m hm).Coefficient p')
    (ordinarySquare P.Coefficient z p' p g sp.w).hom
    (ordinarySquare (lower P m hm).Coefficient z p' p g sp.w).hom
    (ordinaryE P.Coefficient z p' p g sp.w)
    (ordinaryE (lower P m hm).Coefficient z p' p g sp.w)
    (fun N ↦ mateEquiv_counit (ordinaryAdj P.Coefficient p)
      (ordinaryAdj P.Coefficient p')
      (TwoSquare.mk _ _ _ _ (ordinarySquare P.Coefficient z p' p g sp.w).hom) N)
    (fun N ↦ mateEquiv_counit (ordinaryAdj (lower P m hm).Coefficient p)
      (ordinaryAdj (lower P m hm).Coefficient p')
      (TwoSquare.mk _ _ _ _
        (ordinarySquare (lower P m hm).Coefficient z p' p g sp.w).hom) N)
    (PurCompactSupport.scalarPull a p) (PurCompactSupport.scalarPull a p')
    (PurCompactSupport.scalarPull a g).hom (PurCompactSupport.scalarPull a z).hom
    (PurCompactSupport.properComparison a p) (PurCompactSupport.properComparison a p')
    hm₁.1 hm₂.1 hc K
  exact result.symm

set_option backward.isDefEq.respectTransparency true in
/-- The unit-normalized open coefficient comparison commutes with the open exchange.
Source: Stacks 03DI; blueprint constituent assembly
(blueprint: lem-pur-isomorphism-finite-exchange-coherence).
Proof: open-tensor-normalization supplies the open coefficient comparison, normalized
by its open unit. Restrict both composites to the open: every beta and delta becomes
identity and both routes become the same scalar-pullback comparison. Ringed derived
monoidal coherence identifies the successive pullbacks. Full faithfulness of open
extension proves the equality before any constructibility restriction. -/
theorem openCoefficient {U' U W' W : Scheme.{u}}
    (x : U' ⟶ U) (j' : U' ⟶ W') (j : U ⟶ W) (z : W' ⟶ W) [IsIso z]
    [IsOpenImmersion j] [IsOpenImmersion j'] (sj : IsPullback x j' j z)
    (K : DerivedCategory (Modules P.Coefficient U)) :
    (tensorQuotient P m hm h W').map ((ordinaryBeta P.Coefficient x j' j z sj).hom.app K) ≫
        (PurCompactSupport.openComparison (constantChange (quotient P m hm h)) j').app
          ((ordinaryG P.Coefficient x).obj K) ≫
        (ordinaryJ (lower P m hm).Coefficient j').map
          ((PurCompactSupport.scalarPull (constantChange (quotient P m hm h)) x).hom.app K) =
      (PurCompactSupport.scalarPull (constantChange (quotient P m hm h)) z).hom.app
          ((ordinaryJ P.Coefficient j).obj K) ≫
        (ordinaryG (lower P m hm).Coefficient z).map
          ((PurCompactSupport.openComparison (constantChange (quotient P m hm h)) j).app K) ≫
        (ordinaryBeta (lower P m hm).Coefficient x j' j z sj).hom.app
          ((tensorQuotient P m hm h U).obj K) := by
  let a := constantChange (quotient P m hm h)
  let T (X : Scheme.{u}) := tensorQuotient P m hm h X
  have hδ : IsIso (PurCompactSupport.openComparison a j) :=
    (NatTrans.isIso_iff_isIso_app _).mpr
      (fun M ↦ PurCompactSupport.openComparison_isIso a j M)
  have hδ' : IsIso (PurCompactSupport.openComparison a j') :=
    (NatTrans.isIso_iff_isIso_app _).mpr
      (fun M ↦ PurCompactSupport.openComparison_isIso a j' M)
  let dj := @asIso _ _ _ _ (PurCompactSupport.openComparison a j) hδ
  let dj' := @asIso _ _ _ _ (PurCompactSupport.openComparison a j') hδ'
  let χ {V W : Scheme.{u}} (f : V ⟶ W) := PurCompactSupport.scalarPull a f
  let φ : P.Ring →+* (lower P m hm).Ring := Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal P.coefficients.l P.extension P.level)
    (T := Padic.coefficientExtensionIdeal P.coefficients.l P.extension m)
    (Ideal.pow_le_pow_right h)
  have hc := scalarPull_cube (A := P.Ring) (B := (lower P m hm).Ring) φ
    x j' j z sj
  have cube (N : DerivedCategory (Modules P.Coefficient W)) := rotated_iso_cube
    ((T U').mapIso ((ordinarySquare P.Coefficient x j' j z sj.w).app N))
    ((χ x).app ((ordinaryG P.Coefficient j).obj N))
    ((ordinaryG (lower P m hm).Coefficient x).map ((χ j).hom.app N))
    ((χ j').hom.app ((ordinaryG P.Coefficient z).obj N))
    ((ordinaryG (lower P m hm).Coefficient j').mapIso ((χ z).app N))
    ((ordinarySquare (lower P m hm).Coefficient x j' j z sj.w).app ((T W).obj N))
    (hc N)
  have hi := Adjunction.openScalar_exchange_of_unit
    (ordinaryJAdj P.Coefficient j) (ordinaryJAdj (lower P m hm).Coefficient j)
    (ordinaryJAdj P.Coefficient j') (ordinaryJAdj (lower P m hm).Coefficient j')
    (T U) (T U') (T W) (T W')
    (ordinaryG P.Coefficient x) (ordinaryG (lower P m hm).Coefficient x)
    (ordinaryG P.Coefficient z) (ordinaryG (lower P m hm).Coefficient z)
    (χ z) (χ x)
    (ordinarySquare P.Coefficient x j' j z sj.w)
    (ordinarySquare (lower P m hm).Coefficient x j' j z sj.w)
    (χ j) (χ j')
    (ordinaryBeta P.Coefficient x j' j z sj).inv
    (ordinaryBeta (lower P m hm).Coefficient x j' j z sj).inv
    dj.inv dj'.inv
    (ordinaryBetaInv_unit P.Coefficient x j' j z sj)
    (ordinaryBetaInv_unit (lower P m hm).Coefficient x j' j z sj)
    (fun M ↦ scalar_open_inverse_unit (quotient P m hm h) j dj rfl M)
    (fun M ↦ scalar_open_inverse_unit (quotient P m hm h) j' dj' rfl M)
    cube K
  exact iso_triple_of_inverse
    ((T W').mapIso ((ordinaryBeta P.Coefficient x j' j z sj).app K))
    (dj'.app ((ordinaryG P.Coefficient x).obj K))
    ((ordinaryJ (lower P m hm).Coefficient j').mapIso ((χ x).app K))
    ((χ z).app ((ordinaryJ P.Coefficient j).obj K))
    ((ordinaryG (lower P m hm).Coefficient z).mapIso
      (dj.app K))
    ((ordinaryBeta (lower P m hm).Coefficient x j' j z sj).app ((T U).obj K)) hi

set_option linter.unusedVariables false in
/-- Quotient extension commutes with the specified finite compactification exchange.
Source: blueprint constituent assembly, Stacks 07A7 and 0FPI
(blueprint: lem-pur-isomorphism-finite-exchange-coherence).
Proof: write kappa=(P_m delta)(rho J_n), as in basicOperationsCoefficientReduction.
Expand each H as proper exchange followed by open beta. Apply properCoefficient at
J_n K, use naturality of rho with respect to beta, and apply openCoefficient. The
resulting two composites are exactly this square, with the same coefficient and
pullback identifications. All operations concern underlying ringed pro-etale topoi,
so no k-linearity of the isomorphisms is needed. -/
theorem coefficient {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    [X'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [IsSeparated (X' ↘ Spec (.of P.field.k))]
    [Y'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    [IsSeparated (Y' ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f')
    (g : Y' ⟶ Y) (x : X' ⟶ X) (z : c'.Z ⟶ c.Z) [IsIso g]
    (sp : IsPullback z c'.g c.g g) (sj : IsPullback x c'.i c.i z)
    (K : DerivedCategory (Modules P.Coefficient X))
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos X K) :
    (tensorQuotient P m hm h Y').map ((ordinaryH P.Coefficient c c' g x z sp sj).app K) ≫
        (PurCompactSupport.comparison (constantChange (quotient P m hm h)) c').app
          ((ordinaryG P.Coefficient x).obj K) ≫
        (ordinaryJ (lower P m hm).Coefficient c'.i ⋙
          ordinaryR (lower P m hm).Coefficient c'.g).map
          ((PurCompactSupport.scalarPull (constantChange (quotient P m hm h)) x).hom.app K) =
      (PurCompactSupport.scalarPull (constantChange (quotient P m hm h)) g).hom.app
          ((ordinaryJ P.Coefficient c.i ⋙ ordinaryR P.Coefficient c.g).obj K) ≫
        (ordinaryG (lower P m hm).Coefficient g).map
          ((PurCompactSupport.comparison (constantChange (quotient P m hm h)) c).app K) ≫
        (ordinaryH (lower P m hm).Coefficient c c' g x z sp sj).app
          ((tensorQuotient P m hm h X).obj K) := by
  have : IsIso z := sp.isIso_fst_of_isIso
  have he := properCoefficient P m hm h z c'.g c.g g sp
    ((ordinaryJ P.Coefficient c.i).obj K)
  have hb := openCoefficient P m hm h x c'.i c.i z sj K
  have hn := (ordinaryE (lower P m hm).Coefficient z c'.g c.g g sp.w).naturality
    ((PurCompactSupport.openComparison (constantChange (quotient P m hm h)) c.i).app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  simp only [ordinaryH, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.map_comp, PurCompactSupport.comparison_factorization,
    Functor.comp_obj, Functor.comp_map, Category.assoc]
  exact mapped_combine
    (PurCompactSupport.properComparison (constantChange (quotient P m hm h)) c'.g)
    ((ordinaryBeta P.Coefficient x c'.i c.i z sj).hom.app K)
    _ _ _ _ _ _ _ _ _ _ _ he hb hn.symm

end Coefficients

end WeilConjectures.FiniteExchangeCoherence
