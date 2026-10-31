/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicPurityScalarNaturality
public import WeilConjectures.AlgebraicGeometry.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.SmoothTrace
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.FiniteReductionComparisons
import all WeilConjectures.AlgebraicGeometry.AdicPurityScalarNaturalityData
import all WeilConjectures.AlgebraicGeometry.AdicPurityObjects
import all WeilConjectures.AlgebraicGeometry.FiniteReductionComparisons
import WeilConjectures.AlgebraicGeometry.IntegralPurityComparisonCocycles
import WeilConjectures.AlgebraicGeometry.IntegralPurityCounitReduction
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientSmoothPurity
import WeilConjectures.AlgebraicGeometry.IntegralResidueTor
import WeilConjectures.AlgebraicGeometry.FiniteReductionOfPurity

/-! # The specified integral purity family, inverse orientation and counit trace

Source: main-20261015, sec-six-functors/sk-thm-sf-package,
prop-functor-package.proof.md, clause (6)
(blueprint: lem-sf-normalized-integral-purity-trace).

The family is an argument of the interface, so every assertion concerns that same
normalized component. The ambient target realization is the recorded one, and the
counit is transported from its actual compact-support adjunction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 128

universe u
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence
  WeilConjectures.PurityFiniteSetting.smoothPurityTensor
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.NormalizedIntegralPurityTrace
open AdicPurityScalarNaturality
attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (r : ℕ) [SmoothOfRelativeDimension r f]
  (S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))
  (A : Data D C f r S) (E : Field D C)

/-- The specified family component in the actual integral reconstruction coordinates.
Source: clause (6), chosen gamma (blueprint: lem-sf-normalized-integral-purity-trace). -/
@[no_expose] def component (K : Cat D C E Y) :
    purAdicSource D C E.val f r K.obj ≅ purAdicTarget D C E.val f K.obj :=
  (finiteTorConstructibleIntegral C.l E.val X).ι.mapIso ((A.gamma E).app K) ≪≫
    (A.targetRealization E).app K

/-- The actual exceptional counit, transported by the specified target realization.
Source: clause (6), epsilon_R (blueprint: lem-sf-normalized-integral-purity-trace). -/
@[no_expose] def counit (K : Cat D C E Y) :
    (PurCompactSupport.image (PurCompactSupport.completed C.l E.val)
      (integralExceptionalCompactification D f)).obj
        (purAdicTarget D C E.val f K.obj) ⟶ K.obj :=
  (PurCompactSupport.image (PurCompactSupport.completed C.l E.val)
      (integralExceptionalCompactification D f)).map
        ((A.targetRealization E).inv.app K) ≫
    (S.ring.left (integralExceptionalCompactification D f)
      (.integral (fieldStage D C E))).inv.app ((target D C f S E).obj K) ≫
    (finiteTorConstructibleIntegral C.l E.val Y).ι.map
      ((operation D C f S E).adjunction.counit.app K)

/-- Compact support of this very gamma followed by the actual exceptional counit.
Source: clause (6), t_R (blueprint: lem-sf-normalized-integral-purity-trace). -/
@[no_expose] def trace (K : Cat D C E Y) :
    (PurCompactSupport.image (PurCompactSupport.completed C.l E.val)
      (integralExceptionalCompactification D f)).obj
        (purAdicSource D C E.val f r K.obj) ⟶ K.obj :=
  (PurCompactSupport.image (PurCompactSupport.completed C.l E.val)
    (integralExceptionalCompactification D f)).map (component D C f r S A E K).hom ≫
    counit D C f r S A E K

attribute [local irreducible] Padic.coefficientExtensionIdeal

private def quotientTower : ℕᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj n := .of (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E.val (n.unop + 1)))
  map {i j} f := CommRingCat.ofHom
    (Ideal.Quotient.factor
      (S := Padic.coefficientExtensionIdeal C.l E.val (i.unop + 1))
      (T := Padic.coefficientExtensionIdeal C.l E.val (j.unop + 1))
      (by
        unfold Padic.coefficientExtensionIdeal
        exact Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom f.unop) 1))).ulift
  map_id n := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro ⟨x⟩
    exact congrArg ULift.up (DFunLike.congr_fun Ideal.Quotient.factor_eq x)
  map_comp {i j k} f g := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro ⟨x⟩
    have h₁ : Padic.coefficientExtensionIdeal C.l E.val (i.unop + 1) ≤
        Padic.coefficientExtensionIdeal C.l E.val (j.unop + 1) := by
      unfold Padic.coefficientExtensionIdeal
      exact Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom f.unop) 1)
    have h₂ : Padic.coefficientExtensionIdeal C.l E.val (j.unop + 1) ≤
        Padic.coefficientExtensionIdeal C.l E.val (k.unop + 1) := by
      unfold Padic.coefficientExtensionIdeal
      exact Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom g.unop) 1)
    exact congrArg ULift.up (Ideal.Quotient.factor_comp_apply h₁ h₂ x).symm

private theorem coefficientTower_map (W : Scheme.{u}) (m n : ℕ) (h : m ≤ n) :
    (integralCoefficientSheafSystem C.l E.val W).map (homOfLE h).op =
      ((constantSheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}) ⋙
        sheafCompose _ (forget₂ CommRingCat RingCat)).map
          ((quotientTower D C E).map (homOfLE h).op) := by
  let t : integralCoefficientSheafSystem C.l E.val W ⟶ quotientTower D C E ⋙
      constantSheaf _ _ ⋙ sheafCompose _ (forget₂ CommRingCat RingCat) :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (fun n ↦ by
      simp only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ,
        Functor.comp_map]
      with_unfolding_all
        exact (Category.comp_id _).trans (Category.id_comp _).symm)
  exact (Category.comp_id _).symm.trans ((t.naturality (homOfLE h).op).trans
    (Category.id_comp _))

/-- The completed coefficient projections commute with every finite quotient.
Source: clause (6), tensor associators of successive reduction
(blueprint: lem-sf-normalized-integral-purity-trace).
Proof: the completed coefficient sheaf is the inverse limit of the quotient sheaves.
Its cone naturality gives the equality for successive projections. Compose these
identities from n to m; quotient induction identifies the composite quotient map
with finiteReductionRingHom. At m=n both maps are the identity quotient. -/
theorem quotientProjection (W : Scheme.{u}) (n m : ℕ) (h : m ≤ n) :
    (PurCompactSupport.reduction C.l E.val (n + 1) (Nat.succ_pos n)).map W ≫
      Scheme.proEtaleConstantRingMap (T := W)
        ((purAdicFiniteSetting D C E.val n).finiteReductionRingHom
          (m + 1) (Nat.succ_pos m) (Nat.succ_le_succ h)) =
    (PurCompactSupport.reduction C.l E.val (m + 1) (Nat.succ_pos m)).map W := by
  dsimp only [PurCompactSupport.reduction, PurCompactSupport.projection]
  erw [eqToHom_refl, Category.comp_id, eqToHom_refl, Category.comp_id]
  apply (sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map_injective
  change limit.π (integralCoefficientSheafSystem C.l E.val W) (Opposite.op n) ≫
    ((constantSheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}) ⋙
      sheafCompose _ (forget₂ CommRingCat RingCat)).map
        ((quotientTower D C E).map (homOfLE h).op) = _
  erw [← coefficientTower_map D C E W m n h]
  with_unfolding_all
    exact limit.w _ (homOfLE h).op


/-- The canonical tensor associator from iterated reduction to direct reduction.
The bridges and tensor composition are normalized by the scalar adjunction units.
Source: clause (6), successive quotients
(blueprint: lem-sf-normalized-integral-purity-trace). -/
@[no_expose] def reductionComposition (W : Scheme.{u}) (n m : ℕ) (h : m ≤ n) :
    scalarReductionDerivedExtension C.l E.val W n ⋙
        (purAdicFiniteSetting D C E.val n).finiteReduction
          (m + 1) (Nat.succ_pos m) (Nat.succ_le_succ h) W ≅
      scalarReductionDerivedExtension C.l E.val W m :=
  Functor.isoWhiskerRight (reductionBridge D C E W n) _ ≪≫
    PurCompactSupport.tensorComposition
      ((PurCompactSupport.reduction C.l E.val (n + 1) (Nat.succ_pos n)).map W)
      (Scheme.proEtaleConstantRingMap (T := W)
        ((purAdicFiniteSetting D C E.val n).finiteReductionRingHom
          (m + 1) (Nat.succ_pos m) (Nat.succ_le_succ h)))
      ((PurCompactSupport.reduction C.l E.val (m + 1) (Nat.succ_pos m)).map W)
      (quotientProjection D C E W n m h) ≪≫
    (reductionBridge D C E W m).symm

/-- The canonical support comparison in the reconstruction's reduction coordinates.
Source: clause (6), c_N (blueprint: lem-sf-normalized-integral-purity-trace). -/
@[no_expose] def supportComparison
    (N : DerivedCategory (scalarReductionSource C.l E.val X)) (n : ℕ) :
    (scalarReductionDerivedExtension C.l E.val Y n).obj
        ((PurCompactSupport.image (PurCompactSupport.completed C.l E.val)
          (integralExceptionalCompactification D f)).obj N) ⟶
      ((purAdicFiniteSetting D C E.val n).smoothCompactSupport f).obj
        ((scalarReductionDerivedExtension C.l E.val X n).obj N) :=
  (reductionBridge D C E Y n).hom.app _ ≫
  (PurCompactSupport.comparison.{u}
    (PurCompactSupport.reduction C.l E.val (n + 1) (Nat.succ_pos n))
    (integralExceptionalCompactification D f)).app N ≫
  (PurCompactSupport.finiteImageIso.{u} C.l E.val n
    (integralExceptionalCompactification D f)).hom.app _ ≫
  ((purAdicFiniteSetting D C E.val n).smoothCompactSupport f).map
    ((reductionBridge D C E X n).inv.app N)

attribute [local irreducible] reductionComposition supportComparison
  PurityFiniteSetting.finiteReductionSourceComparison
  PurityFiniteSetting.finiteReductionExceptionalComparison
  PurityFiniteSetting.finiteReductionCompactSupportComparison

-- The quotient squares retain the direct and iterated tensor presentations.
set_option maxHeartbeats 400000 in
-- The three quotient squares retain the actual tensor associators.
/-- Cocycle equations of the actual source, exceptional and support comparisons.
Source: clause (6), compatibility with further quotients
(blueprint: lem-sf-normalized-integral-purity-trace). -/
@[no_expose] def QuotientEquations (K : Cat D C E Y) : Prop :=
  ∀ (n m : ℕ) (h : m ≤ n),
    ((purAdicFiniteSetting D C E.val n).finiteReduction
      (m + 1) (Nat.succ_pos m) (Nat.succ_le_succ h) X).map
        (purAdicSourceReduction D C E.val f r K.obj K.property n) ≫
      ((purAdicFiniteSetting D C E.val n).finiteReductionSourceComparison
        (m + 1) (Nat.succ_pos m) (Nat.succ_le_succ h) f r _).hom ≫
      ((purAdicFiniteSetting D C E.val m).compositionShiftedPullback f r).map
        ((reductionComposition D C E Y n m h).hom.app K.obj) =
      (reductionComposition D C E X n m h).hom.app
          (purAdicSource D C E.val f r K.obj) ≫
        purAdicSourceReduction D C E.val f r K.obj K.property m ∧
    ((purAdicFiniteSetting D C E.val n).finiteReduction
      (m + 1) (Nat.succ_pos m) (Nat.succ_le_succ h) X).map
        (purAdicTargetReduction D C E.val f r K.obj K.property n) ≫
      (purAdicFiniteSetting D C E.val n).finiteReductionExceptionalComparison
        (m + 1) (Nat.succ_pos m) (Nat.succ_le_succ h) f r _
          (purAdicReductionFiniteTor D C E.val Y K.obj K.property n) ≫
      ((purAdicFiniteSetting D C E.val m).compositionExceptional f).map
        ((reductionComposition D C E Y n m h).hom.app K.obj) =
      (reductionComposition D C E X n m h).hom.app
          (purAdicTarget D C E.val f K.obj) ≫
        purAdicTargetReduction D C E.val f r K.obj K.property m ∧
    ∀ N : DerivedCategory (scalarReductionSource C.l E.val X),
      N = purAdicSource D C E.val f r K.obj ∨ N = purAdicTarget D C E.val f K.obj →
      ((purAdicFiniteSetting D C E.val n).finiteReduction
        (m + 1) (Nat.succ_pos m) (Nat.succ_le_succ h) Y).map
          (supportComparison D C f E N n) ≫
        (purAdicFiniteSetting D C E.val n).finiteReductionCompactSupportComparison
          (m + 1) (Nat.succ_pos m) (Nat.succ_le_succ h) f _ ≫
        ((purAdicFiniteSetting D C E.val m).smoothCompactSupport f).map
          ((reductionComposition D C E X n m h).hom.app N) =
        (reductionComposition D C E Y n m h).hom.app
            ((PurCompactSupport.image (PurCompactSupport.completed C.l E.val)
              (integralExceptionalCompactification D f)).obj N) ≫
          supportComparison D C f E N m

attribute [local irreducible] QuotientEquations

-- Retain all four finite comparison squares in their original dependent coordinates.
set_option maxHeartbeats 400000 in
-- Elaborate the four finite squares with their full coefficient endpoints.
/-- All further finite quotient equations, including inverse purity and the counit.
The finite comparisons are the independently normalized pullback/twist, support and
exceptional-adjoint comparisons, also for m equal to the starting exponent.
Source: clause (6), successive finite quotients
(blueprint: lem-sf-normalized-integral-purity-trace). -/
@[no_expose] def FiniteEquations (K : Cat D C E Y) (n : ℕ) : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n + 1),
    ∃ e : (purAdicFiniteArrow D C E.val f r K.obj K.property n).left ≅
        (purAdicFiniteArrow D C E.val f r K.obj K.property n).right,
      e.hom = (purAdicFiniteArrow D C E.val f r K.obj K.property n).hom ∧
      ∃ e' : _ ≅ _,
        e'.hom = (PurityFiniteSetting.smoothPurityMap
          ((purAdicFiniteSetting D C E.val n).finiteReductionSetting m hm) f r
            (((purAdicFiniteSetting D C E.val n).finiteReduction m hm hmn Y).obj
              ((scalarReductionDerivedExtension C.l E.val Y n).obj K.obj))
            ((purAdicFiniteSetting D C E.val n).finiteReduction_preserves_ctf m hm hmn Y
              _ (purAdicReductionFiniteTor D C E.val Y K.obj K.property n))) ∧
        ((purAdicFiniteSetting D C E.val n).finiteReduction m hm hmn X).map e.hom ≫
            (purAdicFiniteSetting D C E.val n).finiteReductionExceptionalComparison
              m hm hmn f r _ (purAdicReductionFiniteTor D C E.val Y K.obj K.property n) =
          ((purAdicFiniteSetting D C E.val n).finiteReductionSourceComparison
            m hm hmn f r _).hom ≫ e'.hom ∧
        ((purAdicFiniteSetting D C E.val n).finiteReduction m hm hmn X).map e.inv ≫
            ((purAdicFiniteSetting D C E.val n).finiteReductionSourceComparison
              m hm hmn f r _).hom =
          (purAdicFiniteSetting D C E.val n).finiteReductionExceptionalComparison
            m hm hmn f r _ (purAdicReductionFiniteTor D C E.val Y K.obj K.property n) ≫
              e'.inv ∧
        ((purAdicFiniteSetting D C E.val n).finiteReduction m hm hmn Y).map
            ((purAdicFiniteSetting D C E.val n).coefficientValuedSmoothTrace f r _
              (purAdicReductionFiniteTor D C E.val Y K.obj K.property n)) =
          (purAdicFiniteSetting D C E.val n).finiteReductionCompactSupportComparison
            m hm hmn f _ ≫
          (PurityFiniteSetting.smoothCompactSupport
            ((purAdicFiniteSetting D C E.val n).finiteReductionSetting m hm) f).map
              ((purAdicFiniteSetting D C E.val n).finiteReductionSourceComparison
                m hm hmn f r _).hom ≫
          PurityFiniteSetting.coefficientValuedSmoothTrace
            ((purAdicFiniteSetting D C E.val n).finiteReductionSetting m hm) f r _
              ((purAdicFiniteSetting D C E.val n).finiteReduction_preserves_ctf m hm hmn Y
                _ (purAdicReductionFiniteTor D C E.val Y K.obj K.property n)) ∧
        (purAdicFiniteSetting D C E.val n).finiteReductionCompactSupportComparison
            m hm hmn f ((purAdicFiniteArrow D C E.val f r K.obj K.property n).right) ≫
          (PurityFiniteSetting.smoothCompactSupport
            ((purAdicFiniteSetting D C E.val n).finiteReductionSetting m hm) f).map
              ((purAdicFiniteSetting D C E.val n).finiteReductionExceptionalComparison
                m hm hmn f r _ (purAdicReductionFiniteTor D C E.val Y K.obj K.property n)) ≫
          PurityFiniteSetting.smoothExceptionalCounit
            ((purAdicFiniteSetting D C E.val n).finiteReductionSetting m hm) f _ =
          ((purAdicFiniteSetting D C E.val n).finiteReduction m hm hmn Y).map
            ((purAdicFiniteSetting D C E.val n).smoothExceptionalCounit f
              ((scalarReductionDerivedExtension C.l E.val Y n).obj K.obj))

attribute [local irreducible] purAdicSource purAdicTarget component counit trace
  FiniteEquations scalarReductionDerivedExtension PurCompactSupport.image

private theorem inverseSquare {V W : Type*} [Category V] [Category W]
    (F : V ⥤ W) {H G : V} {H' G' : W} (g : H ≅ G) (e : H' ≅ G')
    (a : F.obj H ⟶ H') (b : F.obj G ⟶ G')
    (hf : F.map g.hom ≫ b = a ≫ e.hom) :
    F.map g.inv ≫ a = b ≫ e.inv := by
  apply (Iso.cancel_iso_hom_right _ _ e).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hf, ← Functor.map_comp_assoc]
  rw [Iso.inv_hom_id, F.map_id, Category.id_comp]

private theorem traceSquare
    {V W V' W' : Type*} [Category V] [Category W] [Category V'] [Category W']
    (P : V ⥤ W) (QX : V ⥤ V') (QY : W ⥤ W') (P' : V' ⥤ W')
    {H G : V} {H' G' : V'} {K : W}
    (g : H ⟶ G) (a : QX.obj H ⟶ H') (b : QX.obj G ⟶ G') (e : H' ⟶ G')
    (cH : QY.obj (P.obj H) ⟶ P'.obj (QX.obj H))
    (cG : QY.obj (P.obj G) ⟶ P'.obj (QX.obj G))
    (ε : P.obj G ⟶ K) (ε' : P'.obj G' ⟶ QY.obj K)
    (hn : QY.map (P.map g) ≫ cG = cH ≫ P'.map (QX.map g))
    (hf : QX.map g ≫ b = a ≫ e)
    (hc : QY.map ε = cG ≫ P'.map b ≫ ε') :
    QY.map (P.map g ≫ ε) =
      cH ≫ P'.map a ≫ P'.map e ≫ ε' := by
  rw [Functor.map_comp, hc, ← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, hf, Functor.map_comp]
  simp only [Category.assoc]

omit [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))] in
private theorem supportComparison_naturality
    {N M : DerivedCategory (scalarReductionSource C.l E.val X)} (a : N ⟶ M) (n : ℕ) :
    (scalarReductionDerivedExtension C.l E.val Y n).map
        ((PurCompactSupport.image (PurCompactSupport.completed C.l E.val)
          (integralExceptionalCompactification D f)).map a) ≫
        supportComparison D C f E M n =
      supportComparison D C f E N n ≫
        ((purAdicFiniteSetting D C E.val n).smoothCompactSupport f).map
          ((scalarReductionDerivedExtension C.l E.val X n).map a) := by
  let P := PurCompactSupport.image (PurCompactSupport.completed C.l E.val)
    (integralExceptionalCompactification D f)
  let Q := Scheme.pbcDerivedExtend
    ((PurCompactSupport.reduction C.l E.val (n + 1) (Nat.succ_pos n)).map X)
  let c := Functor.whiskerLeft P (reductionBridge D C E Y n).hom ≫
    (PurCompactSupport.comparison
      (PurCompactSupport.reduction C.l E.val (n + 1) (Nat.succ_pos n))
      (integralExceptionalCompactification D f)) ≫
    Functor.whiskerLeft Q (PurCompactSupport.finiteImageIso C.l E.val n
      (integralExceptionalCompactification D f)).hom ≫
    Functor.whiskerRight (reductionBridge D C E X n).inv
      ((purAdicFiniteSetting D C E.val n).smoothCompactSupport f)
  have hc (Z : DerivedCategory (scalarReductionSource C.l E.val X)) :
      c.app Z = supportComparison D C f E Z n := by
    unfold supportComparison
    rfl
  have hn := c.naturality a
  change (scalarReductionDerivedExtension C.l E.val Y n).map (P.map a) ≫ c.app M =
    c.app N ≫ ((purAdicFiniteSetting D C E.val n).smoothCompactSupport f).map
      ((scalarReductionDerivedExtension C.l E.val X n).map a) at hn
  rw [hc, hc] at hn
  exact hn

private theorem supportComparison_isIso
    (N : DerivedCategory (scalarReductionSource C.l E.val X))
    (hN : finiteTorConstructibleIntegral C.l E.val X N) (n : ℕ) :
    IsIso (supportComparison D C f E N n) := by
  have := PurCompactSupport.reductionComparison_isIso C.l E.val D C.different f
    (integralExceptionalCompactification D f) (n + 1) (Nat.succ_pos n) N hN
  let e1 := (reductionBridge D C E Y n).app
    ((PurCompactSupport.image (PurCompactSupport.completed C.l E.val)
      (integralExceptionalCompactification D f)).obj N)
  let e2 := asIso ((PurCompactSupport.comparison
    (PurCompactSupport.reduction C.l E.val (n + 1) (Nat.succ_pos n))
    (integralExceptionalCompactification D f)).app N)
  let e3 := (PurCompactSupport.finiteImageIso C.l E.val n
    (integralExceptionalCompactification D f)).app
      ((Scheme.pbcDerivedExtend
        ((PurCompactSupport.reduction C.l E.val (n + 1) (Nat.succ_pos n)).map X)).obj N)
  let e4 := ((purAdicFiniteSetting D C E.val n).smoothCompactSupport f).mapIso
    ((reductionBridge D C E X n).symm.app N)
  have he : (e1 ≪≫ e2 ≪≫ e3 ≪≫ e4).hom = supportComparison D C f E N n := by
    unfold supportComparison
    rfl
  rw [← he]
  exact (e1 ≪≫ e2 ≪≫ e3 ≪≫ e4).isIso_hom

private theorem finiteEquations (K : Cat D C E Y) (n : ℕ) :
    FiniteEquations D C f r E K n := by
  unfold FiniteEquations
  intro m hm hmn
  let P := purAdicFiniteSetting D C E.val n
  let L := (scalarReductionDerivedExtension C.l E.val Y n).obj K.obj
  have hL := purAdicReductionFiniteTor D C E.val Y K.obj K.property n
  have := P.isIso_smoothPurityMap f r L hL
  have := (P.finiteReductionSetting m hm).isIso_smoothPurityMap f r
    ((P.finiteReduction m hm hmn Y).obj L)
    (P.finiteReduction_preserves_ctf m hm hmn Y L hL)
  let e := asIso (P.smoothPurityMap f r L hL)
  let e' := asIso ((P.finiteReductionSetting m hm).smoothPurityMap f r
    ((P.finiteReduction m hm hmn Y).obj L)
    (P.finiteReduction_preserves_ctf m hm hmn Y L hL))
  have hf := P.finiteReductionOfPurity m hm hmn f r L hL
  refine ⟨e, rfl, e', rfl, hf, ?_,
    P.finiteReductionOfSmoothTrace m hm hmn f r L hL, ?_⟩
  · exact inverseSquare (P.finiteReduction m hm hmn X) e e'
      (P.finiteReductionSourceComparison m hm hmn f r L).hom
      (P.finiteReductionExceptionalComparison m hm hmn f r L hL) hf
  · have hb := (P.existsUnique_finiteReductionExceptionalComparison
      m hm hmn f r L hL).choose_spec.1
    with_unfolding_all
      exact hb

attribute [local irreducible] PurityFiniteSetting.smoothPurityMap
  PurityFiniteSetting.smoothExceptionalCounit PurityFiniteSetting.coefficientValuedSmoothTrace
  PurityFiniteSetting.smoothCompactSupport PurityFiniteSetting.compositionExceptional
  PurityFiniteSetting.compositionShiftedPullback

-- The statement retains the dependent finite coefficient and adjunction comparisons.
set_option maxHeartbeats 800000 in
-- Elaborate the dependent normalized family without unfolding its comparison proofs.
/-- Every constructible integral input lies in the uniform finite-Tor domain; the
specified normalized family gives its inverse orientation and actual counit trace,
with precisely the prescribed finite reductions and further-quotient equations.
Source: clause (6), integral reconstruction and finite smooth traces
(blueprint: lem-sf-normalized-integral-purity-trace).

Proof:
1. Bound the residue reduction in [a,b]. Integral residue Tor gives that same Tor
interval at every level, hence membership in finiteTorConstructibleIntegral.
2. Source finiteness gives the canonical a, exceptional-adjoint preservation gives b,
and integral compact support gives c. Finite-type dimension bounds apply also to the
empty scheme with bound zero. The exceptional comparison identifies actual counits.
3. Evaluate A.gamma, using A.targetRealization and A.finiteReductions: its forward
square is exactly the reconstruction square, and this very component is invertible.
4. Apply reduction to the inverse identities and multiply the forward square by
both inverses. This gives the displayed inverse-orientation equation.
5. Expand trace as P(gamma) followed by epsilon. Substitute the counit reduction,
move reduced gamma past c by naturality, and use the purity square. This is the
finite coefficient-valued smooth trace, as an equality of actual morphisms.
6. Under tensor reassociation, source, support and exceptional comparisons obey the
quotient cocycles. Finite reduction of purity and trace gives FiniteEquations at all
further quotients; exceptional adjoint mates identify the coefficient counits.
Identity quotients are included. No uniqueness of integral lifts is asserted. -/
theorem normalizedIntegralPurityTrace
    (L : DerivedCategory (scalarReductionSource C.l E.val Y))
    (hL : sfIntegralConstructible C.l E.val Y L) :
    (∀ (a b : ℤ), a ≤ b →
      (∀ i : ℤ, i ∈ proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension C.l E.val Y 0).obj L) → a ≤ i ∧ i ≤ b) →
      ∀ n : ℕ, HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing C.l E.val (n + 1))
        ((scalarReductionDerivedExtension C.l E.val Y n).obj L) a b) ∧
    ∃ hTor : finiteTorConstructibleIntegral C.l E.val Y L,
      QuotientEquations D C f r E ⟨L, hTor⟩ ∧
      ∀ n : ℕ,
        IsIso (purAdicSourceReduction D C E.val f r L hTor n) ∧
        IsIso (purAdicTargetReduction D C E.val f r L hTor n) ∧
        IsIso (supportComparison D C f E (purAdicSource D C E.val f r L) n) ∧
        IsIso (supportComparison D C f E (purAdicTarget D C E.val f L) n) ∧
        ∃ e : (purAdicFiniteArrow D C E.val f r L hTor n).left ≅
            (purAdicFiniteArrow D C E.val f r L hTor n).right,
          e.hom = (purAdicFiniteArrow D C E.val f r L hTor n).hom ∧
          (scalarReductionDerivedExtension C.l E.val X n).map
              (component D C f r S A E ⟨L, hTor⟩).hom ≫
              purAdicTargetReduction D C E.val f r L hTor n =
            purAdicSourceReduction D C E.val f r L hTor n ≫ e.hom ∧
          (scalarReductionDerivedExtension C.l E.val X n).map
              (component D C f r S A E ⟨L, hTor⟩).inv ≫
              purAdicSourceReduction D C E.val f r L hTor n =
            purAdicTargetReduction D C E.val f r L hTor n ≫ e.inv ∧
          (scalarReductionDerivedExtension C.l E.val Y n).map
              (trace D C f r S A E ⟨L, hTor⟩) =
            supportComparison D C f E (purAdicSource D C E.val f r L) n ≫
            ((purAdicFiniteSetting D C E.val n).smoothCompactSupport f).map
              (purAdicSourceReduction D C E.val f r L hTor n) ≫
            (purAdicFiniteSetting D C E.val n).coefficientValuedSmoothTrace f r
              ((scalarReductionDerivedExtension C.l E.val Y n).obj L)
              (purAdicReductionFiniteTor D C E.val Y L hTor n) ∧
          (scalarReductionDerivedExtension C.l E.val Y n).map
              (counit D C f r S A E ⟨L, hTor⟩) =
            supportComparison D C f E (purAdicTarget D C E.val f L) n ≫
            ((purAdicFiniteSetting D C E.val n).smoothCompactSupport f).map
              (purAdicTargetReduction D C E.val f r L hTor n) ≫
            (purAdicFiniteSetting D C E.val n).smoothExceptionalCounit f
              ((scalarReductionDerivedExtension C.l E.val Y n).obj L) ∧
          FiniteEquations D C f r E ⟨L, hTor⟩ n := by
  let := purAdicResidueInvertible D C Y
  have hres := integral_residue_tor D C.l C.different E.val Y
  refine ⟨hres.1 L hL, ?_⟩
  have hTor : finiteTorConstructibleIntegral C.l E.val Y L := by
    rw [← hres.2]
    exact hL
  refine ⟨hTor, ?_, ?_⟩
  · unfold QuotientEquations
    exact integralPurityComparisonCocycles D C f r E (quotientProjection D C E) ⟨L, hTor⟩
      (reductionComposition D C E) (by unfold reductionComposition; rfl)
      (supportComparison D C f E) (by unfold supportComparison; rfl)
  · intro n
    have hfinite := A.finiteReductions E ⟨L, hTor⟩ n
    have hsource := (purAdicReconstruction D C E.val f r L hTor).choose_spec.2.1
    have htarget := (purAdicReconstruction D C E.val f r L hTor).choose_spec.2.2.1
    have := (purAdicFiniteSetting D C E.val n).isIso_smoothPurityMap f r
      ((scalarReductionDerivedExtension C.l E.val Y n).obj L)
      (purAdicReductionFiniteTor D C E.val Y L hTor n)
    have he : IsIso (purAdicFiniteArrow D C E.val f r L hTor n).hom := by
      unfold purAdicFiniteArrow
      assumption
    let e := asIso (purAdicFiniteArrow D C E.val f r L hTor n).hom
    have hf : (scalarReductionDerivedExtension C.l E.val X n).map
        (component D C f r S A E ⟨L, hTor⟩).hom ≫
          purAdicTargetReduction D C E.val f r L hTor n =
        purAdicSourceReduction D C E.val f r L hTor n ≫ e.hom := by
      unfold component
      with_unfolding_all
        exact hfinite.2.2
    have hi : (scalarReductionDerivedExtension C.l E.val X n).map
        (component D C f r S A E ⟨L, hTor⟩).inv ≫
          purAdicSourceReduction D C E.val f r L hTor n =
        purAdicTargetReduction D C E.val f r L hTor n ≫ e.inv :=
      inverseSquare (scalarReductionDerivedExtension C.l E.val X n)
        (component D C f r S A E ⟨L, hTor⟩) e _ _ hf
    have hc : (scalarReductionDerivedExtension C.l E.val Y n).map
        (counit D C f r S A E ⟨L, hTor⟩) =
      supportComparison D C f E (purAdicTarget D C E.val f L) n ≫
        ((purAdicFiniteSetting D C E.val n).smoothCompactSupport f).map
          (purAdicTargetReduction D C E.val f r L hTor n) ≫
        (purAdicFiniteSetting D C E.val n).smoothExceptionalCounit f
          ((scalarReductionDerivedExtension C.l E.val Y n).obj L) := by
      exact integralPurityCounitReduction D C f r S A E ⟨L, hTor⟩ n
        (counit D C f r S A E ⟨L, hTor⟩) (by unfold counit purAdicTarget; rfl)
        (supportComparison D C f E) (by unfold supportComparison; rfl)
    refine ⟨hfinite.1, hfinite.2.1,
      supportComparison_isIso D C f E _ hsource n,
      supportComparison_isIso D C f E _ htarget n, e, rfl, hf, hi, ?_, ?_,
      finiteEquations D C f r E ⟨L, hTor⟩ n⟩
    · have ht := traceSquare
        (PurCompactSupport.image (PurCompactSupport.completed C.l E.val)
          (integralExceptionalCompactification D f))
        (scalarReductionDerivedExtension C.l E.val X n)
        (scalarReductionDerivedExtension C.l E.val Y n)
        ((purAdicFiniteSetting D C E.val n).smoothCompactSupport f)
        (component D C f r S A E ⟨L, hTor⟩).hom
        (purAdicSourceReduction D C E.val f r L hTor n)
        (purAdicTargetReduction D C E.val f r L hTor n) e.hom
        (supportComparison D C f E _ n) (supportComparison D C f E _ n)
        (counit D C f r S A E ⟨L, hTor⟩)
        ((purAdicFiniteSetting D C E.val n).smoothExceptionalCounit f
          ((scalarReductionDerivedExtension C.l E.val Y n).obj L))
        (supportComparison_naturality D C f E _ n) hf hc
      unfold trace PurityFiniteSetting.coefficientValuedSmoothTrace
      have he' : e.hom = (purAdicFiniteSetting D C E.val n).smoothPurityMap f r
          ((scalarReductionDerivedExtension C.l E.val Y n).obj L)
          (purAdicReductionFiniteTor D C E.val Y L hTor n) := rfl
      rw [he'] at ht
      with_unfolding_all
        exact ht
    · exact hc

end WeilConjectures.NormalizedIntegralPurityTrace
