/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralCompactSupportCoefficientData
public import WeilConjectures.AlgebraicGeometry.FiniteTateSiteDescentDefinitions
public import WeilConjectures.AlgebraicGeometry.RootsOfUnityInverseImageIso
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.FrobeniusIntegralDiscreteTransport
import all WeilConjectures.AlgebraicGeometry.FrobeniusIntegralDiscreteTransportInvertible
import all WeilConjectures.AlgebraicGeometry.ProEtaleIsomorphismInverseImage
import all WeilConjectures.AlgebraicGeometry.ProEtaleModulePullbackComposition
import WeilConjectures.AlgebraicGeometry.FrobeniusScalarTensorTransport

/-! # Transport of the first finite root line

Source: expanded DAG def-weil-frobenius-coefficient-twists, clause 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped ChangeOfRings TensorProduct
namespace WeilConjectures

private instance (priority := 3000) rootSiteSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  proEtaleModuleInverseImage completedIntegralCoefficientSheafUnrestricted
  Padic
attribute [local instance_reducible] PurCompactSupport.completed


attribute [local implicit_reducible] constantSheaf sheafCompose Functor.sheafPushforwardContinuous
  MorphismProperty.Over.pullback Scheme.instCategoryProEt
  proEtaleRingModuleDirectImage ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'
  SheafOfModules.changeOfRingsOfUniverses
  integralCoefficientCommRingSheaf PurCompactSupport.finite
  isoModulePushforwardEquivalence SheafOfModules.pushforwardPushforwardEquivalence
  isoBaseChangeEquivalence SheafOfModules.toSheaf purTwistIntegralModule purTwistIntegralOne
  PresheafOfModules.presheaf purTwistZlOne


private theorem rootTransport_isIso
    (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (r : (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}).obj
      (purTwistZlOne Y l) ⟶ purTwistZlOne X l)
    (hr : r = limit.post (proEtaleRootsOfUnityTower Y l Fact.out)
        (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}) ≫
      lim.map (((proEtaleRootsOfUnityInverseImageIso g).2.1 l Fact.out).choose)) :
    IsIso r := by
  classical
  rw [hr]
  let c := ((proEtaleRootsOfUnityInverseImageIso g).2.1 l Fact.out).choose
  have hc : ∀ k, IsIso (c.app k) := by
    intro k
    dsimp only [c]
    rw [((proEtaleRootsOfUnityInverseImageIso g).2.1 l Fact.out).choose_spec k.unop]
    exact ((proEtaleRootsOfUnityInverseImageIso g).2.2.2 inferInstance
      (l ^ (k.unop + 1)) (pow_pos (Fact.out : l.Prime).pos _)).1
  have : IsIso c := (NatTrans.isIso_iff_isIso_app c).2 hc
  have := proEtaleIso_inverseLimitComparison g AddCommGrpCat.{u + 1}
    (proEtaleRootsOfUnityTower Y l Fact.out)
  infer_instance

private theorem retypeDirectImage
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S)
    (σ : R ⟶ (proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj S)
    (hc : proEtaleRingDirectImageMap g R S c = σ)
    (M : proEtaleRingModules Y R) (N : proEtaleRingModules X S)
    (d : M ⟶ (SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange g)
      (J := ProEt.topology Y) (K := ProEt.topology X)
      (S := (sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
      (R := (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
      ⟨Functor.whiskerRight σ.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩).obj N)
    (hd : IsIso ((SheafOfModules.toSheaf _).map d)) :
    ∃ ψ : M ⟶ (proEtaleRingModuleDirectImage g R S c).obj N,
      IsIso ψ ∧ ∀ (U : Y.ProEtᵒᵖ) (x : M.val.obj U),
        ψ.val.app U x = d.val.app U x := by
  let ψ : M ⟶ (proEtaleRingModuleDirectImage g R S c).obj N :=
    { val := PresheafOfModules.homMk ((SheafOfModules.toSheaf _).map d).hom (by
        intro U a t
        change d.val.app U (a • t) =
          (show S.obj.obj ((proEtaleBaseChange g).op.obj U) from
            (proEtaleRingDirectImageMap g R S c).hom.app U a) •
          (show N.val.obj ((proEtaleBaseChange g).op.obj U) from d.val.app U t)
        rw [hc]
        exact (d.val.app U).hom.map_smul a t) }
  have hψ : IsIso ψ := by
    have : IsIso ((SheafOfModules.toSheaf _).map ψ) := hd
    exact isIso_of_reflects_iso ψ (SheafOfModules.toSheaf _)
  exact ⟨ψ, hψ, fun _ _ ↦ rfl⟩

/-- The prescribed root-limit comparison extends to the first
finite coefficient line. This statement concerns only the first line,
without tensor powers, signed powers, or a uniqueness assertion.
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-def-purity-conv/
def-weil-frobenius-coefficient-twists.md, natural Weil isomorphism;
expanded DAG clause 2; Stacks, Modules on Sites, Tag 03EL.
(blueprint: lem-weil-frobenius-finite-root-transport).
Proof: the finite root comparisons commute with the power transitions. Their inverse
limit is the displayed r; inverse image along the scheme isomorphism preserves this
limit. Its adjunct respects completed Z_l scalars because the scalar actions and r
are determined by their finite projections. Extend this semilinear map through the
constant O_E scalar tensor. The completed coefficient comparison respects both scalar
inclusions into the coefficient pushout, so the extended map respects the recorded
completed action. Apply ordinary finite coefficient extension to this map; its tensor unit sends a
  root to the displayed finite generator. Constant coefficients pull back to the same constants.
The inverse construction uses the inverse scheme isomorphism and the inverse root
and coefficient comparisons. The two composites are identities by tensor generation
and sheafification. No invertibility of l on the schemes is used: only invertibility
of g is needed to commute with the root limit. The same argument includes the empty
scheme and every ramification index. -/
theorem frobeniusFiniteRootTransport
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (n : ℕ)
    (r : (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}).obj
      (purTwistZlOne Y l) ⟶ purTwistZlOne X l)
    (hr : r = limit.post (proEtaleRootsOfUnityTower Y l Fact.out)
        (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}) ≫
      lim.map (((proEtaleRootsOfUnityInverseImageIso g).2.1 l Fact.out).choose)) :
    ∃ e : (proEtaleRingModulePullback g (integralCoefficientCommRingSheaf l E Y n)
        (integralCoefficientCommRingSheaf l E X n) ((PurCompactSupport.finite l E (n + 1)
          (Nat.succ_pos n)).pull g)).obj (purTwistFiniteOne Y l E n) ≅ (purTwistFiniteOne X l E n),
      ∀ (V : Y.ProEt) (a : finiteTateCoefficient l E n)
        (x : (purTwistZlOne Y l).obj.obj (op V)),
        e.hom.val.app (op ((proEtaleBaseChange g).obj V))
          (((proEtaleRingModuleAdjunction g (integralCoefficientCommRingSheaf l E Y n)
            (integralCoefficientCommRingSheaf l E X n) ((PurCompactSupport.finite l E (n + 1)
              (Nat.succ_pos n)).pull g)).unit.app (purTwistFiniteOne Y l E n)).val.app (op V)
            (finiteTateProGenerator l E n Y (op V) a x)) =
      finiteTateProGenerator l E n X (op ((proEtaleBaseChange g).obj V)) a
        (r.hom.app (op ((proEtaleBaseChange g).obj V))
          (((proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).unit.app
            (purTwistZlOne Y l)).hom.app (op V) x)) := by
  classical
  have hrIso : IsIso r := rootTransport_isIso l g r hr
  obtain ⟨β, hβ, hroot, hscalar⟩ := frobeniusIntegralDiscreteTransport l E g r hr hrIso
  let ρ := proEtaleConstantDirectImageMap g CommRingCat.{u + 1}
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))
  let σ := proEtaleConstantDirectImageMap g CommRingCat.{u + 1}
    (CommRingCat.of (finiteTateCoefficient l E n))
  have hsquare : purTwistIntegralQuotient Y l E n ≫ σ =
      ρ ≫ (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map
        (purTwistIntegralQuotient X l E n) := by
    exact AlgebraicGeometry.Scheme.constant_naturality g _
  have hb : ∀ (U : Y.ProEtᵒᵖ)
      (a : (purTwistIntegralConstant Y l E).obj.obj U)
      (x : (purTwistIntegralOne Y l E).val.obj U),
      β.hom.app U (a • x) =
        (show (purTwistIntegralConstant X l E).obj.obj
          ((proEtaleBaseChange g).op.obj U) from ρ.hom.app U a) •
        (show (purTwistIntegralOne X l E).val.obj
          ((proEtaleBaseChange g).op.obj U) from β.hom.app U x) := by
    intro U a x
    have hc := congrArg (fun k ↦ k.hom.app U a) (constantCompletion_square l E g)
    change (sfCompletedCoefficientMap l E g).hom.app U
        ((purTwistIntegralCompletionMap Y l E).hom.app U a) =
      (purTwistIntegralCompletionMap X l E).hom.app ((proEtaleBaseChange g).op.obj U)
        (ρ.hom.app U a) at hc
    exact (hscalar U.unop a x).trans (by
      erw [hc, (purTwistIntegralAction_existsUnique X l E).exists.choose_spec.2.1])
  have hd_pure := AlgebraicGeometry.Scheme.tensor_direct_pure
    (ProEt.topology Y) (ProEt.topology X) (proEtaleBaseChange g)
    (purTwistIntegralQuotient Y l E n) (purTwistIntegralQuotient X l E n)
    ρ σ hsquare (purTwistIntegralOne Y l E) (purTwistIntegralOne X l E) β hb
  generalize hddef : AlgebraicGeometry.Scheme.tensor_direct
    (ProEt.topology Y) (ProEt.topology X) (proEtaleBaseChange g)
    (purTwistIntegralQuotient Y l E n) (purTwistIntegralQuotient X l E n)
    ρ σ hsquare (purTwistIntegralOne Y l E) (purTwistIntegralOne X l E) β hb = d at hd_pure
  have : IsIso σ := constantDirect_isIso g (CommRingCat.of (finiteTateCoefficient l E n))
  have hd : IsIso ((SheafOfModules.toSheaf _).map d) :=
    frobeniusScalarTensorTransport_isIso g (purTwistIntegralQuotient Y l E n)
      (purTwistIntegralQuotient X l E n) ρ σ hsquare
      (purTwistIntegralOne Y l E) (purTwistIntegralOne X l E) β hb
      (constantDirect_isIso g _) (constantDirect_isIso g _) hβ
      ((SheafOfModules.toSheaf _).map d) hd_pure
  let R := integralCoefficientCommRingSheaf l E Y n
  let S := integralCoefficientCommRingSheaf l E X n
  let c := (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull g
  have hc : proEtaleRingDirectImageMap g R S c = σ := by
    exact constantRing_direct g (Padic.coefficientExtensionRing l E (n + 1))
  obtain ⟨ψ, hψ, hψ_app⟩ := retypeDirectImage g R S c σ hc
    (purTwistFiniteOne Y l E n) (purTwistFiniteOne X l E n) d hd
  have hcoef : IsIso (proEtaleRingDirectImageMap g R S c) := by
    rw [hc]
    infer_instance
  let ρring : ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⟶
    (proEtaleSheafDirectImage g RingCat.{u + 1}).obj
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) :=
    (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (proEtaleRingDirectImageMap g R S c)
  have : IsIso ρring := Functor.map_isIso
    (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
    (proEtaleRingDirectImageMap g R S c)
  let eD := isoModulePushforwardEquivalence g
    ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) ρring
  have : (proEtaleRingModuleDirectImage g R S c).IsEquivalence := by
    change eD.functor.IsEquivalence
    exact eD.isEquivalence_functor
  let adj := proEtaleRingModuleAdjunction g R S c
  have : (proEtaleRingModulePullback g R S c).IsEquivalence :=
    adj.isEquivalence_left_of_isEquivalence_right
  have : IsIso adj.unit := adj.unit_isIso_of_L_fully_faithful
  have : IsIso (adj.unit.app (purTwistFiniteOne Y l E n)) :=
    (NatTrans.isIso_iff_isIso_app adj.unit).mp inferInstance _
  let f := (adj.homEquiv _ _).symm ψ
  have hf : adj.unit.app (purTwistFiniteOne Y l E n) ≫
      (proEtaleRingModuleDirectImage g R S c).map f = ψ :=
    (adj.homEquiv_unit _ _ f).symm.trans (Equiv.apply_symm_apply _ ψ)
  have hcomp : IsIso (adj.unit.app (purTwistFiniteOne Y l E n) ≫
      (proEtaleRingModuleDirectImage g R S c).map f) := by
    rw [hf]
    exact hψ
  have hfiso : IsIso f := by
    have : IsIso ((proEtaleRingModuleDirectImage g R S c).map f) :=
      IsIso.of_isIso_comp_left (adj.unit.app (purTwistFiniteOne Y l E n)) _
    exact isIso_of_reflects_iso f (proEtaleRingModuleDirectImage g R S c)
  refine ⟨asIso f, ?_⟩
  intro V a x
  have hfsection := congrArg (fun k ↦ k.val.app (op V)
    (finiteTateProGenerator l E n Y (op V) a x)) hf
  refine hfsection.trans ?_
  erw [hψ_app]
  change d.val.app (op V)
    (SheafOfModules.scalarExtensionSection (purTwistIntegralQuotient Y l E n)
      (purTwistIntegralOne Y l E) (op V)
      ((realizationRingUnit (ProEt.topology Y) (finiteTateCoefficient l E n)).app (op V) a)
      (purTwistIntegralTensor Y l E (op V) 1 x)) = _
  have ht := hd_pure
    (op V)
    ((realizationRingUnit (ProEt.topology Y) (finiteTateCoefficient l E n)).app (op V) a)
    (purTwistIntegralTensor Y l E (op V) 1 x)
  refine ht.trans ?_
  have hroot1 := hroot V 1 x
  have hρone : ρ.hom.app (op V) 1 = 1 := (ρ.hom.app (op V)).hom.map_one
  rw [hρone] at hroot1
  erw [hroot1]
  have hconst : σ.hom.app (op V)
      ((realizationRingUnit (ProEt.topology Y) (finiteTateCoefficient l E n)).app (op V) a) =
    (realizationRingUnit (ProEt.topology X) (finiteTateCoefficient l E n)).app
      (op ((proEtaleBaseChange g).obj V)) a := by
    have ht := constantSection_unit g (Padic.coefficientExtensionRing l E (n + 1)) (op V)
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom ht) a
  erw [hconst]
  rfl

end WeilConjectures
