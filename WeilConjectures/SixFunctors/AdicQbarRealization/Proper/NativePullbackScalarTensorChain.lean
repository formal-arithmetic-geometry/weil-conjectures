/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativeProperTensorComparison
public import WeilConjectures.SixFunctors.AdicQbarRealization.Native.NativeAdicFiniteNormalization
public import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralPullbackModuleIdentification
import all WeilConjectures.SixFunctors.IntegralOrdinary.IntegralPullbackModuleIdentification
import WeilConjectures.SmoothPurity.ProEtale.ProEtaleTotalTensorPullbackGenerators
import WeilConjectures.SmoothPurity.Coefficient.CoefficientTotalTensorMapGenerators
import all WeilConjectures.SixFunctors.AdicQbarRealization.AdicOrdinaryScalarTensorReindexing

/-! # The ordinary scalar and pullback square on total complexes

Source: BS Remark 6.8.15; Stacks Tags 03EL and 07A4.
(blueprint: lem-sf-native-pullback-scalar-tensor-chain).

The unit-normalized module comparison is the canonical ordinary pullback model
comparison followed by the specified scalar balance. Transpose morphisms out of
scalar extension of inverse image through the two module adjunctions. Total-summand
and pure-tensor extensionality reduce equality to source homogeneous sections.
On the left, the canonical pullback total comparison and scalar balance separate
the two factors. On the right, naturality of the native pullback unit, source scalar
balance, and the native pure tensor formula do the same. The two balanced unit
identities identify the factors. Every map preserves bidegree, so the signed
cochain differential introduces no additional sign. The proof imposes no flatness
or boundedness condition on the inputs and applies to zero and empty cases.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures.AdicQbarRealization.Proper
attribute [local irreducible] HasDerivedCategory.standard
  SheafOfModules.monoidalCategory WeilConjectures.coefficientTotalTensor
  ContinuousRational.modulePull ordinaryIntegralModulePull
attribute [local implicit_reducible] WeilConjectures.PurCompactSupport.completed
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  CategoryTheory.Functor.mapHomologicalComplex integralComplex
  completedIntegralCoefficientSheafUnrestricted
set_option backward.defeqAttrib.useBackward true
variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (p : X ⟶ Y)
  (R : LocallyFiniteAdicRealization.Realization l X)
  (S : LocallyFiniteAdicRealization.Realization l Y)
  (O : Operations l p R S)
  (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
  (I : IntegralComparison l p R S O E)

/-- The ordinary scalar balance in canonical ringed pullback coordinates.
Source: BS 6.8.15 (blueprint: lem-sf-native-pullback-scalar-tensor-chain). -/
def nativeModuleBalance :
    proEtaleRingModulePullback p
        ((PurCompactSupport.completed l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)).ring Y)
        ((PurCompactSupport.completed l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)).ring X)
        ((PurCompactSupport.completed l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)).pull p) ⋙
        pbcExtend (coefficientMap l X R E) ≅
      pbcExtend (coefficientMap l Y S E) ⋙ ContinuousRational.modulePull p O.coefficient :=
  Functor.isoWhiskerRight (IntegralOrdinary.pullbackModuleIso l _ p)
    (pbcExtend (coefficientMap l X R E)) ≪≫ I.balance

/-- Unit sections fix this balance before localization.
Source: BS 6.8.15 (blueprint: lem-sf-native-pullback-scalar-tensor-chain).
Proof: scalar-unit naturality moves the ordinary model comparison past insertion
of one. Its unit normalization and I.sections identify the resulting section. -/
theorem nativeModuleBalance_sections
    (M : integralTowerModules l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y)
    (V : Y.ProEt) (x : M.val.obj (op V)) :
    let k := AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E
    let C := PurCompactSupport.completed l k
    let H := proEtaleRingModulePullback p (C.ring Y) (C.ring X) (C.pull p)
    ((nativeModuleBalance l p R S O E I).hom.app M).val.app
        (op ((proEtaleBaseChange p).obj V))
      (pbcTensorSection (coefficientMap l X R E) (H.obj M)
        (op ((proEtaleBaseChange p).obj V)) 1
        (((proEtaleRingModuleAdjunction p (C.ring Y) (C.ring X) (C.pull p)).unit.app M).val.app
          (op V) x)) =
      ContinuousRational.moduleUnit p O.coefficient
        ((pbcExtend (coefficientMap l Y S E)).obj M) V
          (pbcTensorSection (coefficientMap l Y S E) M (op V) 1 x) := by
  intro k C H
  change (I.balance.hom.app M).val.app _
    (((pbcExtend (coefficientMap l X R E)).map
      ((IntegralOrdinary.pullbackModuleIso l k p).hom.app M)).val.app _ _) = _
  erw [scalar_map_section]
  have hunit := IntegralOrdinary.pullbackModuleIso_unit l k p M V x
  exact (congrArg (fun z ↦ (I.balance.hom.app M).val.app _
    (pbcTensorSection (coefficientMap l X R E) _ _ 1 z)) hunit).trans (I.sections M V x)

private theorem scalar_pull_total_ext
    (k : Type u) [Field k] [Algebra (Padic l) k] [FiniteDimensional (Padic l) k]
    {T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : completedIntegralCommRingSheafUnrestricted l k X ⟶ T)
    (P Q : CochainComplex (integralTowerModules l k Y) ℤ)
    (L : CochainComplex (pbcModules X T) ℤ)
    {f g : ((pbcExtend a).mapHomologicalComplex (.up ℤ)).obj
      (((proEtaleRingModulePullback p ((PurCompactSupport.completed l k).ring Y)
        ((PurCompactSupport.completed l k).ring X)
        ((PurCompactSupport.completed l k).pull p)).mapHomologicalComplex (.up ℤ)).obj
          ((constructibleTensorTotal l k Y).obj (P, Q))) ⟶ L}
    (hh : ∀ (i j : ℤ) (V : Y.ProEt) (x : (P.X i).val.obj (op V))
      (y : (Q.X j).val.obj (op V)),
      let C := PurCompactSupport.completed l k
      let H := proEtaleRingModulePullback p (C.ring Y) (C.ring X) (C.pull p)
      let z := pbcTensorSection a (H.obj
        (((constructibleTensorTotal l k Y).obj (P, Q)).X (i + j)))
        (op ((proEtaleBaseChange p).obj V)) 1
        (((proEtaleRingModuleAdjunction p (C.ring Y) (C.ring X) (C.pull p)).unit.app
          (((constructibleTensorTotal l k Y).obj (P, Q)).X (i + j))).val.app (op V)
            (constructibleTensorTotalSection l k Y P Q i j (op V) x y))
      (f.f (i + j)).val.app (op ((proEtaleBaseChange p).obj V)) z =
        (g.f (i + j)).val.app (op ((proEtaleBaseChange p).obj V)) z) : f = g := by
  apply HomologicalComplex.Hom.ext
  funext n
  let C := PurCompactSupport.completed l k
  let h := proEtaleRingModuleAdjunction p (C.ring Y) (C.ring X) (C.pull p)
  apply ((h.comp (pbcScalarAdjunction a)).homEquiv _ (L.X n)).injective
  let := SheafOfModules.monoidalCategory
    (completedIntegralCommRingSheafUnrestricted l k Y)
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  apply SheafOfModules.ScalarHomOrdinary.pure_hom_ext
    (completedIntegralCommRingSheafUnrestricted l k Y) (P.X i) (Q.X j)
  intro V x y
  subst n
  change (f.f (i + j)).val.app (op ((proEtaleBaseChange p).obj V.unop))
      (((pbcScalarAdjunction a).unit.app _).val.app _
        ((h.unit.app _).val.app V
          (constructibleTensorTotalSection l k Y P Q i j V x y))) =
    (g.f (i + j)).val.app (op ((proEtaleBaseChange p).obj V.unop))
      (((pbcScalarAdjunction a).unit.app _).val.app _
        ((h.unit.app _).val.app V
          (constructibleTensorTotalSection l k Y P Q i j V x y)))
  erw [(pbcScalarAdjunction_exists a).exists.choose_spec]
  exact hh i j V.unop x y

set_option maxHeartbeats 6400000 in
-- The total tensor and composite module adjunction require a larger elaboration budget.
/-- Scalar balance and inverse image preserve the same homogeneous pure tensors.
Source: BS 6.8.15; Stacks 03EL (blueprint: lem-sf-native-pullback-scalar-tensor-chain).
Proof: transpose through scalar and geometric adjunctions and test on homogeneous
pure source tensors. The canonical total pullback comparison, target scalar balance
and tensor functoriality give the tensor of the two balanced units. Source scalar
balance, naturality of the native unit and W.pure give the same tensor. The balanced
unit equations identify both factors, and total-summand extensionality finishes. -/
theorem nativeScalarTensor_cochain
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : At l X R) (B : At l Y S)
    (NX : FiniteNormalization l X R A E) (NY : FiniteNormalization l Y S B E)
    (W : TensorComparison l p R S O A B)
    (P Q : CochainComplex (integralTowerModules l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y) ℤ) :
    let k := AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E
    let C := PurCompactSupport.completed l k
    let Hc : CochainComplex (integralTowerModules l k Y) ℤ ⥤
        CochainComplex (integralTowerModules l k X) ℤ :=
      (proEtaleRingModulePullback p (C.ring Y) (C.ring X) (C.pull p)).mapHomologicalComplex (.up ℤ)
    let Fc := (ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ)
    let eX := integralComplex l X R E
    let eY := integralComplex l Y S E
    let cY := constructibleTensorTotal l k Y
    let tX := coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
    let γ := NatIso.mapHomologicalComplex (nativeModuleBalance l p R S O E I) (.up ℤ)
    let J := (proEtaleTensorPullbackTotalIso p (C.ring Y) (C.ring X) (C.pull p) P Q).inv
    eX.map J ≫ NX.balance.hom.app (Hc.obj P, Hc.obj Q) ≫
        tX.map (Prod.mkHom (γ.hom.app P) (γ.hom.app Q)) =
      γ.hom.app (cY.obj (P, Q)) ≫ Fc.map (NY.balance.hom.app (P, Q)) ≫
        W.cochain.hom.app (eY.obj P, eY.obj Q) := by
  intro k C Hc Fc eX eY cY tX γ J
  apply scalar_pull_total_ext l p k (coefficientMap l X R E) P Q
    (tX.obj (Fc.obj (eY.obj P), Fc.obj (eY.obj Q)))
  intro i j V x y
  let V' := op ((proEtaleBaseChange p).obj V)
  let h := proEtaleRingModuleAdjunction p (C.ring Y) (C.ring X) (C.pull p)
  let u := (h.unit.app (P.X i)).val.app (op V) x
  let v := (h.unit.app (Q.X j)).val.app (op V) y
  let x' := pbcTensorSection (coefficientMap l Y S E) (P.X i) (op V) 1 x
  let y' := pbcTensorSection (coefficientMap l Y S E) (Q.X j) (op V) 1 y
  let z := pbcTensorSection (coefficientMap l X R E)
    ((proEtaleRingModulePullback p (C.ring Y) (C.ring X) (C.pull p)).obj
      ((cY.obj (P, Q)).X (i + j))) V' 1
    ((h.unit.app ((cY.obj (P, Q)).X (i + j))).val.app (op V)
      (constructibleTensorTotalSection l k Y P Q i j (op V) x y))
  have hJ : ((eX.map J).f (i + j)).val.app V' z =
      pbcTensorSection (coefficientMap l X R E) _ V' 1
        (constructibleTensorTotalSection l k X (Hc.obj P) (Hc.obj Q) i j V' u v) := by
    dsimp only [eX, integralComplex, Functor.mapHomologicalComplex_map_f, z]
    erw [scalar_map_section]
    apply congrArg (pbcTensorSection (coefficientMap l X R E) _ V' 1)
    have hg := proEtaleTensorPullbackTotal_generators p (C.ring Y) (C.ring X) (C.pull p)
      P Q i j (i + j) rfl V x y
    simp only [J, h, cY, Hc, u, v, V',
      constructibleTensorTotalSection, coefficientTensorGenerator,
      PresheafOfModules.comp_app, ModuleCat.comp_apply, C, PurCompactSupport.completed,
      constructibleTensorOrdinary, constructibleTensorTotal, integralTowerModules,
      SheafOfModules.derivedChangeRingIndependentCoefficients,
      coefficientTotalTensor, Functor.map₂CochainComplex,
      CochainComplex.ιMapBifunctor] at hg ⊢
    convert hg using 1 <;> rfl
  have hγP : ((γ.hom.app P).f i).val.app V'
      (pbcTensorSection (coefficientMap l X R E) _ V' 1 u) =
        ContinuousRational.moduleUnit p O.coefficient ((eY.obj P).X i) V x' := by
    exact nativeModuleBalance_sections l p R S O E I (P.X i) V x
  have hγQ : ((γ.hom.app Q).f j).val.app V'
      (pbcTensorSection (coefficientMap l X R E) _ V' 1 v) =
        ContinuousRational.moduleUnit p O.coefficient ((eY.obj Q).X j) V y' := by
    exact nativeModuleBalance_sections l p R S O E I (Q.X j) V y
  have hγT : ((γ.hom.app (cY.obj (P, Q))).f (i + j)).val.app V' z =
      ContinuousRational.moduleUnit p O.coefficient ((eY.obj (cY.obj (P, Q))).X (i + j)) V
        (pbcTensorSection (coefficientMap l Y S E) _ (op V) 1
          (constructibleTensorTotalSection l k Y P Q i j (op V) x y)) := by
    exact nativeModuleBalance_sections l p R S O E I ((cY.obj (P, Q)).X (i + j)) V
      (constructibleTensorTotalSection l k Y P Q i j (op V) x y)
  change ((tX.map (Prod.mkHom (γ.hom.app P) (γ.hom.app Q))).f (i + j)).val.app V'
      ((NX.balance.hom.app (Hc.obj P, Hc.obj Q)).f (i + j) |>.val.app V'
        (((eX.map J).f (i + j)).val.app V' z)) =
    ((W.cochain.hom.app (eY.obj P, eY.obj Q)).f (i + j)).val.app V'
      (((Fc.map (NY.balance.hom.app (P, Q))).f (i + j)).val.app V'
        (((γ.hom.app (cY.obj (P, Q))).f (i + j)).val.app V' z))
  erw [hJ, NX.balance_sections (Hc.obj P) (Hc.obj Q) i j V' 1 u v]
  erw [native_total_map_generator]
  erw [hγP, hγQ, hγT]
  have hn := congrArg (fun t ↦ t.val.app (op V)
    (pbcTensorSection (coefficientMap l Y S E) _ (op V) 1
      (constructibleTensorTotalSection l k Y P Q i j (op V) x y)))
    (O.moduleAdjunction.unit.naturality ((NY.balance.hom.app (P, Q)).f (i + j)))
  simp only [Functor.id_map, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hn
  erw [O.unit_sections, O.unit_sections] at hn
  change ContinuousRational.moduleUnit p O.coefficient _ V
      (((NY.balance.hom.app (P, Q)).f (i + j)).val.app (op V)
        (pbcTensorSection (coefficientMap l Y S E) _ (op V) 1
          (constructibleTensorTotalSection l k Y P Q i j (op V) x y))) =
    (((Fc.map (NY.balance.hom.app (P, Q))).f (i + j)).val.app V'
      (ContinuousRational.moduleUnit p O.coefficient _ V
        (pbcTensorSection (coefficientMap l Y S E) _ (op V) 1
          (constructibleTensorTotalSection l k Y P Q i j (op V) x y)))) at hn
  erw [← hn]
  erw [NY.balance_sections P Q i j (op V) 1 x y]
  have hw := (W.pure (eY.obj P) (eY.obj Q) i j V x' y').symm
  dsimp only [eY, integralComplex, V', x', y', Functor.mapHomologicalComplex,
    Functor.comp_obj, Functor.comp_map, Functor.prod_obj] at hw ⊢
  erw [O.unit_sections, O.unit_sections, O.unit_sections] at hw
  exact hw

end WeilConjectures.AdicQbarRealization.Proper
