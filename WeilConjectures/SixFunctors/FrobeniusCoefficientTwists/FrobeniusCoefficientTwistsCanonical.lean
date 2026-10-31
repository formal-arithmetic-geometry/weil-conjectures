/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescent
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.RootsOfUnityInverseImageIso
public import WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageTensorHom
public import WeilConjectures.SixFunctors.Sf.SfWeilSheafComplex
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
import all WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedReductionAugmentationIso
import WeilConjectures.SmoothPurity.IntegralOnSlice.IsomorphismOrdinaryCompletionChain
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated

import WeilConjectures.SmoothPurity.Frobenius.FrobeniusIntegralRootTransport
import WeilConjectures.SmoothPurity.Frobenius.FrobeniusFiniteRootTransport
import WeilConjectures.SmoothPurity.Integral.IntegralRootPowerGenerators
import WeilConjectures.SmoothPurity.Finite.FiniteRootPowerGenerators
import WeilConjectures.SmoothPurity.Frobenius.FrobeniusPositivePowerTransport
import all WeilConjectures.SmoothPurity.FrobeniusCoefficientTwists.FrobeniusSignedPowerTransport
import all WeilConjectures.SmoothPurity.FrobeniusCoefficientTwists.FrobeniusAugmentationGeneric
import WeilConjectures.SmoothPurity.FrobeniusCoefficientTwists.FrobeniusNormalizedDescent
import all WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModulePullbackComposition

/-! # Canonical Frobenius on coefficient twists

Source: main-20261015, def-weil-frobenius-coefficient-twists, clauses 1--5
(blueprint: def-weil-frobenius-coefficient-twists).
The first map below is an actual map of root towers. Its inverse limit, rather than
an arbitrary trivialization of a Tate line, determines the signed coefficient maps.
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme CategoryTheory.Endofunctor
namespace WeilConjectures
namespace FrobeniusCoefficientTwists

attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived
attribute [local irreducible] HasDerivedCategory.standard
  CochainComplex.mappingCocone.fst CochainComplex.mappingCocone.snd
attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  proEtaleModuleInverseImage Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  IntegralOnSlice.ordinaryPull IntegralOnSlice.ordinaryAdjunction Scheme.residueField Padic
  completedIntegralCoefficientSheafUnrestricted MorphismProperty.Over.pullback constantSheaf
attribute [local instance_reducible] PurCompactSupport.completed IntegralOnSlice.Site
  IntegralOnSlice.topology IntegralOnSlice.restrict IntegralOnSlice.ring
  IntegralOnSlice.ordinaryComplexPull integralOperationsPullbackComplexFunctor
  integralOperationsRoosFunctor integralOperationsRoos
  sfRationalTwistingFunctor sfQbarTwistingFunctor

/-- The native additive structure, retained as a named instance presentation.
Source: the existing completed-coefficient module category and Mathlib's
`SheafOfModules` preadditive instance
(blueprint: def-weil-frobenius-coefficient-twists). -/
@[instance_reducible]
def coefficientPreadditive (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : Scheme.{u}) :
    Preadditive (integralTowerModules l E W) := inferInstance

attribute [local instance 4000] coefficientPreadditive

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.scalarReductionSourceDerived
attribute [-instance] WeilConjectures.scalarReductionTargetDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local instance 3000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance] coefficientSiteSmall

/-- The existing nonnegative completed root powers.
Source: definition clauses 2--3
(blueprint: def-weil-frobenius-coefficient-twists). -/
abbrev positiveLine (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (d : ℕ) :=
  coefficientTwistPower T
    (R := completedIntegralCommRingSheafUnrestricted l E T)
    (purTwistIntegralModule T l E) d

/-- Pure local tensors in the existing completed root powers.
Source: definition clauses 2--3, normalization on root tensors
(blueprint: def-weil-frobenius-coefficient-twists). -/
def generator (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (W : T.ProEtᵒᵖ)
    (a : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj W) :
    (d : ℕ) → (Fin d → (purTwistZlOne T l).obj.obj W) →
      (positiveLine l E T d).val.obj W
  | 0, _ => a
  | 1, x => @SMul.smul _ _ (purTwistIntegralAction T l E W).toSMul a
      (purTwistIntegralTensor T l E W 1 (x 0))
  | d + 2, x => SheafOfModules.siteSheafTensorTmul
      (positiveLine l E T (d + 1)) (purTwistIntegralModule T l E) W
      (generator l E T W a (d + 1) (fun i ↦ x i.castSucc))
      (purTwistIntegralTensor T l E W 1 (x (Fin.last (d + 1))))

/-- The root comparisons with their actual power transitions.
Source: definition clause 2, inverse images of roots of unity
(blueprint: def-weil-frobenius-coefficient-twists). -/
def rootTowerMap (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    proEtaleRootsOfUnityTower Y l (Fact.out : l.Prime) ⋙
        proEtaleSheafInverseImage g AddCommGrpCat.{u + 1} ⟶
      proEtaleRootsOfUnityTower X l (Fact.out : l.Prime) := by
  refine NatTrans.ofOpSequence
    (fun r ↦ proEtaleRootsOfUnityInverseImageMap g (l ^ (r + 1))) ?_
  intro r
  simp only [Functor.comp_map, proEtaleRootsOfUnityTower,
    Functor.ofOpSequence_map_homOfLE_succ]
  change (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}).map
      (proEtaleRootsOfUnityTransition Y (l ^ (r + 1)) (l ^ (r + 2))
        (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
        (pow_dvd_pow l (Nat.le_succ (r + 1)))) ≫
      proEtaleRootsOfUnityInverseImageMap g (l ^ (r + 1)) =
    proEtaleRootsOfUnityInverseImageMap g (l ^ (r + 2)) ≫
      proEtaleRootsOfUnityTransition X (l ^ (r + 1)) (l ^ (r + 2))
        (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
        (pow_dvd_pow l (Nat.le_succ (r + 1)))
  exact (proEtaleRootsOfUnityInverseImageIso g).1 _ _ _ _ _

private theorem rootTowerMap_app (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) (r : ℕ) :
    (rootTowerMap l g).app (op r) =
      proEtaleRootsOfUnityInverseImageMap g (l ^ (r + 1)) := by
  rfl

private theorem rootTowerMap_eq (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    rootTowerMap l g = ((proEtaleRootsOfUnityInverseImageIso g).2.1 l Fact.out).choose := by
  apply NatTrans.ext
  funext r
  rw [rootTowerMap_app]
  exact (((proEtaleRootsOfUnityInverseImageIso g).2.1 l Fact.out).choose_spec r.unop).symm

attribute [local irreducible] rootTowerMap

/-- The inverse-limit comparison followed by the inverse limit of the root maps.
This formula retains all the projections of the completed root line.
Source: definition clause 2, tau for Z_l(1)
(blueprint: def-weil-frobenius-coefficient-twists). -/
def rootLineMap (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}).obj (purTwistZlOne Y l) ⟶
      purTwistZlOne X l :=
  limit.post (proEtaleRootsOfUnityTower Y l Fact.out)
      (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}) ≫
    lim.map (rootTowerMap l g)

attribute [local irreducible] rootLineMap

/-- Pull a compatible root section through the specified inverse-image unit and
the specified inverse-limit root map. This is defined before extending coefficients.
Source: definition clause 2
(blueprint: def-weil-frobenius-coefficient-twists). -/
def rootSection (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (V : Y.ProEt) (x : (purTwistZlOne Y l).obj.obj (op V)) :
    (purTwistZlOne X l).obj.obj (op ((proEtaleBaseChange g).obj V)) :=
  (rootLineMap l g).hom.app (op ((proEtaleBaseChange g).obj V))
    (((proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).unit.app
      (purTwistZlOne Y l)).hom.app (op V) x)

/-- The ordinary completed-coefficient module pullback, with the existing
projection-normalized coefficient identification.
Source: definition clause 1
(blueprint: def-weil-frobenius-coefficient-twists). -/
abbrev modulePull (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}} (g : X ⟶ Y) :=
  proEtaleRingModulePullback g
    ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull g)

/-- Insertion of a section into the preceding module pullback.
Source: definition clause 1, coefficient-linear inverse image
(blueprint: def-weil-frobenius-coefficient-twists). -/
def moduleSection (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : integralTowerModules l E Y) (V : Y.ProEt)
    (x : M.val.obj (op V)) :
    ((modulePull l E g).obj M).val.obj (op ((proEtaleBaseChange g).obj V)) :=
  ((proEtaleRingModuleAdjunction g
    ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull g)).unit.app
      M).val.app (op V) x

/-- The nonnegative powers are fixed on every scalar and root tensor, including
the coefficient unit at zero. This is the coefficient extension of rootLineMap,
followed by its tensor powers, not an unnormalized line isomorphism.
Source: definition clauses 2--3
(blueprint: def-weil-frobenius-coefficient-twists).
Proof: extend the inverse-limit root map along the constant integer coefficients.
The specified completed coefficient comparison makes it linear. The tensor
universal property gives the powers; at zero use the coefficient comparison.
For an isomorphism of schemes all these factors are isomorphisms. The displayed
local generators determine each sheaf map uniquely, including on the empty site. -/
theorem existsUnique_positiveLineMaps (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    ∃! tau : ∀ d : ℕ,
      (modulePull l E g).obj (positiveLine l E Y d) ≅
        positiveLine l E X d,
      ∀ (d : ℕ) (V : Y.ProEt)
        (a : (completedIntegralCoefficientSheafUnrestricted
          l E Y).obj.obj (op V))
        (x : Fin d → (purTwistZlOne Y l).obj.obj (op V)),
        (tau d).hom.val.app (op ((proEtaleBaseChange g).obj V))
            (moduleSection l E g (positiveLine l E Y d) V
              (generator l E Y (op V) a d x)) =
          generator l E X (op ((proEtaleBaseChange g).obj V))
            ((sfCompletedCoefficientMap l E g).hom.app (op V) a)
            d (fun i ↦ rootSection l g V (x i)) := by
  obtain ⟨e, he⟩ := frobeniusIntegralRootTransport l E g (rootLineMap l g)
    (by unfold rootLineMap; rw [rootTowerMap_eq]; rfl)
  obtain ⟨P, hzero, hone, hstep⟩ := frobeniusPositivePowerTransport g
    (completedIntegralCommRingSheafUnrestricted l E Y)
    (completedIntegralCommRingSheafUnrestricted l E X)
    ((PurCompactSupport.completed l E).pull g)
    (purTwistIntegralModule Y l E) (purTwistIntegralModule X l E) e
  have hcoef : proEtaleRingDirectImageMap g
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull g) = sfCompletedCoefficientMap l E g := by
    exact (proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _
      |>.apply_symm_apply _
  have hP : ∀ (d : ℕ) (V : Y.ProEt)
      (a : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V))
      (x : Fin d → (purTwistZlOne Y l).obj.obj (op V)),
      (P d).hom.val.app (op ((proEtaleBaseChange g).obj V))
        (moduleSection l E g (positiveLine l E Y d) V
          (generator l E Y (op V) a d x)) =
      generator l E X (op ((proEtaleBaseChange g).obj V))
        ((sfCompletedCoefficientMap l E g).hom.app (op V) a)
        d (fun i ↦ rootSection l g V (x i)) := by
    apply Nat.twoStepInduction
    · intro V a x
      exact (hzero V a).trans (congrArg (fun f ↦ f.hom.app (op V) a) hcoef)
    · intro V a x
      rw [hone]
      exact he V a (x 0)
    · intro d _ ih V a x
      change (P (d + 2)).hom.val.app _
        (moduleSection l E g _ V (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} _ _ _
          (generator l E Y (op V) a (d + 1) (fun i ↦ x i.castSucc))
          (purTwistIntegralTensor Y l E (op V) 1 (x (Fin.last (d + 1)))))) = _
      erw [hstep, ih]
      have he1 := he V 1 (x (Fin.last (d + 1)))
      have hy := @one_smul _ _ _ (purTwistIntegralAction Y l E (op V)).toMulAction
        (purTwistIntegralTensor Y l E (op V) 1 (x (Fin.last (d + 1))))
      have hx := @one_smul _ _ _
        (purTwistIntegralAction X l E (op ((proEtaleBaseChange g).obj V))).toMulAction
        (purTwistIntegralTensor X l E (op ((proEtaleBaseChange g).obj V)) 1
          (rootSection l g V (x (Fin.last (d + 1)))))
      have hc : (sfCompletedCoefficientMap l E g).hom.app (op V)
          (1 : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V)) = 1 :=
        ((sfCompletedCoefficientMap l E g).hom.app (op V)).hom.map_one
      have hright := (congrArg (fun b ↦ @SMul.smul _ _
        (purTwistIntegralAction X l E (op ((proEtaleBaseChange g).obj V))).toSMul b
        (purTwistIntegralTensor X l E (op ((proEtaleBaseChange g).obj V)) 1
          (rootSection l g V (x (Fin.last (d + 1)))))) hc).trans hx
      have he1' := (congrArg (fun z ↦ e.hom.val.app
        (op ((proEtaleBaseChange g).obj V))
        (moduleSection l E g (purTwistIntegralModule Y l E) V z)) hy.symm).trans
          (he1.trans hright)
      exact congrArg (fun z ↦ SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} _ _ _ _ z)
        he1'
  refine ⟨P, hP, ?_⟩
  intro Q hQ
  funext d
  apply Iso.ext
  apply ((proEtaleRingModuleAdjunction g
    ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull g)).homEquiv _ _).injective
  apply integralRootPower_hom_ext l E Y
    (fun d V a x ↦ generator l E Y V a d x)
    (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) d
  intro V a x
  exact (hQ d V.unop a x).trans (hP d V.unop a x).symm

/-- The tensor-power comparisons selected from their unique scalar/root formulas.
Source: definition clauses 2--3
(blueprint: def-weil-frobenius-coefficient-twists). -/
def positiveLineMaps (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (d : ℕ) :
    (modulePull l E g).obj (positiveLine l E Y d) ≅
      positiveLine l E X d :=
  (existsUnique_positiveLineMaps l E g).exists.choose d

attribute [local irreducible] positiveLineMaps

/-- Signed lines use the published positive tensor powers and internal duals.
Source: definition clause 3
(blueprint: def-weil-frobenius-coefficient-twists). -/
abbrev line (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (m : ℤ) :=
  coefficientTwistLine T
    (R := completedIntegralCommRingSheafUnrestricted l E T)
    (purTwistIntegralModule T l E) m

/-- The negative powers are fixed by evaluation, which is precisely conjugation
by the positive comparison and the coefficient comparison. Positive powers retain
their previously fixed root-tensor maps.
Source: definition clause 3
(blueprint: def-weil-frobenius-coefficient-twists).
Proof: for negative powers transport internal Hom through the isomorphism of sites.
Send phi to c composed with phi composed with the inverse positive comparison.
Evaluation on all local sections gives the displayed equation. The positive maps
are invertible and their local images generate, so this equation determines the
negative map uniquely. Inverting the conjugation gives its inverse. The clauses
cover zero, every positive integer and every negative integer without overlap. -/
theorem existsUnique_signedLineMaps (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    ∃! tau : ∀ m : ℤ, (modulePull l E g).obj (line l E Y m) ≅ line l E X m,
      (∀ d : ℕ, HEq (tau (d : ℤ)) (positiveLineMaps l E g d)) ∧
      ∀ (n : ℕ) (V W : Y.ProEt) (a : W ⟶ V)
        (phi : (line l E Y (Int.negSucc n)).val.obj (op V))
        (x : (positiveLine l E Y (n + 1)).val.obj (op W)),
        ((tau (Int.negSucc n)).hom.val.app (op ((proEtaleBaseChange g).obj V))
          (moduleSection l E g (line l E Y (Int.negSucc n)) V phi)).app
            (op (Over.mk ((proEtaleBaseChange g).map a)))
              ((positiveLineMaps l E g (n + 1)).hom.val.app
                (op ((proEtaleBaseChange g).obj W))
                (moduleSection l E g (positiveLine l E Y (n + 1)) W x)) =
          (positiveLineMaps l E g 0).hom.val.app (op ((proEtaleBaseChange g).obj W))
            (moduleSection l E g (positiveLine l E Y 0) W
              (phi.app (op (Over.mk a)) x)) := by
  exact genericSignedProof g
    (completedIntegralCommRingSheafUnrestricted l E Y)
    (completedIntegralCommRingSheafUnrestricted l E X)
    ((PurCompactSupport.completed l E).pull g) (purTwistIntegralModule Y l E)
    (purTwistIntegralModule X l E) (positiveLineMaps l E g)

/-- The unique signed inverse-image comparisons at completed coefficients.
Source: definition clause 3
(blueprint: def-weil-frobenius-coefficient-twists). -/
def signedLineMaps (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (m : ℤ) :
    (modulePull l E g).obj (line l E Y m) ≅ line l E X m :=
  (existsUnique_signedLineMaps l E g).exists.choose m

attribute [local irreducible] signedLineMaps

/-- Finite-coefficient module pullback with its constant coefficient comparison.
The natural number n denotes the positive quotient exponent n+1.
Source: definition clauses 1--2
(blueprint: def-weil-frobenius-coefficient-twists). -/
abbrev finiteModulePull (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}}
    (g : X ⟶ Y) (n : ℕ) :=
  proEtaleRingModulePullback g
    ((PurCompactSupport.finite l E (n + 1)
      (Nat.succ_pos n)).ring Y)
    ((PurCompactSupport.finite l E (n + 1)
      (Nat.succ_pos n)).ring X)
    ((PurCompactSupport.finite l E (n + 1)
      (Nat.succ_pos n)).pull g)

/-- The actual finite module inverse-image unit on a section.
Source: definition clause 1
(blueprint: def-weil-frobenius-coefficient-twists). -/
def finiteModuleSection (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}}
    (g : X ⟶ Y) (n : ℕ)
    (M : SheafOfModules.{u + 1} (integralCoefficientSheaf
      l E Y n))
    (V : Y.ProEt) (x : M.val.obj (op V)) :
    ((finiteModulePull l E g n).obj M).val.obj (op ((proEtaleBaseChange g).obj V)) :=
  ((proEtaleRingModuleAdjunction g
    ((PurCompactSupport.finite l E (n + 1)
      (Nat.succ_pos n)).ring Y)
    ((PurCompactSupport.finite l E (n + 1)
      (Nat.succ_pos n)).ring X)
    ((PurCompactSupport.finite l E (n + 1)
      (Nat.succ_pos n)).pull g)).unit.app M).val.app (op V) x

section FinitePositiveProof
attribute [local semireducible] constantSheaf

/-- Finite powers are the reductions of the same scalar/root tensor formulas.
Source: definition clauses 2--3
(blueprint: def-weil-frobenius-coefficient-twists).
Proof: reduce the integral scalar/root maps. The coefficient square commutes with
inverse image and the power transitions. The displayed formula fixes every local
pure tensor, so sheafification and the tensor universal property prove uniqueness.
The inverse root and coefficient maps give the inverse at an isomorphism of schemes.
This argument includes the coefficient unit at exponent zero and every positive
finite quotient, without an unramifiedness assumption. -/
theorem existsUnique_finitePositiveLineMaps (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    ∃! tau : ∀ d : ℕ,
      (finiteModulePull l E g n).obj
          (finiteCoefficientTwist l E Y n (d : ℤ)) ≅
        finiteCoefficientTwist l E X n (d : ℤ),
      ∀ (d : ℕ) (V : Y.ProEt)
        (a : finiteTateCoefficient l E n)
        (x : Fin d → (purTwistZlOne Y l).obj.obj (op V)),
        (tau d).hom.val.app (op ((proEtaleBaseChange g).obj V))
          (finiteModuleSection l E g n
            (finiteCoefficientTwist l E Y n (d : ℤ)) V
              (finiteTateProPowerGenerator l E n Y (op V) a d x)) =
          finiteTateProPowerGenerator l E n X
            (op ((proEtaleBaseChange g).obj V)) a d
            (fun i ↦ rootSection l g V (x i)) := by
  obtain ⟨e, he⟩ := frobeniusFiniteRootTransport l E g n (rootLineMap l g)
    (by unfold rootLineMap; rw [rootTowerMap_eq]; rfl)
  obtain ⟨P, hzero, hone, hstep⟩ := frobeniusPositivePowerTransport g
    (integralCoefficientCommRingSheaf l E Y n)
    (integralCoefficientCommRingSheaf l E X n)
    ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull g)
    (purTwistFiniteOne Y l E n) (purTwistFiniteOne X l E n) e
  have hcoef := constantRing_direct g (Padic.coefficientExtensionRing l E (n + 1))
  have hP : ∀ (d : ℕ) (V : Y.ProEt) (a : finiteTateCoefficient l E n)
      (x : Fin d → (purTwistZlOne Y l).obj.obj (op V)),
      (P d).hom.val.app (op ((proEtaleBaseChange g).obj V))
        (finiteModuleSection l E g n (finiteCoefficientTwist l E Y n (d : ℤ)) V
          (finiteTateProPowerGenerator l E n Y (op V) a d x)) =
      finiteTateProPowerGenerator l E n X (op ((proEtaleBaseChange g).obj V)) a d
        (fun i ↦ rootSection l g V (x i)) := by
    apply Nat.twoStepInduction
    · intro V a x
      have hz := hzero V ((realizationRingUnit (ProEt.topology Y)
        (finiteTateCoefficient l E n)).app (op V) a)
      have hc := congrArg (fun f ↦ f.hom.app (op V)
        ((realizationRingUnit (ProEt.topology Y)
          (finiteTateCoefficient l E n)).app (op V) a)) hcoef
      have hua :
          ((toSheafify (ProEt.topology Y)
              ((Functor.const Y.ProEtᵒᵖ).obj
                (CommRingCat.of (finiteTateCoefficient l E n)))).app (op V) ≫
            (proEtaleCoefficientDirectImageMap g
              (Padic.coefficientExtensionRing l E (n + 1))).hom.app (op V)).hom a =
          ((toSheafify (ProEt.topology X)
              ((Functor.const X.ProEtᵒᵖ).obj
                (CommRingCat.of (finiteTateCoefficient l E n)))).app
            (op ((proEtaleBaseChange g).obj V))).hom a := by
        rw [constantSection_unit]
        rfl
      exact hz.trans (hc.trans hua)
    · intro V a x
      rw [hone]
      exact he V a (x 0)
    · intro d _ ih V a x
      change (P (d + 2)).hom.val.app _
        (finiteModuleSection l E g n _ V
          (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} _ _ _
          (finiteTateProPowerGenerator l E n Y (op V) a (d + 1)
            (fun i ↦ x i.castSucc))
          (finiteTateProGenerator l E n Y (op V) 1 (x (Fin.last (d + 1)))))) = _
      erw [hstep, ih]
      exact congrArg (fun z ↦ SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} _ _ _ _ z)
        (he V 1 (x (Fin.last (d + 1))))
  refine ⟨P, hP, ?_⟩
  intro Q hQ
  funext d
  apply Iso.ext
  apply ((proEtaleRingModuleAdjunction g
    ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring Y)
    ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring X)
    ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull g)).homEquiv _ _).injective
  apply finiteRootPower_hom_ext l E Y n
    (fun d V a x ↦ finiteTateProPowerGenerator l E n Y V a d x)
    (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) d
  intro V a x
  exact (hQ d V.unop a x).trans (hP d V.unop a x).symm

end FinitePositiveProof

/-- Finite positive power maps with the root and coefficient normalization retained.
Source: definition clauses 2--3
(blueprint: def-weil-frobenius-coefficient-twists). -/
def finitePositiveLineMaps (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n d : ℕ) :
    (finiteModulePull l E g n).obj
        (finiteCoefficientTwist l E Y n (d : ℤ)) ≅
      finiteCoefficientTwist l E X n (d : ℤ) :=
  (existsUnique_finitePositiveLineMaps l E g n).exists.choose d

attribute [local irreducible] finitePositiveLineMaps

/-- Finite negative powers use the same inverse-positive conjugation as completed
powers. Evaluation states the formula without choosing an internal-Hom trivialization.
Source: definition clause 3
(blueprint: def-weil-frobenius-coefficient-twists).
Proof: transport internal Hom across the site isomorphism. Conjugate by the
positive map and the coefficient map. The displayed evaluation identity fixes the
negative map on all local sections. The positive and coefficient maps are invertible,
which gives both uniqueness and the inverse negative map. -/
theorem existsUnique_finiteSignedLineMaps (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    ∃! tau : ∀ m : ℤ,
      (finiteModulePull l E g n).obj
          (finiteCoefficientTwist l E Y n m) ≅
        finiteCoefficientTwist l E X n m,
      (∀ d : ℕ, HEq (tau (d : ℤ)) (finitePositiveLineMaps l E g n d)) ∧
      ∀ (j : ℕ) (V W : Y.ProEt) (a : W ⟶ V)
        (phi : (finiteCoefficientTwist l E Y n
          (Int.negSucc j)).val.obj (op V))
        (x : (finiteCoefficientTwist l E Y n
          ((j + 1 : ℕ) : ℤ)).val.obj (op W)),
        ((tau (Int.negSucc j)).hom.val.app (op ((proEtaleBaseChange g).obj V))
          (finiteModuleSection l E g n
            (finiteCoefficientTwist l E Y n (Int.negSucc j))
            V phi)).app (op (Over.mk ((proEtaleBaseChange g).map a)))
              ((finitePositiveLineMaps l E g n (j + 1)).hom.val.app
                (op ((proEtaleBaseChange g).obj W))
                (finiteModuleSection l E g n
                  (finiteCoefficientTwist l E Y n
                    ((j + 1 : ℕ) : ℤ)) W x)) =
          (finitePositiveLineMaps l E g n 0).hom.val.app
            (op ((proEtaleBaseChange g).obj W))
            (finiteModuleSection l E g n
              (finiteCoefficientTwist l E Y n 0) W
              (phi.app (op (Over.mk a)) x)) := by
  exact genericSignedProof g _ _ _ (purTwistFiniteOne Y l E n)
    (purTwistFiniteOne X l E n) (finitePositiveLineMaps l E g n)

/-- The finite signed comparisons, fixed on positive root tensors and negative
evaluations.
Source: definition clause 3
(blueprint: def-weil-frobenius-coefficient-twists). -/
def finiteSignedLineMaps (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) (m : ℤ) :
    (finiteModulePull l E g n).obj
        (finiteCoefficientTwist l E Y n m) ≅
      finiteCoefficientTwist l E X n m :=
  (existsUnique_finiteSignedLineMaps l E g n).exists.choose m

section AugmentationProof
attribute [local instance 3000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance] coefficientSiteSmall

section AugmentationConstruction
attribute [local semireducible] completedIntegralCoefficientSheafUnrestricted
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem augmentationRingMap {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (proEtaleRingDirectImageMap g
        ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull g)) =
      IntegralOnSlice.ordinaryCompletedRingMap l E g := by
  have h : proEtaleRingDirectImageMap g
        ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull g) = sfCompletedCoefficientMap l E g := by
    exact (proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _
      |>.apply_symm_apply _
  rw [h]
  apply (IntegralOnSlice.ordinaryCompletedRingMap_existsUnique l E g).unique
  · intro n
    exact congrArg
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map)
      ((sfCompletedCoefficientMap_existsUnique l E g).exists.choose_spec n)
  · exact (IntegralOnSlice.ordinaryCompletedRingMap_existsUnique l E g).exists.choose_spec

private def augmentationPullIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    modulePull l E g ≅ IntegralOnSlice.ordinaryPull l E g :=
  (proEtaleRingModuleAdjunction g
    ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull g)).leftAdjointUniq
      ((IntegralOnSlice.ordinaryAdjunction l E g).ofNatIsoRight
        (SheafOfModules.pushforwardCongr (augmentationRingMap l E g)).symm)

private theorem augmentationPullIso_unit {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : integralTowerModules l E Y) (V : Y.ProEt) (x : M.val.obj (op V)) :
    ((augmentationPullIso l E g).hom.app M).val.app
        (op ((proEtaleBaseChange g).obj V))
      (moduleSection l E g M V x) =
      ((IntegralOnSlice.ordinaryAdjunction l E g).unit.app M).val.app (op V) x := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (proEtaleRingModuleAdjunction g
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull g))
    ((IntegralOnSlice.ordinaryAdjunction l E g).ofNatIsoRight
      (SheafOfModules.pushforwardCongr (augmentationRingMap l E g)).symm) M
  exact congrArg (fun a ↦ a.val.app (op V) x) h

attribute [local irreducible] augmentationPullIso

private def augmentationComplexComparison {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (modulePull l E g).mapHomologicalComplex (.up ℤ) ⟶
      IntegralOnSlice.ordinaryComplexPull l E g := by
  let F₀ : IntegralOnSlice.Mod l E Y none ⥤ IntegralOnSlice.Mod l E X none :=
    modulePull l E g
  let e₀ : F₀ ≅ IntegralOnSlice.ordinaryPull l E g := augmentationPullIso l E g
  let : F₀.Additive := proEtaleRingModulePullback_additive g _ _ _
  let : (IntegralOnSlice.ordinaryPull l E g).Additive := Functor.additive_of_iso e₀
  exact (NatIso.mapHomologicalComplex e₀ (.up ℤ)).hom

private def augmentationTower {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (modulePull l E g).mapHomologicalComplex (.up ℤ) ⋙
        (Functor.const ℕᵒᵖ : CochainComplex (integralTowerModules l E X) ℤ ⥤ _) ⟶
      integralOperationsPullbackTowerFunctor l E g :=
  Functor.whiskerRight (augmentationComplexComparison l E g) (Functor.const ℕᵒᵖ) ≫
    IntegralOnSlice.ordinaryQuotientAugmentation l E g

private theorem augmentationTower_formula {X Y : Scheme.{u}} (g : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) (i : ℤ)
    (V : Y.ProEt) (x : (P.X i).val.obj (op V)) :
    ((((augmentationTower l E g).app P).app (op n)).f i).val.app
        (op ((proEtaleBaseChange g).obj V))
      (moduleSection l E g (P.X i) V x) =
      integralOperationsPullbackGenerator l E g n
        (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
        (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x) := by
  change (((((IntegralOnSlice.ordinaryQuotientAugmentation l E g).app P).app
    (op n)).f i).val.app (op ((proEtaleBaseChange g).obj V)))
      (((augmentationPullIso l E g).hom.app (P.X i)).val.app
        (op ((proEtaleBaseChange g).obj V)) (moduleSection l E g (P.X i) V x)) = _
  rw [augmentationPullIso_unit]
  exact (IntegralOnSlice.ordinaryQuotientAugmentation_existsUnique l E g).exists.choose_spec
    P n i V x

end AugmentationConstruction

attribute [local irreducible] productAug chainAug augmentationPullIso augmentationComplexComparison
  augmentationTower

attribute [local irreducible] finiteSignedLineMaps

private def canonicalAugmentation (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (modulePull l E g).mapHomologicalComplex (.up ℤ) ⟶
      integralOperationsPullbackComplexFunctor l E g :=
  towerAugmentation _ _ (augmentationTower l E g)

/-- The two prescribed coordinate equations for the strict pullback augmentation.
This is exactly the scalar-generator formula and the vanishing shifted component.
Source: definition clause 4
(blueprint: def-weil-frobenius-coefficient-twists). -/
def pullbackAugmentationNormalization (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (eta : (modulePull l E g).mapHomologicalComplex (.up ℤ) ⟶
      integralOperationsPullbackComplexFunctor l E g) : Prop :=
      (∀ (C : CochainComplex (integralTowerModules l E Y) ℤ)
        (i : ℤ) (n : ℕ) (V : Y.ProEt) (x : (C.X i).val.obj (op V)),
        (((eta.app C).f i ≫
          (CochainComplex.mappingCocone.fst
            (towerTransitionEndomorphism
              (K := fun j ↦ ((integralOperationsPullbackTowerFunctor
                l E g).obj C).obj (op j))
              (integralOperationsTowerStep
                ((integralOperationsPullbackTowerFunctor
                  l E g).obj C)))).f i ≫
          (Pi.π (fun j ↦ ((integralOperationsPullbackTowerFunctor
            l E g).obj C).obj (op j)) n).f i).val.app
              (op ((proEtaleBaseChange g).obj V)))
          (moduleSection l E g (C.X i) V x) =
            integralOperationsPullbackGenerator l E g n
              (((unrestrictedIntegralFiniteComplex l E Y n).obj
                C).X i) V
              (unrestrictedIntegralTensorSection l E Y n
                (C.X i) (op V) 1 x)) ∧
      ∀ (C : CochainComplex (integralTowerModules l E Y) ℤ)
        (i : ℤ),
        (eta.app C).f i ≫
          (CochainComplex.mappingCocone.snd
            (towerTransitionEndomorphism
              (K := fun j ↦ ((integralOperationsPullbackTowerFunctor
                l E g).obj C).obj (op j))
              (integralOperationsTowerStep
                ((integralOperationsPullbackTowerFunctor
                  l E g).obj C)))).v i (i - 1) (by omega) = 0

private theorem canonicalAugmentation_spec (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    pullbackAugmentationNormalization l E g (canonicalAugmentation l E g) := by
  let F : CochainComplex (integralTowerModules l E Y) ℤ ⥤
      CochainComplex (integralTowerModules l E X) ℤ :=
    (modulePull l E g).mapHomologicalComplex (.up ℤ)
  let T : CochainComplex (integralTowerModules l E Y) ℤ ⥤
      (ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E X) ℤ) :=
    integralOperationsPullbackTowerFunctor l E g
  let a := augmentationTower l E g
  let eta : F ⟶ T ⋙ integralOperationsRoosFunctor := canonicalAugmentation l E g
  have hf (C : CochainComplex (integralTowerModules l E Y) ℤ) :
      eta.app C ≫ CochainComplex.mappingCocone.fst
        (towerTransitionEndomorphism (K := fun n : ℕ ↦ (T.obj C).obj (op n))
          (integralOperationsTowerStep (T.obj C))) = productAug F T a C :=
    chainAug_fst F T a C
  have hs (C : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) :
      (eta.app C).f i ≫ (CochainComplex.mappingCocone.snd
        (towerTransitionEndomorphism (K := fun n : ℕ ↦ (T.obj C).obj (op n))
          (integralOperationsTowerStep (T.obj C)))).v i (i - 1) (by omega) = 0 :=
    chainAug_snd F T a C i
  have hformula (C : CochainComplex (integralTowerModules l E Y) ℤ)
      (i : ℤ) (n : ℕ) (V : Y.ProEt) (x : (C.X i).val.obj (op V)) :
      (((eta.app C ≫ CochainComplex.mappingCocone.fst
          (towerTransitionEndomorphism (K := fun j : ℕ ↦ (T.obj C).obj (op j))
            (integralOperationsTowerStep (T.obj C))) ≫
          Pi.π (fun j : ℕ ↦ (T.obj C).obj (op j)) n).f i).val.app
            (op ((proEtaleBaseChange g).obj V)))
        (moduleSection l E g (C.X i) V x) =
        integralOperationsPullbackGenerator l E g n
          (((unrestrictedIntegralFiniteComplex l E Y n).obj C).X i) V
          (unrestrictedIntegralTensorSection l E Y n (C.X i) (op V) 1 x) := by
    rw [← Category.assoc, hf]
    simp only [productAug, Pi.lift_π]
    exact augmentationTower_formula l E g C n i V x
  exact ⟨hformula, hs⟩

attribute [local irreducible] canonicalAugmentation

/-- The strict comparison from ordinary inverse image to the specified completed
pullback Roos complex. Both cone components are fixed, so this does not choose a
map of homotopy limits from its finite evaluations.
Source: definition clause 4, lambda; the isomorphism-derived-pullback construction
(blueprint: def-weil-frobenius-coefficient-twists).
Proof: reduce a module section x at each positive quotient and apply the finite
inverse-image unit. These maps are completed-linear, since the coefficient maps
commute with the quotient projections. They commute with every strict transition.
Their product is killed by 1-s. The mapping-cocone lift with zero second component
gives the comparison. The displayed two component equations determine it uniquely
in every degree and prove its naturality in the original complex. -/
theorem existsUnique_pullbackAugmentation (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    ∃! eta : (modulePull l E g).mapHomologicalComplex (.up ℤ) ⟶
        integralOperationsPullbackComplexFunctor l E g,
      pullbackAugmentationNormalization l E g eta := by
  let eta := canonicalAugmentation l E g
  have h := canonicalAugmentation_spec l E g
  refine ⟨eta, h, ?_⟩
  intro other hother
  apply NatTrans.ext
  funext C
  apply augmentationCocone_ext
  · apply Pi.hom_ext
    intro n
    apply HomologicalComplex.hom_ext
    intro i
    apply ringedPull_hom_ext g _ _ _
    intro V x
    exact (hother.1 C i n V x).trans (h.1 C i n V x).symm
  · intro i
    exact (hother.2 C i).trans (h.2 C i).symm

end AugmentationProof

attribute [local irreducible] canonicalAugmentation

/-- The uniquely normalized strict augmentation.
Source: definition clause 4
(blueprint: def-weil-frobenius-coefficient-twists). -/
def pullbackAugmentation (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}}
    (g : X ⟶ Y) :
    (modulePull l E g).mapHomologicalComplex (.up ℤ) ⟶
      integralOperationsPullbackComplexFunctor l E g :=
  (existsUnique_pullbackAugmentation l E g).exists.choose

private theorem unique_choice_eq {A : Sort*} {p : A → Prop}
    (h : ∃! x, p x) (x : A) (hx : p x) : h.exists.choose = x :=
  h.unique h.exists.choose_spec hx

private theorem pullbackAugmentation_canonical (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    pullbackAugmentation l E g = canonicalAugmentation l E g :=
  unique_choice_eq (p := pullbackAugmentationNormalization l E g)
    (existsUnique_pullbackAugmentation l E g)
    (canonicalAugmentation l E g) (canonicalAugmentation_spec l E g)

attribute [local irreducible] Functor.mapHomologicalComplex DerivedCategory.Q

section AugmentationIdentification
attribute [local instance_reducible] pullbackAugmentation
attribute [local instance 3000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance] coefficientSiteSmall
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] augmentationPullIso augmentationComplexComparison
  integralDerivedPullback integralDerivedPullbackComparison

private theorem pullbackAugmentation_eq (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (C : CochainComplex (integralTowerModules l E Y) ℤ) :
    (pullbackAugmentation l E g).app C =
      (augmentationComplexComparison l E g).app C ≫
        IntegralOnSlice.ordinaryCompletionChain l E g C := by
  rw [pullbackAugmentation_canonical]
  unfold canonicalAugmentation towerAugmentation
  change chainAug ((modulePull l E g).mapHomologicalComplex (.up ℤ))
      (integralOperationsPullbackTowerFunctor l E g) (augmentationTower l E g) C =
    (augmentationComplexComparison l E g).app C ≫
      chainAug (IntegralOnSlice.ordinaryComplexPull l E g)
        (integralOperationsPullbackTowerFunctor l E g)
        (IntegralOnSlice.ordinaryQuotientAugmentation l E g) C
  exact chainAug_precomp (IntegralOnSlice.ordinaryComplexPull l E g)
    (integralOperationsPullbackTowerFunctor l E g)
    (IntegralOnSlice.ordinaryQuotientAugmentation l E g)
    ((modulePull l E g).mapHomologicalComplex (.up ℤ))
    (augmentationComplexComparison l E g) C

attribute [local irreducible] pullbackAugmentation IntegralOnSlice.roosUnit
  IntegralOnSlice.ordinaryCompletionChain integralOperationsPullbackComplexFunctor
  integralOperationsRoos
attribute [local instance_reducible] IntegralOnSlice.roos

/-- Ordinary inverse image along an isomorphism preserves completeness; the
specified augmentation is therefore a quasi-isomorphism on complete good inputs.
Source: definition clause 4 and lem-weil-isomorphism-derived-pullback
(blueprint: def-weil-frobenius-coefficient-twists).
Proof: identify inverse image with reindexing the equivalent pro-etale site.
It preserves the strict quotient tower, its products and its Roos differential.
The augmentation becomes the usual derived-completeness unit, which is invertible
on a complete input. The finite reductions and the common constructibility interval
are preserved by this exact relabelling. -/
theorem pullbackAugmentation_isIso (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (C : CochainComplex (integralTowerModules l E Y) ℤ)
    (hC : integralOperationsGoodComplex l E Y C)
    (hK : sfIntegralConstructible l E Y
      (DerivedCategory.Q.obj C)) :
    IsIso (DerivedCategory.Q.map ((pullbackAugmentation l E g).app C)) := by
  let F₀ : IntegralOnSlice.Mod l E Y none ⥤ IntegralOnSlice.Mod l E X none :=
    modulePull l E g
  let : F₀.Additive := proEtaleRingModulePullback_additive g _ _ _
  let : PreservesFiniteLimits F₀ :=
    proEtaleRingModulePullback_preservesFiniteLimits g _ _ _
  let : PreservesFiniteColimits F₀ :=
    proEtaleRingModulePullback_preservesFiniteColimits g _ _ _
  let e₀ : F₀ ≅ IntegralOnSlice.ordinaryPull l E g := augmentationPullIso l E g
  let : (IntegralOnSlice.ordinaryPull l E g).Additive := Functor.additive_of_iso e₀
  have hi : IsIso ((augmentationComplexComparison l E g).app C) := by
    unfold augmentationComplexComparison
    exact ((NatIso.mapHomologicalComplex e₀ (.up ℤ)).app C).isIso_hom
  exact augmentation_isIso l E g C hC hK F₀ e₀ (pullbackAugmentation l E g)
    (augmentationComplexComparison l E g) hi (pullbackAugmentation_eq l E g C)

end AugmentationIdentification

attribute [local irreducible] pullbackAugmentation

/-- Lambda on a good complete representative: normalized descent to the strict
Roos complex, followed by the inverse of its specified augmentation.
Source: definition clause 4
(blueprint: def-weil-frobenius-coefficient-twists). -/
def completedToOrdinaryOnGood (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (C : CochainComplex (integralTowerModules l E Y) ℤ)
    (hC : integralOperationsGoodComplex l E Y C)
    (hK : sfIntegralConstructible l E Y
      (DerivedCategory.Q.obj C)) :
    (integralDerivedPullback l E g).obj
        (DerivedCategory.Q.obj C) ≅
      (PurCompactSupport.pull (PurCompactSupport.completed l E)
        g).obj (DerivedCategory.Q.obj C) :=
  ((((modulePull l E g).mapDerivedCategoryFactors.app C ≪≫
      @asIso _ _ _ _ (DerivedCategory.Q.map ((pullbackAugmentation l E g).app C))
        (pullbackAugmentation_isIso l E g C hC hK)) ≪≫
      ((integralDerivedPullbackComparison l E g).app ⟨C, hC⟩).symm)).symm

private theorem reassoc_left_inverse {A : Type*} [Category A] {W X Y Z : A}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (d : Z ⟶ W)
    (h : (((a ≫ b) ≫ c) ≫ d) = 𝟙 W) : (a ≫ b ≫ c) ≫ d = 𝟙 W := by
  simpa only [Category.assoc] using h

section CompletedComparisonProof
attribute [local irreducible] integralDerivedPullback integralDerivedPullbackComparison

private theorem completed_good_normalization (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (C : CochainComplex (integralTowerModules l E Y) ℤ)
    (hC : integralOperationsGoodComplex l E Y C)
    (hK : sfIntegralConstructible l E Y (DerivedCategory.Q.obj C)) :
    ((modulePull l E g).mapDerivedCategoryFactors.hom.app C ≫
        DerivedCategory.Q.map ((pullbackAugmentation l E g).app C) ≫
        (integralDerivedPullbackComparison l E g).inv.app ⟨C, hC⟩) ≫
      (completedToOrdinaryOnGood l E g C hC hK).hom = 𝟙 _ := by
  exact reassoc_left_inverse ((modulePull l E g).mapDerivedCategoryFactors.hom.app C)
    (DerivedCategory.Q.map ((pullbackAugmentation l E g).app C))
    ((integralDerivedPullbackComparison l E g).inv.app ⟨C, hC⟩)
    (completedToOrdinaryOnGood l E g C hC hK).hom
    (completedToOrdinaryOnGood l E g C hC hK).inv_hom_id

attribute [local irreducible] completedToOrdinaryOnGood

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in

/-- The full lambda comparison has the strict representative normalization retained.
Source: definition clause 4
(blueprint: def-weil-frobenius-coefficient-twists).
Proof: resolve each integral constructible object by a flat-term K-flat complex.
The previous comparison gives the component there. Naturality of the strict
augmentation and the normalized descent makes it independent of resolution and
natural in every localized arrow. Every object has such a representative, so the
displayed formula also proves uniqueness. No arbitrary natural isomorphism is chosen. -/
theorem existsUnique_completedToOrdinary (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    ∃! e : (sfIntegralConstructible l E Y).ι ⋙
          integralDerivedPullback l E g ≅
        (sfIntegralConstructible l E Y).ι ⋙
          PurCompactSupport.pull (PurCompactSupport.completed l E) g,
      ∀ (C : CochainComplex (integralTowerModules l E Y) ℤ)
        (hC : integralOperationsGoodComplex l E Y C)
        (hK : sfIntegralConstructible l E Y
          (DerivedCategory.Q.obj C)),
        e.hom.app ⟨DerivedCategory.Q.obj C, hK⟩ =
          (completedToOrdinaryOnGood l E g C hC hK).hom := by
  let P := sfIntegralConstructible l E Y
  let L := integralOperationsGoodLocalization l E Y
  let W := (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E Y).ι
  let : L.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E Y
  let : P.IsClosedUnderIsomorphisms :=
    sfIntegralConstructible_isClosedUnderIsomorphisms l E Y
  obtain ⟨e, he, hu⟩ := normalized_descent L W P (modulePull l E g).mapDerivedCategory
    (integralDerivedPullback l E g) _ _
    (Functor.isoWhiskerLeft (integralOperationsGoodComplex l E Y).ι
      (modulePull l E g).mapDerivedCategoryFactors)
    (integralDerivedPullbackComparison l E g)
    (Functor.whiskerLeft (integralOperationsGoodComplex l E Y).ι
      (Functor.whiskerRight (pullbackAugmentation l E g) DerivedCategory.Q))
    (fun C hK ↦ completedToOrdinaryOnGood l E g C.obj C.property hK)
    (fun C hK ↦ completed_good_normalization l E g C.obj C.property hK)
  refine ⟨e, ?_, ?_⟩
  · intro C hC hK
    exact he ⟨C, hC⟩ hK
  · intro e' he'
    exact hu e' (fun C hK ↦ he' C.obj C.property hK)

end CompletedComparisonProof

/-- The canonical lambda comparison determined on all good representatives.
Source: definition clause 4
(blueprint: def-weil-frobenius-coefficient-twists). -/
def completedToOrdinary (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :=
  (existsUnique_completedToOrdinary l E g).exists.choose

attribute [local irreducible] completedToOrdinary

/-- The ordinary signed line placed in degree zero with its actual inverse-image
comparison, before completed pullback is identified with ordinary pullback.
Source: definition clause 4
(blueprint: def-weil-frobenius-coefficient-twists). -/
def ordinaryDerivedLineMap (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (m : ℤ) :
    (PurCompactSupport.pull (PurCompactSupport.completed l E) g).obj
        ((DerivedCategory.singleFunctor _ 0).obj (line l E Y m)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (line l E X m) :=
  ((modulePull l E g).mapDerivedCategorySingleFunctor 0).app (line l E Y m) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (signedLineMaps l E g m)

attribute [local irreducible] ordinaryDerivedLineMap

/-- The integral theta is exactly tau after the specified lambda.
Source: definition clause 4
(blueprint: def-weil-frobenius-coefficient-twists). -/
def integralDerivedLineMap (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (m : ℤ) :
    (integralDerivedPullback l E g).obj
        (sfIntegralTwistingObject l E Y m) ≅
      sfIntegralTwistingObject l E X m :=
  (completedToOrdinary l E g).app
      (sfIntegralTwistingCoefficient l E Y m) ≪≫
    ordinaryDerivedLineMap l E g m

attribute [local irreducible] integralDerivedLineMap

/-- The finite derived comparison is the exact inverse-image/single comparison
followed by the specified signed sheaf map.
Source: definition clause 4
(blueprint: def-weil-frobenius-coefficient-twists). -/
def finiteDerivedLineMap (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (n : ℕ) (m : ℤ) :
    (PurCompactSupport.pull (PurCompactSupport.finite l E
      (n + 1) (Nat.succ_pos n)) g).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (finiteCoefficientTwist l E Y n m)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (finiteCoefficientTwist l E X n m) :=
  ((finiteModulePull l E g n).mapDerivedCategorySingleFunctor 0).app
      (finiteCoefficientTwist l E Y n m) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (finiteSignedLineMaps l E g n m)

attribute [local irreducible] finiteDerivedLineMap

/-- The unchanged rational coefficient-line object is the localization of its
specified complete integral representative.
Source: definition clause 4
(blueprint: def-weil-frobenius-coefficient-twists). -/
abbrev rationalLine (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    [∀ t : T, Invertible (l : T.residueField t)] (m : ℤ) :
    sfRationalConstructibleCategory l E T :=
  sfRationalTwistingCoefficient l E T m

/-- Theta at rational coefficients is exactly the localized integral theta, with
the recorded pullback's unchanged-object identification. No stable lattice for
any other Weil complex enters this definition.
Source: definition clause 4
(blueprint: def-weil-frobenius-coefficient-twists). -/
def rationalDerivedLineMap (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (m : ℤ) :
    (rationalDerivedPullback l E g).obj (rationalLine l E Y m) ≅
      rationalLine l E X m :=
  eqToIso ((rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.1
      (rationalLine l E Y m)) ≪≫
    (sfRationalConstructibleLocalization l E X).mapIso
      (ObjectProperty.isoMk _ (integralDerivedLineMap l E g m))

attribute [local irreducible] rationalDerivedLineMap rationalDerivedPullback
set_option allowUnsafeReducibility true in
attribute [local reducible] commonStageDerivedPullback

set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.ofHom

attribute [local irreducible] ScalarLocalization.composition Padic.coefficientExtensionIntegers
  commonStagePullbackComparison ObjectProperty.FullSubcategory.category


attribute [local implicit_reducible] GeneralAlgebraicallyClosedCoefficients.Stage
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5


section CommonStageMapElaboration
attribute [local irreducible] ScalarLocalization.category

/-- The common-stage theta is represented by the same rational root map at the
least finite coefficient stage, with the prescribed pullback object identification.
Source: definition clause 4
(blueprint: def-weil-frobenius-coefficient-twists). -/
def commonDerivedLineMap (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (m : ℤ) :
    (commonStageDerivedPullback l Ω g).obj (sfQbarTwistingCoefficient l Y Ω m) ≅
      sfQbarTwistingCoefficient l X Ω m :=
  eqToIso ((commonStageDerivedPullback_existsUnique l Ω g).exists.choose_spec.1
      (sfQbarTwistingCoefficient l Y Ω m)) ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion
      (Padic.finiteCoefficientBase l Ω)).mapIso
        (rationalDerivedLineMap l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
            (Padic.finiteCoefficientBase l Ω)) g m)

end CommonStageMapElaboration

set_option allowUnsafeReducibility true in
attribute [local irreducible] commonDerivedLineMap commonStageDerivedPullback
attribute [local irreducible] commonStageDerivedTensor rationalDerivedTensor

/-- The tensor formula for twisting a rational Weil structure.
Its first factor is the recorded, normalized derived pullback/tensor comparison.
Source: definition clause 5
(blueprint: def-weil-frobenius-coefficient-twists). -/
def rationalTwistStructure (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X : Scheme.{u}} (g : X ⟶ X) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    (K : sfRationalConstructibleCategory l E X)
    (theta : (rationalDerivedPullback l E g).obj K ≅ K) (m : ℤ) :
    (rationalDerivedPullback l E g).obj
        ((sfRationalTwistingFunctor l E X m).obj K) ≅
      (sfRationalTwistingFunctor l E X m).obj K :=
  canonicalRationalPullbackTensor l E g K (sfRationalTwistingCoefficient l E X m) ≪≫
    (rationalDerivedTensor l E X).mapIso
      (Iso.prod theta (rationalDerivedLineMap l E g m))

attribute [local irreducible] rationalTwistStructure

/-- The identical tensor formula in the actual common-stage category.
Source: definition clause 5
(blueprint: def-weil-frobenius-coefficient-twists). -/
def commonTwistStructure (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X : Scheme.{u}} (g : X ⟶ X) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X)
    (theta : (commonStageDerivedPullback l Ω g).obj K ≅ K) (m : ℤ) :
    (commonStageDerivedPullback l Ω g).obj ((sfQbarTwistingFunctor l X Ω m).obj K) ≅
      (sfQbarTwistingFunctor l X Ω m).obj K :=
  canonicalCommonStagePullbackTensor l Ω g K (sfQbarTwistingCoefficient l X Ω m) ≪≫
    (commonStageDerivedTensor l Ω X).mapIso
      (Iso.prod theta (commonDerivedLineMap l Ω g m))

attribute [local irreducible] commonTwistStructure

/-- Pullback/twist commutation before applying a Weil structure.
Source: definition clause 5, tensor comparison followed by tau
(blueprint: def-weil-frobenius-coefficient-twists). -/
def rationalTwistCommutationComponent (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X : Scheme.{u}} (g : X ⟶ X) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)] (m : ℤ)
    (K : sfRationalConstructibleCategory l E X) :
    (rationalDerivedPullback l E g).obj ((sfRationalTwistingFunctor l E X m).obj K) ≅
      (sfRationalTwistingFunctor l E X m).obj ((rationalDerivedPullback l E g).obj K) :=
  canonicalRationalPullbackTensor l E g K (sfRationalTwistingCoefficient l E X m) ≪≫
    (rationalDerivedTensor l E X).mapIso
      (Iso.prod (Iso.refl _) (rationalDerivedLineMap l E g m))

private theorem tensorTwist_naturality {A : Type*} [Category A]
    (F : A ⥤ A) (T : A × A ⥤ A) (e : T ⋙ F ≅ F.prod F ⋙ T)
    (N : A) (t : F.obj N ≅ N) {K L : A} (a : K ⟶ L) :
    F.map (T.map (Prod.mkHom a (𝟙 N))) ≫
        (e.app (L, N) ≪≫ T.mapIso (Iso.prod (Iso.refl _) t)).hom =
      (e.app (K, N) ≪≫ T.mapIso (Iso.prod (Iso.refl _) t)).hom ≫
        T.map (Prod.mkHom (F.map a) (𝟙 N)) := by
  have h := e.hom.naturality (Prod.mkHom a (𝟙 N))
  simp only [Functor.comp_map, Functor.prod_map] at h
  dsimp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom]
  rw [← Category.assoc, h, Category.assoc]
  rw [Category.assoc]
  apply congrArg (fun b ↦ e.hom.app (K, N) ≫ b)
  change T.map _ ≫ T.map _ = T.map _ ≫ T.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg (fun b ↦ T.map b)
  ext <;> simp

/-- Naturality required to make the prescribed tensor comparison a natural isomorphism.
Source: definition clause 5, maps u tensor id
(blueprint: def-weil-frobenius-coefficient-twists).
Proof: canonicalRationalPullbackTensor is natural in both variables. Compose its
naturality square with the tensor map id tensor tau. Functoriality of tensor moves
u past this second factor. The resulting equation is exactly the displayed square. -/
theorem rationalTwistCommutation_naturality (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X : Scheme.{u}} (g : X ⟶ X) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)] (m : ℤ)
    {K L : sfRationalConstructibleCategory l E X} (a : K ⟶ L) :
    (rationalDerivedPullback l E g).map ((sfRationalTwistingFunctor l E X m).map a) ≫
      (rationalTwistCommutationComponent l E g m L).hom =
    (rationalTwistCommutationComponent l E g m K).hom ≫
      (sfRationalTwistingFunctor l E X m).map ((rationalDerivedPullback l E g).map a) := by
  obtain ⟨e, he⟩ := (derivedPullbackTensorIso l E g 0
    (AlgebraicClosure (Padic l))).2.2.2.2.2.2.1
  have h := tensorTwist_naturality (rationalDerivedPullback l E g)
    (rationalDerivedTensor l E X) e (sfRationalTwistingCoefficient l E X m)
    (rationalDerivedLineMap l E g m) a
  rw [he, he] at h
  exact h

attribute [local irreducible] rationalTwistCommutationComponent

/-- The prescribed comparison as a natural isomorphism.
Source: definition clause 5
(blueprint: def-weil-frobenius-coefficient-twists). -/
def rationalTwistCommutation (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X : Scheme.{u}} (g : X ⟶ X) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)] (m : ℤ) :
    sfRationalTwistingFunctor l E X m ⋙ rationalDerivedPullback l E g ≅
      rationalDerivedPullback l E g ⋙ sfRationalTwistingFunctor l E X m :=
  NatIso.ofComponents (rationalTwistCommutationComponent l E g m)
    (fun a ↦ rationalTwistCommutation_naturality l E g m a)

attribute [local irreducible] rationalTwistCommutation

/-- The same commutation component on common-stage representatives.
Source: definition clause 5
(blueprint: def-weil-frobenius-coefficient-twists). -/
def commonTwistCommutationComponent (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X : Scheme.{u}} (g : X ⟶ X) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)] (m : ℤ)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X) :
    (commonStageDerivedPullback l Ω g).obj ((sfQbarTwistingFunctor l X Ω m).obj K) ≅
      (sfQbarTwistingFunctor l X Ω m).obj ((commonStageDerivedPullback l Ω g).obj K) :=
  canonicalCommonStagePullbackTensor l Ω g K (sfQbarTwistingCoefficient l X Ω m) ≪≫
    (commonStageDerivedTensor l Ω X).mapIso
      (Iso.prod (Iso.refl _) (commonDerivedLineMap l Ω g m))

/-- Naturality descends the specified finite-stage square to morphism classes.
Source: definition clause 5
(blueprint: def-weil-frobenius-coefficient-twists).
Proof: choose a common finite coefficient field for the arrow and the Tate line.
The preceding rational tensor-naturality square holds there. The coefficient
comparison cocycles conjugate both sides by the same maps at every enlargement.
Thus the equality passes to the common-stage morphism classes. -/
theorem commonTwistCommutation_naturality (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X : Scheme.{u}} (g : X ⟶ X) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)] (m : ℤ)
    {K L : generalAlgebraicallyClosedConstructibleCategory l Ω X} (a : K ⟶ L) :
    (commonStageDerivedPullback l Ω g).map ((sfQbarTwistingFunctor l X Ω m).map a) ≫
      (commonTwistCommutationComponent l Ω g m L).hom =
    (commonTwistCommutationComponent l Ω g m K).hom ≫
      (sfQbarTwistingFunctor l X Ω m).map ((commonStageDerivedPullback l Ω g).map a) := by
  obtain ⟨e, he⟩ := (derivedPullbackTensorIso l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
      (Padic.finiteCoefficientBase l Ω)) g 0 Ω).2.2.2.2.2.2.2.1
  have h := tensorTwist_naturality (commonStageDerivedPullback l Ω g)
    (commonStageDerivedTensor l Ω X) e (sfQbarTwistingCoefficient l X Ω m)
    (commonDerivedLineMap l Ω g m) a
  rw [he, he] at h
  exact h

attribute [local irreducible] commonTwistCommutationComponent

/-- The common-stage tensor commutation, with its actual normalized components.
Source: definition clause 5
(blueprint: def-weil-frobenius-coefficient-twists). -/
def commonTwistCommutation (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X : Scheme.{u}} (g : X ⟶ X) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)] (m : ℤ) :
    sfQbarTwistingFunctor l X Ω m ⋙ commonStageDerivedPullback l Ω g ≅
      commonStageDerivedPullback l Ω g ⋙ sfQbarTwistingFunctor l X Ω m :=
  NatIso.ofComponents (commonTwistCommutationComponent l Ω g m)
    (fun a ↦ commonTwistCommutation_naturality l Ω g m a)

attribute [local irreducible] commonTwistCommutation

/-- The rational coefficient Weil line, using the geometric semilinear Frobenius.
Source: definition clauses 4--5
(blueprint: def-weil-frobenius-coefficient-twists). -/
def rationalWeilLine (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (m : ℤ) :
    sfWeilComplex D l hl Y₀ E :=
  letI : IsIso (D.geometricFrobenius Y₀).hom := (D.geometricFrobenius Y₀).isIso_hom
  letI : ∀ x : (D.geometricFiber Y₀).left,
    Invertible (l : (D.geometricFiber Y₀).left.residueField x) :=
      fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
  IsoAlgebra.mk (sfRationalTwistingCoefficient l E (D.geometricFiber Y₀).left m)
    (rationalDerivedLineMap l E (D.geometricFrobenius Y₀).hom m)

attribute [local irreducible] rationalWeilLine

/-- Tensoring a rational Weil complex by the normalized coefficient Weil line.
The underlying arrow is u tensor id by the published twisting functor.
Source: definition clause 5
(blueprint: def-weil-frobenius-coefficient-twists). -/
def rationalWeilTwistingFunctor (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (m : ℤ) :
    sfWeilComplex D l hl Y₀ E ⥤ sfWeilComplex D l hl Y₀ E :=
  letI : IsIso (D.geometricFrobenius Y₀).hom := (D.geometricFrobenius Y₀).isIso_hom
  letI : ∀ x : (D.geometricFiber Y₀).left,
    Invertible (l : (D.geometricFiber Y₀).left.residueField x) :=
      fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
  IsoAlgebra.mapOfNatIso (rationalTwistCommutation l E (D.geometricFrobenius Y₀).hom m)

attribute [local irreducible] rationalWeilTwistingFunctor

/-- The coefficient Weil line in the literal common-stage category.
Source: definition clauses 4--5
(blueprint: def-weil-frobenius-coefficient-twists). -/
def commonWeilLine (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (m : ℤ) :
    sfCommonStageWeilComplex D l hl Y₀ Ω :=
  letI : IsIso (D.geometricFrobenius Y₀).hom := (D.geometricFrobenius Y₀).isIso_hom
  letI : ∀ x : (D.geometricFiber Y₀).left,
    Invertible (l : (D.geometricFiber Y₀).left.residueField x) :=
      fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
  IsoAlgebra.mk (sfQbarTwistingCoefficient l (D.geometricFiber Y₀).left Ω m)
    (commonDerivedLineMap l Ω (D.geometricFrobenius Y₀).hom m)

attribute [local irreducible] commonWeilLine

/-- Tensoring a common-stage Weil complex by that same coefficient Weil line.
Source: definition clause 5
(blueprint: def-weil-frobenius-coefficient-twists). -/
def commonWeilTwistingFunctor (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (m : ℤ) :
    sfCommonStageWeilComplex D l hl Y₀ Ω ⥤ sfCommonStageWeilComplex D l hl Y₀ Ω :=
  letI : IsIso (D.geometricFrobenius Y₀).hom := (D.geometricFrobenius Y₀).isIso_hom
  letI : ∀ x : (D.geometricFiber Y₀).left,
    Invertible (l : (D.geometricFiber Y₀).left.residueField x) :=
      fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
  IsoAlgebra.mapOfNatIso (commonTwistCommutation l Ω (D.geometricFrobenius Y₀).hom m)

attribute [local irreducible] commonWeilTwistingFunctor

/-- The coefficient Weil line is a sheaf in the existing constructible heart.
Source: definition clause 4
(blueprint: def-weil-frobenius-coefficient-twists).
Proof: the signed line is an invertible completed module sheaf in degree zero.
Its finite reductions are locally free of rank one and its actual coefficient
rationalization is therefore in the constructible heart. Its Frobenius isomorphism
changes no cohomological degree. This is the heart-carrier predicate used here. -/
theorem rationalWeilLine_heart (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (m : ℤ) :
    sfRationalHeartProperty l E (D.geometricFiber Y₀).left
      ((sfWeilForget D l hl Y₀ E).obj (rationalWeilLine D l hl Y₀ E m)) := by
  let : ∀ x : (D.geometricFiber Y₀).left,
      Invertible (l : (D.geometricFiber Y₀).left.residueField x) :=
    fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
  unfold rationalWeilLine
  change sfRationalHeartProperty l E (D.geometricFiber Y₀).left
    (sfRationalTwistingCoefficient l E (D.geometricFiber Y₀).left m)
  constructor
  all_goals
    refine ⟨sfIntegralTwistingCoefficient l E (D.geometricFiber Y₀).left m,
      ?_, ⟨Iso.refl _⟩⟩
    intro i hi
    change IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((DerivedCategory.singleFunctor _ 0).obj _))
    simp at hi
    have hi0 : i ≠ 0 := by omega
    exact (HomologicalComplex.isZero_single_obj_homology _ _ _ _ hi0).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _) ≪≫
        (DerivedCategory.homologyFunctorFactors _ i).app _)

/-- The coefficient Weil sheaf, in the project's recorded heart subcategory.
Source: definition clause 4
(blueprint: def-weil-frobenius-coefficient-twists). -/
def rationalWeilSheaf (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (m : ℤ) :
    sfWeilSheaf D l hl Y₀ E :=
  ⟨rationalWeilLine D l hl Y₀ E m,rationalWeilLine_heart D l hl Y₀ E m⟩

/-- Common-stage descent preserves the degree-zero coefficient-line heart condition.
Source: definition clause 4
(blueprint: def-weil-frobenius-coefficient-twists).
Proof: the common-stage line is represented at the least finite coefficient field
by the preceding rational degree-zero rank-one sheaf. The common-stage heart is
defined stagewise and finite scalar extension is exact. Hence it has that heart property. -/
theorem commonWeilLine_heart (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p) (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (m : ℤ) :
    sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Ω
      ((sfCommonStageWeilForget D l hl Y₀ Ω).obj (commonWeilLine D l hl Y₀ Ω m)) := by
  let : ∀ x : (D.geometricFiber Y₀).left,
      Invertible (l : (D.geometricFiber Y₀).left.residueField x) :=
    fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
  have h := rationalWeilLine_heart D l hl Y₀
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
      (Padic.finiteCoefficientBase l Ω)) m
  unfold rationalWeilLine at h
  unfold commonWeilLine
  change sfRationalHeartProperty _ _ _
    (sfRationalTwistingCoefficient _ _ _ _) at h
  constructor
  · exact ⟨Padic.finiteCoefficientBase l Ω, _, h.1, ⟨Iso.refl _⟩⟩
  · exact ⟨Padic.finiteCoefficientBase l Ω, _, h.2, ⟨Iso.refl _⟩⟩

/-- The same coefficient Weil sheaf in the actual common-stage heart subcategory.
Source: definition clause 4
(blueprint: def-weil-frobenius-coefficient-twists). -/
def commonWeilSheaf (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (m : ℤ) :
    sfCommonStageWeilSheaf D l hl Y₀ Ω :=
  ⟨commonWeilLine D l hl Y₀ Ω m,commonWeilLine_heart D l hl Y₀ Ω m⟩

end FrobeniusCoefficientTwists

end WeilConjectures
