/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.IntegralCompactSupportCoefficientData
public import Sheaf.Paper.FiniteTateSiteDescent
public import Sheaf.AlgebraicGeometry.RootsOfUnityInverseImageIso
public import Sheaf.Paper.PurInverseImageTensorHom
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.DerivedPullbackTensorIso

/-! # Canonical Frobenius on coefficient twists

Source: main-20261015, def-weil-frobenius-coefficient-twists, clauses 1--5
(blueprint: def-weil-frobenius-coefficient-twists).
The first map below is an actual map of root towers. Its inverse limit, rather than
an arbitrary trivialization of a Tate line, determines the signed coefficient maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme CategoryTheory.Endofunctor
namespace WeilConjectures
namespace FrobeniusCoefficientTwists

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
      proEtaleRootsOfUnityTower X l (Fact.out : l.Prime) :=
  ((proEtaleRootsOfUnityInverseImageIso g).2.1 l Fact.out).choose

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
  sorry

/-- The tensor-power comparisons selected from their unique scalar/root formulas.
Source: definition clauses 2--3
(blueprint: def-weil-frobenius-coefficient-twists). -/
def positiveLineMaps (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (d : ℕ) :
    (modulePull l E g).obj (positiveLine l E Y d) ≅
      positiveLine l E X d :=
  (existsUnique_positiveLineMaps l E g).exists.choose d

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
  sorry

/-- The unique signed inverse-image comparisons at completed coefficients.
Source: definition clause 3
(blueprint: def-weil-frobenius-coefficient-twists). -/
def signedLineMaps (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (m : ℤ) :
    (modulePull l E g).obj (line l E Y m) ≅ line l E X m :=
  (existsUnique_signedLineMaps l E g).exists.choose m

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
  sorry

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
  sorry

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
                  l E g).obj C)))).v i (i - 1) (by omega) = 0 := by
  sorry

/-- The uniquely normalized strict augmentation.
Source: definition clause 4
(blueprint: def-weil-frobenius-coefficient-twists). -/
def pullbackAugmentation (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}}
    (g : X ⟶ Y) :
    (modulePull l E g).mapHomologicalComplex (.up ℤ) ⟶
      integralOperationsPullbackComplexFunctor l E g :=
  (existsUnique_pullbackAugmentation l E g).exists.choose

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
  sorry

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
  (integralDerivedPullbackComparison l E g).app ⟨C, hC⟩ ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map ((pullbackAugmentation l E g).app C))
      (pullbackAugmentation_isIso l E g C hC hK)).symm ≪≫
    ((modulePull l E g).mapDerivedCategoryFactors.app C).symm

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
  sorry

/-- The canonical lambda comparison determined on all good representatives.
Source: definition clause 4
(blueprint: def-weil-frobenius-coefficient-twists). -/
def completedToOrdinary (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :=
  (existsUnique_completedToOrdinary l E g).exists.choose

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
  have h := e.hom.naturality
    (Prod.mkHom a (𝟙 (sfRationalTwistingCoefficient l E X m)))
  simp only [Functor.comp_map, Functor.prod_map] at h
  have heh := fun M N ↦ congrArg Iso.hom (he M N)
  change ∀ M N, e.hom.app (M, N) = _ at heh
  rw [heh, heh] at h
  change (rationalDerivedPullback l E g).map
      ((rationalDerivedTensor l E X).map (Prod.mkHom a (𝟙 _))) ≫ _ = _
  dsimp only [rationalTwistCommutationComponent, Iso.trans_hom, Functor.mapIso_hom,
    Iso.prod_hom, Iso.refl_hom]
  rw [← Category.assoc, h, Category.assoc]
  rw [Category.assoc]
  apply congrArg (fun b ↦
    (canonicalRationalPullbackTensor l E g K (sfRationalTwistingCoefficient l E X m)).hom ≫ b)
  change (rationalDerivedTensor l E X).map _ ≫ (rationalDerivedTensor l E X).map _ =
    (rationalDerivedTensor l E X).map _ ≫ (rationalDerivedTensor l E X).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg (fun b ↦ (rationalDerivedTensor l E X).map b)
  ext <;> simp

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
  have h := e.hom.naturality
    (Prod.mkHom a (𝟙 (sfQbarTwistingCoefficient l X Ω m)))
  simp only [Functor.comp_map, Functor.prod_map] at h
  have heh := fun M N ↦ congrArg Iso.hom (he M N)
  change ∀ M N, e.hom.app (M, N) = _ at heh
  rw [heh, heh] at h
  change (commonStageDerivedPullback l Ω g).map
      ((commonStageDerivedTensor l Ω X).map (Prod.mkHom a (𝟙 _))) ≫ _ = _
  dsimp only [commonTwistCommutationComponent, Iso.trans_hom, Functor.mapIso_hom,
    Iso.prod_hom, Iso.refl_hom]
  rw [← Category.assoc, h, Category.assoc]
  rw [Category.assoc]
  apply congrArg (fun b ↦
    (canonicalCommonStagePullbackTensor l Ω g K (sfQbarTwistingCoefficient l X Ω m)).hom ≫ b)
  change (commonStageDerivedTensor l Ω X).map _ ≫ (commonStageDerivedTensor l Ω X).map _ =
    (commonStageDerivedTensor l Ω X).map _ ≫ (commonStageDerivedTensor l Ω X).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg (fun b ↦ (commonStageDerivedTensor l Ω X).map b)
  ext <;> simp

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

/-- The rational coefficient Weil line, using the geometric semilinear Frobenius.
Source: definition clauses 4--5
(blueprint: def-weil-frobenius-coefficient-twists). -/
def rationalWeilLine (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (m : ℤ) :
    sfWeilComplex D l hl Y₀ E :=
  letI : ∀ x : (D.geometricFiber Y₀).left,
    Invertible (l : (D.geometricFiber Y₀).left.residueField x) :=
      fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
  IsoAlgebra.mk (sfRationalTwistingCoefficient l E (D.geometricFiber Y₀).left m)
    (rationalDerivedLineMap l E (D.geometricFrobenius Y₀).hom m)

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
  letI : ∀ x : (D.geometricFiber Y₀).left,
    Invertible (l : (D.geometricFiber Y₀).left.residueField x) :=
      fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
  IsoAlgebra.mapOfNatIso (rationalTwistCommutation l E (D.geometricFrobenius Y₀).hom m)

/-- The coefficient Weil line in the literal common-stage category.
Source: definition clauses 4--5
(blueprint: def-weil-frobenius-coefficient-twists). -/
def commonWeilLine (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (m : ℤ) :
    sfCommonStageWeilComplex D l hl Y₀ Ω :=
  letI : ∀ x : (D.geometricFiber Y₀).left,
    Invertible (l : (D.geometricFiber Y₀).left.residueField x) :=
      fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
  IsoAlgebra.mk (sfQbarTwistingCoefficient l (D.geometricFiber Y₀).left Ω m)
    (commonDerivedLineMap l Ω (D.geometricFrobenius Y₀).hom m)

/-- Tensoring a common-stage Weil complex by that same coefficient Weil line.
Source: definition clause 5
(blueprint: def-weil-frobenius-coefficient-twists). -/
def commonWeilTwistingFunctor (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (m : ℤ) :
    sfCommonStageWeilComplex D l hl Y₀ Ω ⥤ sfCommonStageWeilComplex D l hl Y₀ Ω :=
  letI : ∀ x : (D.geometricFiber Y₀).left,
    Invertible (l : (D.geometricFiber Y₀).left.residueField x) :=
      fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
  IsoAlgebra.mapOfNatIso (commonTwistCommutation l Ω (D.geometricFrobenius Y₀).hom m)

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
