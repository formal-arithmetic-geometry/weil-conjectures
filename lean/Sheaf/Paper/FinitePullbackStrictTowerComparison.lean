/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.IntegralCompletedTowerPullbackUniverses
public import Sheaf.Paper.PrincipalKoszulStrictReplacement
public import Sheaf.Paper.SfImmersionCompletedPullbackComparison
public import Sheaf.Paper.CompletedPullbackReduction
public import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.DiagramKFlatReplacements
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass

/-! # Natural finite pullback comparison of strict reduction towers

Source: Stacks Project, Tags 099N(5), 0G7E, 06XN, 03EL and 0FNH
(blueprint: lem-a1-finite-pullback-strict-tower-comparison).
The positive exponent n+1 is indexed by n : ℕ. The zigzag lives in strict diagrams
before localization. Its two isomorphisms are fixed on tensor generators.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a v w a' v' w'
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
open WeilConjectures.CompletedTowerIndependent
namespace WeilConjectures.FinitePullbackStrictTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The canonical total-tensor generator, in the existing direct-sum totalization.
Source: Stacks 03EK, 06YM
(blueprint: lem-a1-finite-pullback-strict-tower-comparison). -/
def tensorGenerator (W : Scheme.{t}) (P Q : CochainComplex (Modules l E W) ℤ)
    (p q k : ℤ) (hpq : p + q = k) (U : W.ProEtᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    ((((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)).X k).val.obj U) :=
  coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W) P Q p q k hpq U x y

/-- The degree-zero generator of S_n[0], including restriction along pi_n.
Source: Stacks 099N(5)
(blueprint: lem-a1-finite-pullback-strict-tower-comparison). -/
def residueGenerator (W : Scheme.{t}) (n : ℕ) (U : W.ProEtᵒᵖ)
    (z : (integralCoefficientSheaf l E W n).obj.obj U) :
    (((CochainComplex.singleFunctor (Modules l E W) 0).obj
      (PrincipalKoszulStrictReplacement.residue l E W n)).X 0).val.obj U :=
  ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (PrincipalKoszulStrictReplacement.residue l E W n)).inv.val.app U) z

/-- The cone's degree-zero free generator, fixed by the standard cone inclusion.
Source: Stacks 0A0E
(blueprint: lem-a1-finite-pullback-strict-tower-comparison). -/
def koszulZero (W : Scheme.{t}) (n : ℕ) :
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W) ⟶
      (PrincipalKoszulStrictReplacement.koszul l E W n).X 0 :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W))).inv ≫
      (CochainComplex.mappingCone.inr
        ((CochainComplex.singleFunctor (Modules l E W) 0).map
          (PrincipalKoszulStrictReplacement.multiplication l E W n))).f 0

/-- The cone's degree-minus-one free generator, with the usual Koszul sign convention.
Source: Stacks 0A0E
(blueprint: lem-a1-finite-pullback-strict-tower-comparison). -/
def koszulMinusOne (W : Scheme.{t}) (n : ℕ) :
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W) ⟶
      (PrincipalKoszulStrictReplacement.koszul l E W n).X (-1) :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W))).inv ≫
      (CochainComplex.mappingCone.inl
        ((CochainComplex.singleFunctor (Modules l E W) 0).map
          (PrincipalKoszulStrictReplacement.multiplication l E W n))).v 0 (-1) (by decide)

/-- The two actual Koszul degrees, without excluding either summand.
Source: Stacks 0A0E
(blueprint: lem-a1-finite-pullback-strict-tower-comparison). -/
def koszulDegree (negative : Bool) : ℤ := if negative then -1 else 0

/-- The actual Koszul free basis in either of its two degrees.
Source: Stacks 0A0E
(blueprint: lem-a1-finite-pullback-strict-tower-comparison). -/
def koszulBasis (W : Scheme.{t}) (n : ℕ) (negative : Bool) :
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W) ⟶
      (PrincipalKoszulStrictReplacement.koszul l E W n).X (koszulDegree negative) :=
  match negative with
  | true => koszulMinusOne l E W n
  | false => koszulZero l E W n

/-- The tensor-reduction tower P tensor S_n with actual quotient transitions.
Source: Stacks 099N(5)
(blueprint: lem-a1-finite-pullback-strict-tower-comparison). -/
def tensorReduction (W : Scheme.{t}) (P : CochainComplex (Modules l E W) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (Modules l E W) ℤ :=
  PrincipalKoszulStrictReplacement.targetTower l E W P

variable {X Y : Scheme.{t}} (g : X ⟶ Y)

/-- Ordinary G on cochain complexes, with no exactness assumption.
Source: Stacks 03D2
(blueprint: lem-a1-finite-pullback-strict-tower-comparison). -/
def G : CochainComplex (Modules l E Y) ℤ ⥤ CochainComplex (Modules l E X) ℤ :=
  (pull l E g).mapHomologicalComplex (.up ℤ)

/-- The canonical generator of ordinary pullback, fixed by its adjunction unit.
Source: Stacks 03D2
(blueprint: lem-a1-finite-pullback-strict-tower-comparison). -/
def generator (M : Modules l E Y) (V : Y.ProEt) (x : M.val.obj (op V)) :
    ((pull l E g).obj M).val.obj (op ((Scheme.proEtaleBaseChange g).obj V)) :=
  ((adjunction l E g).unit.app M).val.app (op V) x

/-- B_g^0 is the existing strict finite pullback tower, transposed degreewise.
Source: Stacks 099N(5), 06YY
(blueprint: lem-a1-finite-pullback-strict-tower-comparison). -/
def finiteComplex : CochainComplex (Modules l E Y) ℤ ⥤
    CochainComplex (Towers l E X) ℤ :=
  integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X

/-- V_g composed with the specified derived strict reduction.
Source: Stacks 099N(5)
(blueprint: lem-a1-finite-pullback-strict-tower-comparison). -/
def pulledReduction : DerivedCategory (Modules l E Y) ⥤ DerivedCategory (Towers l E X) :=
  (reductionPair l E Y).functor ⋙ derivedPull l E g

/-- The strict replacement H(P) with transitions id_P tensor (t,1).
Source: Stacks 0A0E
(blueprint: lem-a1-finite-pullback-strict-tower-comparison). -/
def H (W : Scheme.{t}) (P : CochainComplex (Modules l E W) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (Modules l E W) ℤ :=
  PrincipalKoszulStrictReplacement.sourceTower l E W P

/-- The specified augmentation H(P) to P tensor S_n as a strict natural transformation.
Source: Stacks 093M
(blueprint: lem-a1-finite-pullback-strict-tower-comparison). -/
def augmentation (W : Scheme.{t}) (P : CochainComplex (Modules l E W) ℤ) :
    H l E W P ⟶ tensorReduction l E W P :=
  PrincipalKoszulStrictReplacement.comparison l E W P

/-- Pull a diagram back term by term, retaining all maps of the diagram.
Source: Stacks 099N(5)
(blueprint: lem-a1-finite-pullback-strict-tower-comparison). -/
def diagramPull : (ℕᵒᵖ ⥤ CochainComplex (Modules l E Y) ℤ) ⥤
    (ℕᵒᵖ ⥤ CochainComplex (Modules l E X) ℤ) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (G l E g)

/-- Normalization of P tensor S_n to the recorded ordinary scalar extension.
Both maps are balanced and the inverse inserts 1. This equation fixes all tensors.
Source: Stacks 03EK
(blueprint: lem-a1-finite-pullback-strict-tower-comparison). -/
def ReductionNormalization (W : Scheme.{t}) (P : CochainComplex (Modules l E W) ℤ)
    (e : tensorReduction l E W P ≅ ((reductionComplex l E W).obj P).asFunctor) : Prop :=
  ∀ (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ) (x : (P.X i).val.obj U)
      (z : (integralCoefficientSheaf l E W n).obj.obj U),
    (((e.hom.app (op n)).f i).val.app U)
        (tensorGenerator l E W P
          ((CochainComplex.singleFunctor (Modules l E W) 0).obj
            (PrincipalKoszulStrictReplacement.residue l E W n))
          i 0 i (add_zero i) U x (residueGenerator l E W n U z)) =
      unrestrictedIntegralTensorSection l E W n (P.X i) U z x

/-- Normalization of G(P tensor Q_n) to GP tensor Q'_n on both Koszul summands.
The scalar b stays in the first factor. Thus the map uses the actual structural
ring map, respects the unit, and has the inverse inserting 1.
Source: Stacks 03EL, 07A4
(blueprint: lem-a1-finite-pullback-strict-tower-comparison). -/
def KoszulNormalization (P : CochainComplex (Modules l E Y) ℤ)
    (e : (diagramPull l E g).obj (H l E Y P) ≅ H l E X ((G l E g).obj P)) : Prop :=
  ∀ (n : ℕ) (negative : Bool) (p k : ℤ)
      (hp : p + koszulDegree negative = k) (V : Y.ProEt)
      (x : (P.X p).val.obj (op V))
      (b : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
        (op ((Scheme.proEtaleBaseChange g).obj V))),
    (((e.hom.app (op n)).f k).val.app (op ((Scheme.proEtaleBaseChange g).obj V)))
      (b • generator l E g (((H l E Y P).obj (op n)).X k) V
        (tensorGenerator l E Y P (PrincipalKoszulStrictReplacement.koszul l E Y n)
          p (koszulDegree negative) k hp (op V) x
            ((koszulBasis l E Y n negative).val.app (op V)
              (1 : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V))))) =
      tensorGenerator l E X ((G l E g).obj P)
        (PrincipalKoszulStrictReplacement.koszul l E X n)
        p (koszulDegree negative) k hp (op ((Scheme.proEtaleBaseChange g).obj V))
        (b • generator l E g (P.X p) V x)
        ((koszulBasis l E X n negative).val.app
          (op ((Scheme.proEtaleBaseChange g).obj V))
          (1 : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
            (op ((Scheme.proEtaleBaseChange g).obj V))))

/-- Balanced normalization of GP tensor S'_n to Res_n g_n^*(P tensor S_n).
It sends (x tensor b) tensor a to x tensor pi_n(b)*a. The equation on a=1,
and linearity over R', determine all a locally because pi_n is locally surjective.
Source: Stacks 03EK, 03EL
(blueprint: lem-a1-finite-pullback-strict-tower-comparison). -/
def BalancedNormalization (P : CochainComplex (Modules l E Y) ℤ)
    (e : tensorReduction l E X ((G l E g).obj P) ≅
      ((finiteComplex l E g).obj P).asFunctor) : Prop :=
  ∀ (n : ℕ) (i : ℤ) (V : Y.ProEt) (x : (P.X i).val.obj (op V))
      (b : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
        (op ((Scheme.proEtaleBaseChange g).obj V))),
    (((e.hom.app (op n)).f i).val.app (op ((Scheme.proEtaleBaseChange g).obj V)))
        (tensorGenerator l E X ((G l E g).obj P)
          ((CochainComplex.singleFunctor (Modules l E X) 0).obj
            (PrincipalKoszulStrictReplacement.residue l E X n))
          i 0 i (add_zero i) (op ((Scheme.proEtaleBaseChange g).obj V))
          (b • generator l E g (P.X i) V x)
          (residueGenerator l E X n (op ((Scheme.proEtaleBaseChange g).obj V)) 1)) =
      ((limit.π (integralCoefficientSheafSystem l E X) (op n)).hom.app
          (op ((Scheme.proEtaleBaseChange g).obj V)) b) •
        (@id (((integralOperationsLevelPullback l E g n).obj
            (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i)).val.obj
              (op ((Scheme.proEtaleBaseChange g).obj V)))
          (integralOperationsPullbackGenerator l E g n
            (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
            (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x)))

/-- The ordinary reduction at level n, retaining its completed coefficient action.
Source: Stacks 06YY
(blueprint: lem-a1-finite-pullback-strict-tower-comparison). -/
def reductionLevelModules (W : Scheme.{t}) (n : ℕ) :=
  unrestrictedIntegralReductionFunctor l E W n ⋙
    SheafOfModules.restrictScalars
      (limit.π (integralCoefficientSheafSystem l E W) (op n))

/-- The existing additive structure on ordinary reduction followed by restriction.
Source: Stacks 06YY
(blueprint: lem-a1-finite-pullback-strict-tower-comparison). -/
instance reductionLevelModules_additive (W : Scheme.{t}) (n : ℕ) :
    (reductionLevelModules l E W n).Additive := by
  unfold reductionLevelModules
  infer_instance

/-- The module functor whose termwise lift is the nth finite pullback level.
Source: Stacks 03D2
(blueprint: lem-a1-finite-pullback-strict-tower-comparison). -/
def finiteLevelModules (n : ℕ) :=
  unrestrictedIntegralReductionFunctor l E Y n ⋙ integralOperationsLevelPullback l E g n ⋙
    SheafOfModules.restrictScalars
      (limit.π (integralCoefficientSheafSystem l E X) (op n))

/-- Additivity inherited from reduction, finite inverse image and restriction.
Source: Stacks 03D2
(blueprint: lem-a1-finite-pullback-strict-tower-comparison). -/
instance finiteLevelModules_additive (n : ℕ) : (finiteLevelModules l E g n).Additive := by
  have := integralOperationsLevelPullback_additive l E g n
  unfold finiteLevelModules
  infer_instance

/-- A shift on the reduction complex is the standard termwise shift at every level.
Source: Stacks 014E, 0FNH
(blueprint: lem-a1-finite-pullback-strict-tower-comparison). -/
def ReductionShiftNormalization (W : Scheme.{t})
    (c : (reductionComplex l E W).CommShift ℤ) : Prop :=
  ∀ (P : CochainComplex (Modules l E W) ℤ) (r i : ℤ) (n : ℕ),
    (((Functor.commShiftIso (reductionComplex l E W) (self := c) r).hom.app P).f i).app
        (op n) =
      (((reductionLevelModules l E W n).mapCochainComplexShiftIso r).hom.app P).f i

/-- A shift on B_g^0 is the exact finite termwise shift, without a free automorphism.
Source: Stacks 014E, 0FNH
(blueprint: lem-a1-finite-pullback-strict-tower-comparison). -/
def FiniteShiftNormalization (c : (finiteComplex l E g).CommShift ℤ) : Prop :=
  ∀ (P : CochainComplex (Modules l E Y) ℤ) (r i : ℤ) (n : ℕ),
    (((Functor.commShiftIso (finiteComplex l E g) (self := c) r).hom.app P).f i).app
        (op n) =
      (((finiteLevelModules l E g n).mapCochainComplexShiftIso r).hom.app P).f i

/-- The canonical derived shift is fixed by its counit on actual representatives.
This equation makes sense even where that counit is not invertible.
Source: Stacks 06XN, 05SE
(blueprint: lem-a1-finite-pullback-strict-tower-comparison). -/
def ShiftDescent {A : Type a} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {D : Type a'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
    (F : CochainComplex A ℤ ⥤ CochainComplex D ℤ)
    (L : DerivedCategory A ⥤ DerivedCategory D)
    (ε : DerivedCategory.Q ⋙ L ⟶ F ⋙ DerivedCategory.Q)
    (cF : F.CommShift ℤ) (cL : L.CommShift ℤ) : Prop :=
  ∀ (P : CochainComplex A ℤ) (r : ℤ),
    L.map ((DerivedCategory.Q.commShiftIso r).hom.app P) ≫
        (Functor.commShiftIso L (self := cL) r).hom.app (DerivedCategory.Q.obj P) ≫
        (ε.app P)⟦r⟧' =
      ε.app (P⟦r⟧) ≫
        DerivedCategory.Q.map ((Functor.commShiftIso F (self := cF) r).hom.app P) ≫
        (DerivedCategory.Q.commShiftIso r).hom.app (F.obj P)

/-- The composite reduction/tower-pullback shift s^V, with both factors specified.
Source: Stacks 05SE, 06XN
(blueprint: lem-a1-finite-pullback-strict-tower-comparison). -/
def pulledShift (cR : (reductionPair l E Y).functor.CommShift ℤ)
    (cV : (derivedPull l E g).CommShift ℤ) (r : ℤ)
    (K : DerivedCategory (Modules l E Y)) :
    (pulledReduction l E g).obj (K⟦r⟧) ⟶ ((pulledReduction l E g).obj K)⟦r⟧ :=
  (derivedPull l E g).map
      ((Functor.commShiftIso (reductionPair l E Y).functor (self := cR) r).hom.app K) ≫
    (Functor.commShiftIso (derivedPull l E g) (self := cV) r).hom.app
      ((reductionPair l E Y).functor.obj K)

set_option genSizeOfSpec false
set_option genInjectivity false

/-- All clauses of the strict comparison, with its prescribed maps and computation.
The natural isomorphism is on entire derived categories; naturality therefore
includes roofs and inverse quasi-isomorphisms, with no choice of representatives.
Source: Stacks 099N(5), 0G7E, 06XN, 03EL and 0FNH
(blueprint: lem-a1-finite-pullback-strict-tower-comparison). -/
structure Comparison where
  B : DerivedPair l E Y X (finiteComplex l E g)
  b : pulledReduction l E g ≅ B.functor
  reductionIso : ∀ (P : CochainComplex (Modules l E Y) ℤ),
    integralOperationsGoodComplex l E Y P →
      (tensorReduction l E Y P ≅ ((reductionComplex l E Y).obj P).asFunctor)
  reduction_normalization : ∀ P hP, ReductionNormalization l E Y P (reductionIso P hP)
  koszulIso : ∀ (P : CochainComplex (Modules l E Y) ℤ),
    integralOperationsGoodComplex l E Y P →
      ((diagramPull l E g).obj (H l E Y P) ≅ H l E X ((G l E g).obj P))
  koszul_normalization : ∀ P hP, KoszulNormalization l E g P (koszulIso P hP)
  balancedIso : ∀ (P : CochainComplex (Modules l E Y) ℤ),
    integralOperationsGoodComplex l E Y P →
      (tensorReduction l E X ((G l E g).obj P) ≅ ((finiteComplex l E g).obj P).asFunctor)
  balanced_normalization : ∀ P hP, BalancedNormalization l E g P (balancedIso P hP)
  pull_good : ∀ P, integralOperationsGoodComplex l E Y P →
    integralOperationsGoodComplex l E X ((G l E g).obj P)
  koszul_pull_good : ∀ P, integralOperationsGoodComplex l E Y P →
    ∀ n : ℕ, integralOperationsGoodComplex l E X
      (((diagramPull l E g).obj (H l E Y P)).obj (op n))
  middle_quasiIso : ∀ P, integralOperationsGoodComplex l E Y P →
    ∀ n : ℕ, QuasiIso ((augmentation l E X ((G l E g).obj P)).app (op n))
  reductionH : ∀ (P : CochainComplex (Modules l E Y) ℤ),
    integralOperationsGoodComplex l E Y P →
      ((reductionPair l E Y).functor.obj (DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj ((transpose l E Y).obj (H l E Y P)))
  reductionH_normalization : ∀ P hP,
    (reductionH P hP).hom ≫
        DerivedCategory.Q.map ((transpose l E Y).map
          (augmentation l E Y P ≫ (reductionIso P hP).hom)) =
      (reductionPair l E Y).counit.app P
  zigzag : ∀ P hP,
    (derivedPull l E g).map (reductionH P hP).hom ≫
        (derivedCounit l E g).app ((transpose l E Y).obj (H l E Y P)) ≫
        DerivedCategory.Q.map ((transpose l E X).map (koszulIso P hP).hom) ≫
        DerivedCategory.Q.map
          ((transpose l E X).map (augmentation l E X ((G l E g).obj P))) ≫
        DerivedCategory.Q.map ((transpose l E X).map (balancedIso P hP).hom) =
      b.hom.app (DerivedCategory.Q.obj P) ≫ B.counit.app P
  reductionChainShift : (reductionComplex l E Y).CommShift ℤ
  reductionChainShift_normalization : ReductionShiftNormalization l E Y reductionChainShift
  reductionShift : (reductionPair l E Y).functor.CommShift ℤ
  reductionShift_descent : ShiftDescent (A := Modules l E Y) (D := Towers l E Y)
    (reductionComplex l E Y) (reductionPair l E Y).functor
    (reductionPair l E Y).counit reductionChainShift reductionShift
  towerShift : (derivedPull l E g).CommShift ℤ
  towerShift_descent : ShiftDescent ((towerPull l E g).mapHomologicalComplex (.up ℤ))
    (derivedPull l E g) (derivedCounit l E g) inferInstance towerShift
  finiteChainShift : (finiteComplex l E g).CommShift ℤ
  finiteChainShift_normalization : FiniteShiftNormalization l E g finiteChainShift
  finiteShift : B.functor.CommShift ℤ
  finiteShift_descent : ShiftDescent (A := Modules l E Y) (D := Towers l E X)
    (finiteComplex l E g) B.functor B.counit finiteChainShift finiteShift
  shifts : ∀ (K : DerivedCategory (Modules l E Y)) (r : ℤ),
    b.hom.app (K⟦r⟧) ≫
        (Functor.commShiftIso B.functor (self := finiteShift) r).hom.app K =
      pulledShift l E g reductionShift towerShift r K ≫ (b.hom.app K)⟦r⟧'

/-- Strict finite pullback and derived strict tower pullback have the normalized
natural comparison, including arbitrary derived arrows and every integer shift.

Source: Stacks Project, proetale.tex Tag 099N(5), sites-cohomology.tex Tags 0G7E,
06YS, 06YT, 06YY, 0G7D, 07A4, sites-modules.tex 03EK/03EL, and derived.tex 06XN.
(blueprint: lem-a1-finite-pullback-strict-tower-comparison).

Proof:
1. Apply flat-term K-flat resolutions (lem-pc-kflat-resolution), change-of-rings
   invariance (lem-pur-derived-change-of-rings), exact finite inverse image
   (prop-weil-pbc-proetale-constant-exact), and levelwise exactness of towers.
   The resolving-class theorem lem-pur-left-derived-from-kflat-class descends B^0
   with its universal counit and representative computation to B on all of D(R).
2. Use lem-a1-principal-koszul-strict-replacement to replace P tensor S by
   H(P)=P tensor Q, with transitions id tensor (t,1) and the actual augmentation.
   The diagram resolving class of def-weil-pbc-completed-pullback and
   lem-weil-pbc-diagram-kflat-replacements computes V on H(P).
3. Apply lem-weil-pbc-ringed-topoi-derived-tensor-pullback (Stacks 0G7E) to P
   and to each P tensor Q_n. Their images under G are K-flat with flat terms.
   No invertibility or flatness of the completed coefficient map is needed.
4. The ordinary comparison lem-pur-cochain-pullback-tensor-coherence and the
   action unitor identify GQ_n with Q'_n. Constants preserve t, so (t,1) maps
   to (t,1). Its total tensor map is uniquely fixed on the two Koszul generators
   by KoszulNormalization, with no sign or scalar automorphism introduced.
5. Apply principal Koszul replacement on X to GP, now known to be flat-term
   K-flat. The middle augmentation is a levelwise quasi-isomorphism. Levelwise
   abelianness makes its transposition a quasi-isomorphism of strict towers.
6. Constant coefficient transport (prop-weil-pbc-proetale-constant-ring-map)
   identifies g^-1 S_n with S'_n. The coefficient projection square commutes by
   directRingMap. Tensor association identifies both GP tensor S'_n and g_n^*P_n
   with g^-1 P tensor S'_n. The forward formula is (x tensor b) tensor a mapped
   to x tensor pi_n(b)*a; its inverse inserts 1. The balanced maps commute with
   restrictions and the differentials, giving BalancedNormalization.
7. Quotient reduction commutes with those formulas: q(pi_(n+1)(b)*a) equals
   pi_n(b)*q(a). Thus both isomorphisms and the augmentation form strict maps.
   On a pulled-back quotient-unit generator this gives pi_n(b), exactly the
   ordinary and derived finite evaluation normalizations fixed by the recorded
   completed-pullback and def-a1-integral-completed-pullback-interfaces APIs.
8. All maps are natural in chain maps. The localization equivalence of
   lem-weil-pbc-site-derived-tensor-descent uniquely extends them to all derived
   morphisms. Chain naturality also gives naturality for inverse resolving
   quasi-isomorphisms, proving independence of representatives and linearity.
9. In lem-weil-pbc-total-tensor-integer-shifts the first-variable tensor shift
   is unsigned. Termwise pullback shifts are identities on terms. Hence every
   arrow of the zigzag commutes with them on complexes. The canonical derived
   shift comparisons are their counit-normalized descents. Localize the chain
   equality to obtain sB after b(K[r]) = b(K)[r] after sV for every K and r. -/
theorem finite_pullback_strict_tower_comparison
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    Nonempty (Comparison l E g) := by
  sorry

end WeilConjectures.FinitePullbackStrictTower
