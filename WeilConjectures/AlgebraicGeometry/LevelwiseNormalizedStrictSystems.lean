/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalSystemTransport
public import WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensorSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic


/-! # Levelwise normalized ordinary strict systems

Source: latest blueprint, lem-coef-finite-exceptional.proof.md, last paragraph,
and sk-prop-pe-unbounded-classical unit/direct-image proofs
(blueprint: def-coef-levelwise-normalized-strict-systems).

All systems are ordinary strict semilinear systems. Bounds are existential at
individual levels, with no bound on the whole derived system. Finite coefficient
exponent n+1 is used throughout.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry SheafOfModules
attribute [local instance 10000] strictEtaleSystemDerived strictEtaleLevelDerived
  exceptionalProSystemDerived exceptionalProLevelDerived

attribute [local instance 30000] exceptionalTransportProEtaleCommRingSheafify
  exceptionalTransportProEtaleAddCommGrpSheafify exceptionalTransportProEtaleAddCommGrpLocal


namespace WeilConjectures.LevelwiseNormalizedAdjointDescent

/-- Fix the existing coefficient-sized small-site witness at its concrete universe.
Source: blueprint size convention
(blueprint: def-coef-levelwise-normalized-strict-systems). -/
local instance (priority := 50000) proSmall (W : Scheme.{u}) : EssentiallySmall.{u + 1} W.ProEt :=
  WeilConjectures.scalarReductionSiteSmall.{u, 0} W


/-- Cache coefficient-sized ring composition on the actual small pro-etale site.
Source: blueprint coefficient system construction
(blueprint: def-coef-levelwise-normalized-strict-systems). -/
local instance proRingCompose (W : Scheme.{u}) :
    (Scheme.ProEt.topology W).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := inferInstance

variable (O : Type (u + 1)) [CommRing O] (ell : O)

/-- Cache the existing abelian structure of the actual strict system category.
Source: blueprint levelwise descent, constructions and conclusions
(blueprint: def-coef-levelwise-normalized-strict-systems). -/
local instance proSystemAbelian (W : Scheme.{u}) :
    Abelian (CoefficientSystem.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology W) O ell) :=
  coefficientSystemAbelian.{u + 1, u, u + 1}

/-- Derived canonical constant-scalar restriction on the ordinary etale level.
Source: blueprint levelwise descent, constructions and conclusions
(blueprint: def-coef-levelwise-normalized-strict-systems). -/
def etaleLevel (W : Scheme.{u}) (n : ℕ) :
    DerivedCategory.{u + 2} (strictEtaleLevel W O ell n) ⥤
      Etale.DerivedCategoryModule (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)) W :=
  letI : HasDerivedCategory.{u + 2}
      (ConstantScalarRestriction.Modules W.smallEtaleTopology
        (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))) :=
    strictEtaleLevelDerived W O ell n
  (ConstantScalarRestriction.restriction W.smallEtaleTopology
    (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))).mapDerivedCategory.{u + 2, u + 1}

/-- Derived canonical constant-scalar restriction on the ordinary pro-etale level.
Source: blueprint levelwise descent, constructions and conclusions
(blueprint: def-coef-levelwise-normalized-strict-systems). -/
def proLevel (W : Scheme.{u}) (n : ℕ) :
    DerivedCategory.{u + 2} (coefficientLevelModules.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology W) O ell n) ⥤
      DerivedCategory.{u + 1} (Sheaf (Scheme.ProEt.topology W)
        (ModuleCat.{u + 1} (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)))) :=
  letI : HasDerivedCategory.{u + 2}
      (ConstantScalarRestriction.Modules (Scheme.ProEt.topology W)
        (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))) :=
    exceptionalProLevelDerived W O ell n
  (ConstantScalarRestriction.restriction (Scheme.ProEt.topology W)
    (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))).mapDerivedCategory.{u + 2, u + 1}

/-- Bounded constructibility and a finite Tor interval on one etale level.
Source: blueprint levelwise descent, constructions and conclusions
(blueprint: def-coef-levelwise-normalized-strict-systems). -/
def etaleFiniteTor (W : Scheme.{u}) (n : ℕ) :
    ObjectProperty (DerivedCategory.{u + 2} (strictEtaleLevel W O ell n)) :=
  fun K ↦ Etale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)))
      W ((etaleLevel O ell W n).obj K) ∧
    ∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn
      (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)) W a b
        ((etaleLevel O ell W n).obj K)

/-- Intrinsic bounded constructibility and finite Tor amplitude on one pro-etale level.
Source: blueprint levelwise descent, constructions and conclusions
(blueprint: def-coef-levelwise-normalized-strict-systems). -/
def proFiniteTor (W : Scheme.{u}) (n : ℕ) :
    ObjectProperty (DerivedCategory.{u + 2}
      (coefficientLevelModules.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W) O ell n)) :=
  fun K ↦ ProEtale.DerivedCategory.boundedConstructibleIntrinsic
      (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)) W ((proLevel O ell W n).obj K) ∧
    ProEtale.DerivedCategory.finiteTorAmplitude
      (ModuleCat.{u + 1} (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))) W
        ((proLevel O ell W n).obj K)

/-- Normalization and bounded constructible finite Tor levels, without common bounds.
Source: blueprint levelwise descent, constructions and conclusions
(blueprint: def-coef-levelwise-normalized-strict-systems). -/
def etaleNormalized (W : Scheme.{u}) (P : StrictEtaleEvaluation W O ell) :
    ObjectProperty (DerivedCategory.{u + 2} (strictEtaleCoefficientSystem W O ell)) :=
  fun M ↦ IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
      (J := W.smallEtaleTopology) O ell P M ∧
    ∀ n : ℕ, etaleFiniteTor O ell W n ((P.evaluation n).obj M)

/-- The intrinsic normalized pro-etale full subcategory, without common bounds.
Source: blueprint levelwise descent, constructions and conclusions
(blueprint: def-coef-levelwise-normalized-strict-systems). -/
def proNormalized (W : Scheme.{u}) (P : ExceptionalProEvaluation W O ell) :
    ObjectProperty (DerivedCategory.{u + 2, u + 1, u + 2}
      (CoefficientSystem.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W) O ell)) :=
  fun M ↦ IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology W) O ell P M ∧
    ∀ n : ℕ, proFiniteTor O ell W n ((P.evaluation n).obj M)

variable {O ell}
variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  (S : StrictEtaleCompactSupport O ell c)

/-- The assumed actual etale system adjunction and its canonical evaluated maps.
Source: blueprint levelwise descent, constructions and conclusions
(blueprint: def-coef-levelwise-normalized-strict-systems). -/
structure EvaluatedAdjunction where
  right : DerivedCategory.{u + 2} (strictEtaleCoefficientSystem Y O ell) ⥤
    DerivedCategory.{u + 2} (strictEtaleCoefficientSystem X O ell)
  adjunction : S.functor ⊣ right
  levelRight : ∀ n : ℕ, DerivedCategory.{u + 2} (strictEtaleLevel Y O ell n) ⥤
    DerivedCategory.{u + 2} (strictEtaleLevel X O ell n)
  levelAdjunction : ∀ n : ℕ, S.levelFunctor n ⊣ levelRight n
  evaluation : ∀ n : ℕ, right ⋙ S.PX.evaluation n ≅ S.PY.evaluation n ⋙ levelRight n
  unit : ∀ (n : ℕ) M,
    (S.PX.evaluation n).map (adjunction.unit.app M) ≫
      (evaluation n).hom.app (S.functor.obj M) ≫
        (levelRight n).map ((S.evaluation n).hom.app M) =
      (levelAdjunction n).unit.app ((S.PX.evaluation n).obj M)
  counit : ∀ (n : ℕ) N,
    (S.levelFunctor n).map ((evaluation n).hom.app N) ≫
      (levelAdjunction n).counit.app ((S.PY.evaluation n).obj N) =
      (S.evaluation n).inv.app (right.obj N) ≫
        (S.PY.evaluation n).map (adjunction.counit.app N)
  quotientOpen : ∀ {m n : ℕ} (h : n ≤ m),
    (S.PX.scalar h).derived ⋙ S.levelDerivedOpen n ≅
      S.levelDerivedOpen m ⋙ (S.PZ.scalar h).derived
  quotientMate : ∀ {m n : ℕ} (h : n ≤ m),
    levelRight m ⋙ (S.PX.scalar h).derived ⟶ (S.PY.scalar h).derived ⋙ levelRight n
  openMate : ∀ {m n : ℕ} (h : n ≤ m),
    (mateEquiv (S.levelDerivedOpenAdjunction m) (S.levelDerivedOpenAdjunction n)
      (.mk _ _ _ _ (quotientOpen h).hom)).natTrans =
      (S.openDerived.derivedTensor h).inv

variable {S}

/-- Canonical compact-support coefficient comparison, defined by the proper
counit mate and the open scalar comparison, without assuming global invertibility.
Source: blueprint compact-support quotient construction
(blueprint: def-coef-levelwise-normalized-strict-systems). -/
def q (A : EvaluatedAdjunction S) {m n : ℕ} (h : n ≤ m) :
    S.levelFunctor m ⋙ (S.PY.scalar h).derived ⟶
      (S.PX.scalar h).derived ⋙ S.levelFunctor n :=
  (Functor.associator _ _ _).hom ≫
    whiskerLeft (S.levelDerivedOpen m)
      (mateEquiv (S.properDerived.level m).adjunction (S.properDerived.level n).adjunction
        (.mk _ _ _ _ (S.properDerived.derivedTensor h).hom)).natTrans ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight (A.quotientOpen h).inv _ ≫ (Functor.associator _ _ _).hom

/-- The specified counit mate of the compact-support quotient comparison.
Source: blueprint levelwise descent, constructions and conclusions
(blueprint: def-coef-levelwise-normalized-strict-systems). -/
def b (A : EvaluatedAdjunction S) {m n : ℕ} (h : n ≤ m) :
    A.levelRight m ⋙ (S.PX.scalar h).derived ⟶
      (S.PY.scalar h).derived ⋙ A.levelRight n :=
  A.quotientMate h

/-- The two assumed equations for the actual scalar-extension adjuncts of transitions.
Source: blueprint levelwise descent, constructions and conclusions
(blueprint: def-coef-levelwise-normalized-strict-systems). -/
def TransitionFormulas (A : EvaluatedAdjunction S) : Prop :=
  (∀ {m n : ℕ} (h : n ≤ m) M,
    (S.PY.scalar h).derived.map ((S.evaluation m).hom.app M) ≫
      (q A h).app ((S.PX.evaluation m).obj M) ≫
      (S.levelFunctor n).map
        (((S.PX.scalar h).derivedAdj.homEquiv _ _).symm ((S.PX.transition h).app M)) =
    ((S.PY.scalar h).derivedAdj.homEquiv _ _).symm
      ((S.PY.transition h).app (S.functor.obj M)) ≫ (S.evaluation n).hom.app M) ∧
  (∀ {m n : ℕ} (h : n ≤ m) N,
    (S.PX.scalar h).derived.map ((A.evaluation m).hom.app N) ≫
      (b A h).app ((S.PY.evaluation m).obj N) ≫
      (A.levelRight n).map
        (((S.PY.scalar h).derivedAdj.homEquiv _ _).symm ((S.PY.transition h).app N)) =
    ((S.PX.scalar h).derivedAdj.homEquiv _ _).symm
      ((S.PX.transition h).app (A.right.obj N)) ≫ (A.evaluation n).hom.app N) ∧
  (∀ {m n : ℕ} (h : n ≤ m) N,
    (q A h).app ((A.levelRight m).obj N) ≫
      (S.levelFunctor n).map ((b A h).app N) ≫
      (A.levelAdjunction n).counit.app ((S.PY.scalar h).derived.obj N) =
    (S.PY.scalar h).derived.map ((A.levelAdjunction m).counit.app N))

end WeilConjectures.LevelwiseNormalizedAdjointDescent
