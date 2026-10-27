/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.Paper.IntegralCompletedTowerPullbackUniverses
public import Sheaf.Paper.PrincipalKoszulStrictReplacement
public import Sheaf.Paper.CompletedPullbackUniverseTransportData
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # Shared strict finite-pullback tower data and generators

Source: Stacks Project, Tags 03EK, 03EL, 099N(5), 0A0E and 07A4;
finite-map pullback proof, balanced and pulled-Koszul comparisons
(blueprint: def-a1-finite-pullback-strict-tower-data).
These definitions belong below both comparisons, independently of their parent theorem.
Positive exponent n+1 is indexed by n : ℕ; scheme and coefficient universes are independent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u r s v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
attribute [local irreducible] WeilConjectures.unrestrictedIntegralReductionFunctor
  WeilConjectures.CompletedTowerIndependent.pull
open WeilConjectures.CompletedTowerIndependent
namespace WeilConjectures.FinitePullbackStrictTowerData

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The canonical total-tensor generator, in the existing direct-sum totalization.
Source: Stacks 03EK, 06YM
(blueprint: def-a1-finite-pullback-strict-tower-data). -/
def tensorGenerator (W : Scheme.{t}) (P Q : CochainComplex (Modules l E W) ℤ)
    (p q k : ℤ) (hpq : p + q = k) (U : W.ProEtᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    ((((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)).X k).val.obj U) :=
  coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W) P Q p q k hpq U x y

/-- The degree-zero generator of S_n[0], including restriction along pi_n.
Source: Stacks 099N(5)
(blueprint: def-a1-finite-pullback-strict-tower-data). -/
def residueGenerator (W : Scheme.{t}) (n : ℕ) (U : W.ProEtᵒᵖ)
    (z : (integralCoefficientSheaf l E W n).obj.obj U) :
    (((CochainComplex.singleFunctor (Modules l E W) 0).obj
      (PrincipalKoszulStrictReplacement.residue l E W n)).X 0).val.obj U :=
  ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (PrincipalKoszulStrictReplacement.residue l E W n)).inv.val.app U) z

/-- The cone's degree-zero free generator, fixed by the standard cone inclusion.
Source: Stacks 0A0E
(blueprint: def-a1-finite-pullback-strict-tower-data). -/
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
(blueprint: def-a1-finite-pullback-strict-tower-data). -/
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
(blueprint: def-a1-finite-pullback-strict-tower-data). -/
def koszulDegree (negative : Bool) : ℤ := if negative then -1 else 0

/-- The actual Koszul free basis in either of its two degrees.
Source: Stacks 0A0E
(blueprint: def-a1-finite-pullback-strict-tower-data). -/
def koszulBasis (W : Scheme.{t}) (n : ℕ) (negative : Bool) :
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W) ⟶
      (PrincipalKoszulStrictReplacement.koszul l E W n).X (koszulDegree negative) :=
  match negative with
  | true => koszulMinusOne l E W n
  | false => koszulZero l E W n

/-- Functorial P-first total tensor with the actual restricted quotient tower.
Source: Stacks 03EK (blueprint: def-a1-finite-pullback-strict-tower-data). -/
def reductions (W : Scheme.{t}) : CochainComplex (Modules l E W) ℤ ⥤
    (ℕᵒᵖ ⥤ CochainComplex (Modules l E W) ℤ) :=
  (SheafOfModules.KFlatTotalTensorModel.tensor
    (completedIntegralCommRingSheafUnrestricted l E W)).map₂CochainComplex ⋙
      (Functor.whiskeringLeft ℕᵒᵖ _ _).obj
        (Functor.ofOpSequence (PrincipalKoszulStrictReplacement.residueStep l E W) ⋙
          CochainComplex.singleFunctor (Modules l E W) 0)

/-- Functorial P-first total tensor with the specified principal Koszul tower.
Source: Stacks 03EK, 0A0E
(blueprint: def-a1-finite-pullback-strict-tower-data). -/
def koszuls (W : Scheme.{t}) : CochainComplex (Modules l E W) ℤ ⥤
    (ℕᵒᵖ ⥤ CochainComplex (Modules l E W) ℤ) :=
  (SheafOfModules.KFlatTotalTensorModel.tensor
    (completedIntegralCommRingSheafUnrestricted l E W)).map₂CochainComplex ⋙
      (Functor.whiskeringLeft ℕᵒᵖ _ _).obj
        (principalKoszulTower (completedIntegralCommRingSheafUnrestricted l E W)
          (PrincipalKoszulStrictReplacement.uniformizer l E W))

/-- The tensor-reduction tower P tensor S_n with actual quotient transitions.
Source: Stacks 099N(5)
(blueprint: def-a1-finite-pullback-strict-tower-data). -/
def tensorReduction (W : Scheme.{t}) (P : CochainComplex (Modules l E W) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (Modules l E W) ℤ :=
  (reductions l E W).obj P

variable {X Y : Scheme.{t}} (g : X ⟶ Y)

/-- Ordinary G on cochain complexes, with no exactness assumption.
Source: Stacks 03D2
(blueprint: def-a1-finite-pullback-strict-tower-data). -/
def G : CochainComplex (Modules l E Y) ℤ ⥤ CochainComplex (Modules l E X) ℤ :=
  (pull l E g).mapHomologicalComplex (.up ℤ)

/-- The canonical generator of ordinary pullback, fixed by its adjunction unit.
Source: Stacks 03D2
(blueprint: def-a1-finite-pullback-strict-tower-data). -/
def generator (M : Modules l E Y) (V : Y.ProEt) (x : M.val.obj (op V)) :
    ((pull l E g).obj M).val.obj (op ((Scheme.proEtaleBaseChange g).obj V)) :=
  ((adjunction l E g).unit.app M).val.app (op V) x

/-- B_g^0 is the existing strict finite pullback tower, transposed degreewise.
Source: Stacks 099N(5), 06YY
(blueprint: def-a1-finite-pullback-strict-tower-data). -/
def finiteComplex : CochainComplex (Modules l E Y) ℤ ⥤
    CochainComplex (Towers l E X) ℤ :=
  integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X

/-- The strict replacement H(P) with transitions id_P tensor (t,1).
Source: Stacks 0A0E
(blueprint: def-a1-finite-pullback-strict-tower-data). -/
def H (W : Scheme.{t}) (P : CochainComplex (Modules l E W) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (Modules l E W) ℤ :=
  (koszuls l E W).obj P

/-- The specified augmentation H(P) to P tensor S_n as a strict natural transformation.
Source: Stacks 093M
(blueprint: def-a1-finite-pullback-strict-tower-data). -/
def augmentation (W : Scheme.{t}) (P : CochainComplex (Modules l E W) ℤ) :
    H l E W P ⟶ tensorReduction l E W P :=
  PrincipalKoszulStrictReplacement.comparison l E W P

/-- Pull a diagram back term by term, retaining all maps of the diagram.
Source: Stacks 099N(5)
(blueprint: def-a1-finite-pullback-strict-tower-data). -/
def diagramPull : (ℕᵒᵖ ⥤ CochainComplex (Modules l E Y) ℤ) ⥤
    (ℕᵒᵖ ⥤ CochainComplex (Modules l E X) ℤ) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (G l E g)

/-- Normalization of P tensor S_n to the recorded ordinary scalar extension.
Both maps are balanced and the inverse inserts 1. This equation fixes all tensors.
Source: Stacks 03EK
(blueprint: def-a1-finite-pullback-strict-tower-data). -/
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
(blueprint: def-a1-finite-pullback-strict-tower-data). -/
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
(blueprint: def-a1-finite-pullback-strict-tower-data). -/
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

/-- The existing finite strict tower, expressed with the recorded transposition API.
Source: Stacks 06YY (blueprint: def-a1-finite-pullback-strict-tower-data). -/
def finite {X Y : Scheme.{t}} (g : X ⟶ Y) : CochainComplex (Modules l E Y) ℤ ⥤
    (ℕᵒᵖ ⥤ CochainComplex (Modules l E X) ℤ) :=
  finiteComplex l E g ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex

variable {X Y : Scheme.{t}} (g : X ⟶ Y)

/-- The C comparison is fixed on pulled quotient-unit generators, including outer scalars.
Source: Stacks 03EL (blueprint: def-a1-finite-pullback-strict-tower-data). -/
def QuotientUnitNormalization
    (c : reductions l E Y ⋙ diagramPull l E g ≅ finite l E g) :
    Prop :=
  ∀ (P : CochainComplex (Modules l E Y) ℤ) (n : ℕ) (i : ℤ) (V : Y.ProEt)
      (x : (P.X i).val.obj (op V))
      (b : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
        (op ((Scheme.proEtaleBaseChange g).obj V))),
    ((((c.hom.app P).app (op n)).f i).val.app
      (op ((Scheme.proEtaleBaseChange g).obj V)))
      (b • generator l E g ((((reductions l E Y).obj P).obj (op n)).X i) V
        (tensorGenerator l E Y P
          ((CochainComplex.singleFunctor (Modules l E Y) 0).obj
            (PrincipalKoszulStrictReplacement.residue l E Y n))
          i 0 i (add_zero i) (op V) x (residueGenerator l E Y n (op V) 1))) =
      b • (@id (((((finite l E g).obj P).obj (op n)).X i).val.obj
          (op ((Scheme.proEtaleBaseChange g).obj V)))
        (integralOperationsPullbackGenerator l E g n
          (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
          (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x)))


end WeilConjectures.FinitePullbackStrictTowerData
