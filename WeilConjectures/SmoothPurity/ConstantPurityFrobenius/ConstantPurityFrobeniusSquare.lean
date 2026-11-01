/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstantPurityFrobenius.CommonConstantUnitFrobenius
public import WeilConjectures.SmoothPurity.RationalSmoothPurityCanonical.RationalSmoothPurityCanonical
public import WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure
public import WeilConjectures.SmoothPurity.FrobeniusCoefficientTwists.FrobeniusCoefficientTwistsCanonical
public import WeilConjectures.DeligneLaumon.FieldWeilShriekShiftData
public import WeilConjectures.PoincareDuality.SemilinearFieldOperationLifts
public import WeilConjectures.SixFunctors.FrobeniusExchange.FrobeniusGeometricExchange
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SmoothPurity.Common.CommonFrobeniusSquareNormalization
import WeilConjectures.SmoothPurity.RationalWeilPurity.RationalWeilPurityNaturalityMate
import WeilConjectures.SmoothPurity.Frobenius.FrobeniusCompactRationalNormalization
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Constant purity and its canonical Frobenius square

Source: main-20261015, cor-pur-adic-and-rational-smooth-dualizing-complexes.proof.md,
first sentence, and thm-pur-weil-equivariance-of-purity-and-trace.proof.md, Steps 1--2
(blueprint: lem-pur-constant-purity-frobenius-square).

The auxiliary unit map retains the strict Roos normalization of the constant pair.
All field maps are its actual localization and finite-stage inclusion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstantPurityFrobenius

section SquareData
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X₀ Y₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
  [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
  [∀ x : (D.geometricFiber X₀).left,
    Invertible (l : (D.geometricFiber X₀).left.residueField x)]
  [∀ y : (D.geometricFiber Y₀).left,
    Invertible (l : (D.geometricFiber Y₀).left.residueField y)]

/-- The fixed common-stage Frobenius pullback on the source.
Source: canonical Frobenius square conventions
(blueprint: lem-pur-constant-purity-frobenius-square). -/
abbrev sourceFrobenius := sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω

/-- The fixed common-stage Frobenius pullback on the target.
Source: canonical Frobenius square conventions
(blueprint: lem-pur-constant-purity-frobenius-square). -/
abbrev targetFrobenius := sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω

variable
  [xft : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k))]
  [xqc : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k))]
  [yft : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k))]
  [yqc : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k))]
  [fover : @Scheme.Hom.IsOver (D.geometricFiber X₀).left
    (D.geometricFiber Y₀).left (FrobeniusExchange.fiberMap D f₀) (Spec (.of D.k))
    inferInstance inferInstance]
  [fsep : IsSeparated (FrobeniusExchange.fiberMap D f₀)]
  [fft : LocallyOfFiniteType (FrobeniusExchange.fiberMap D f₀)]
  [fqc : QuasiCompact (FrobeniusExchange.fiberMap D f₀)]

variable (c₀ : Compactification f₀.left)
  (S : @ConstructibleExceptionalCoefficients.System l inferInstance Ω
    inferInstance inferInstance inferInstance D hl
    (D.geometricFiber X₀).left (D.geometricFiber Y₀).left
    (FrobeniusExchange.fiberMap D f₀) inferInstance inferInstance
    xft xqc yft yqc fover fsep fft fqc)

/-- The chosen compactification and its prescribed exceptional adjunction.
Source: compact-support mate in the statement
(blueprint: lem-pur-constant-purity-frobenius-square). -/
abbrev operation := S.ring.operation (FrobeniusExchange.geometricCompactification D f₀ c₀)

set_option linter.unusedSectionVars false in
/-- The model recipe has exactly the recorded rational compact-support endpoints.
Source: compact-support exchange, definition of its compact recipe
(blueprint: lem-pur-constant-purity-frobenius-square).
Proof: unfold modelRationalSource and modelRationalTarget. The compact branch is
sfCompactSupportFiniteFunctor at the retained geometric compactification.
The geometric automorphism has the same galoisMap as galois. The inherited field
structure maps coincide; the remaining geometric hypotheses are proof irrelevant.
Substitution gives both functor equalities. -/
theorem rationalExchange_endpoints (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) :
    (Arrow.mk (FrobeniusExchange.frobeniusRational D l hl E.carrier f₀
      (FrobeniusExchange.frobeniusCompactModel D f₀ c₀))).left =
      (Arrow.mk (S.ring.rationalLeft
        (FrobeniusExchange.geometricCompactification D f₀ c₀) E).hom).right ⋙
          sfWeilFrobeniusPullback D l hl Y₀ E.carrier ∧
    (Arrow.mk (FrobeniusExchange.frobeniusRational D l hl E.carrier f₀
      (FrobeniusExchange.frobeniusCompactModel D f₀ c₀))).right =
      sfWeilFrobeniusPullback D l hl X₀ E.carrier ⋙
        (Arrow.mk (S.ring.rationalLeft
          (FrobeniusExchange.geometricCompactification D f₀ c₀) E).hom).right := by
  constructor
  · dsimp only [FrobeniusExchange.frobeniusRational, Arrow.mk_left, Arrow.mk_right]
    unfold FrobeniusExchange.modelRationalSource
    rfl
  · dsimp only [FrobeniusExchange.frobeniusRational, Arrow.mk_left, Arrow.mk_right]
    unfold FrobeniusExchange.modelRationalTarget
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- At a finite field, conjugate the actual compactification exchange by the
recorded compact-support realization. This fixes the map rather than its endpoints.
Source: compact-support exchange convention and proof Step 4
(blueprint: lem-pur-constant-purity-frobenius-square). -/
def rationalBeta (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l)
    (K : sfRationalConstructibleCategory l
      E.carrier (D.geometricFiber X₀).left) :
    (sfWeilFrobeniusPullback D l hl Y₀ E.carrier).obj
        ((operation D l hl Ω X₀ Y₀ f₀ c₀ S (.rational E)).F.obj K) ⟶
      (operation D l hl Ω X₀ Y₀ f₀ c₀ S (.rational E)).F.obj
        ((sfWeilFrobeniusPullback D l hl X₀ E.carrier).obj K) :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  (rationalDerivedPullback l E.carrier
      (D.geometricFrobenius Y₀).hom).map
    ((S.ring.rationalLeft (FrobeniusExchange.geometricCompactification D f₀ c₀)
      E).hom.app K) ≫
    eqToHom (congrArg (fun H ↦ H.obj K)
      (rationalExchange_endpoints D l hl Ω X₀ Y₀ f₀ c₀ S E).1.symm) ≫
    (FrobeniusExchange.frobeniusRational D l hl
      E.carrier f₀
      (FrobeniusExchange.frobeniusCompactModel D f₀ c₀)).app K ≫
    eqToHom (congrArg (fun H ↦ H.obj K)
      (rationalExchange_endpoints D l hl Ω X₀ Y₀ f₀ c₀ S E).2) ≫
    (S.ring.rationalLeft (FrobeniusExchange.geometricCompactification D f₀ c₀)
      E).inv.app
        ((rationalDerivedPullback l E.carrier
          (D.geometricFrobenius X₀).hom).obj K)

private theorem transport_hom_of_heq {C : Type*} [Category C]
    {A B A' B' : C} (hA : A = A') (hB : B = B')
    (a : A ⟶ B) (b : A' ⟶ B') (h : HEq a b) :
    eqToHom hA.symm ≫ a ≫ eqToHom hB = b := by
  subst hA
  subst hB
  simpa using eq_of_heq h

private theorem rationalBeta_eq (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l)
    (K : sfRationalConstructibleCategory l E.carrier (D.geometricFiber X₀).left) :
    rationalBeta D l hl Ω X₀ Y₀ f₀ c₀ S E K =
      (RationalWeilPurity.betaComponent D l hl f₀ E.carrier Ω c₀ S K).hom := by
  let r := FrobeniusExchange.frobeniusRational D l hl E.carrier f₀
    (FrobeniusExchange.frobeniusCompactModel D f₀ c₀)
  let e := RationalWeilPurity.rationalExchange D l hl f₀ E.carrier c₀ K
  have hr := transport_hom_of_heq
    (congrArg (fun H ↦ H.obj K)
      (rationalExchange_endpoints D l hl Ω X₀ Y₀ f₀ c₀ S E).1)
    (congrArg (fun H ↦ H.obj K)
      (rationalExchange_endpoints D l hl Ω X₀ Y₀ f₀ c₀ S E).2)
    (r.app K) e.hom
    (frobeniusCompactRational_normalization D l hl f₀ E.carrier c₀ K)
  let FY := sfWeilFrobeniusPullback D l hl Y₀ E.carrier
  let q := S.ring.rationalLeft (FrobeniusExchange.geometricCompactification D f₀ c₀) E
  have h := congrArg (fun a ↦ FY.map (q.hom.app K) ≫ a ≫
    q.inv.app ((sfWeilFrobeniusPullback D l hl X₀ E.carrier).obj K)) hr
  simpa only [FY, q, r, e, rationalBeta, RationalWeilPurity.betaComponent,
    sfWeilFrobeniusPullback, operation, FrobeniusExchange.geometricCompactification,
    zlGeometricCompactification, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Category.assoc] using h

section StageComparison
attribute [local instance 2000] IntermediateField.algebra'
attribute [local irreducible] rationalBeta
  rationalDerivedPullback commonStageDerivedPullback
attribute [local irreducible] ScalarLocalization.category scalarReductionSourceDerived
  SheafOfModules.instCategory SheafOfModules.instAbelian
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Its common-stage component is explicitly conjugated by the prescribed
stage pullback and exceptional-coefficient comparisons.
Source: common-stage exchange convention and proof Step 4
(blueprint: lem-pur-constant-purity-frobenius-square). -/
def betaAtStage (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (D.geometricFiber X₀).left) :
    (targetFrobenius D l hl Ω Y₀).obj
        ((operation D l hl Ω X₀ Y₀ f₀ c₀ S .closed).F.obj
          ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K)) ⟶
      (operation D l hl Ω X₀ Y₀ f₀ c₀ S .closed).F.obj
        ((sourceFrobenius D l hl Ω X₀).obj
          ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K)) :=
by
  let E : ConstructibleExceptionalCoefficients.FieldStage.{u} l :=
    ConstructibleExceptionalCoefficients.commonField l Ω L
  let FX := sourceFrobenius D l hl Ω X₀
  let FY := targetFrobenius D l hl Ω Y₀
  let IY := GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω)
    (Y := (D.geometricFiber Y₀).left) L
  let IX := GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω)
    (Y := (D.geometricFiber X₀).left) L
  let R := (operation D l hl Ω X₀ Y₀ f₀ c₀ S (.rational E)).F
  let F := (operation D l hl Ω X₀ Y₀ f₀ c₀ S .closed).F
  let q := (@ConstructibleExceptionalCoefficients.CommonSystem.commonComparison
    l inferInstance Ω inferInstance inferInstance inferInstance D hl
    (D.geometricFiber X₀).left (D.geometricFiber Y₀).left
    (FrobeniusExchange.fiberMap D f₀) inferInstance inferInstance
    xft xqc yft yqc fover fsep fft fqc
    (@ConstructibleExceptionalCoefficients.System.ring
      l inferInstance Ω inferInstance inferInstance inferInstance D hl
      (D.geometricFiber X₀).left (D.geometricFiber Y₀).left
      (FrobeniusExchange.fiberMap D f₀) inferInstance inferInstance
      xft xqc yft yqc fover fsep fft fqc S)
    (@ConstructibleExceptionalCoefficients.System.fields
      l inferInstance Ω inferInstance inferInstance inferInstance D hl
      (D.geometricFiber X₀).left (D.geometricFiber Y₀).left
      (FrobeniusExchange.fiberMap D f₀) inferInstance inferInstance
      xft xqc yft yqc fover fsep fft fqc S)
    (@ConstructibleExceptionalCoefficients.System.common
      l inferInstance Ω inferInstance inferInstance inferInstance D hl
      (D.geometricFiber X₀).left (D.geometricFiber Y₀).left
      (FrobeniusExchange.fiberMap D f₀) inferInstance inferInstance
      xft xqc yft yqc fover fsep fft fqc S)
    (FrobeniusExchange.geometricCompactification D f₀ c₀) L).q
  let a : FY.obj (F.obj (IX.obj K)) ⟶ FY.obj (IY.obj (R.obj K)) :=
    FY.map (q.inv.app K)
  let b : FY.obj (IY.obj (R.obj K)) ⟶
      IY.obj ((sfWeilFrobeniusPullback D l hl Y₀ E.carrier).obj (R.obj K)) :=
    (sfWeilStagePullbackIdentification D l hl Y₀ Ω L (R.obj K)).hom
  have hcat : ConstructibleExceptionalCoefficients.category l Ω
      (D.geometricFiber Y₀).left (.rational E) =
      GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω
        (D.geometricFiber Y₀).left L := by
    unfold ConstructibleExceptionalCoefficients.category
      GeneralAlgebraicallyClosedCoefficients.stageCategory
    unfold ScalarLocalization.category
    with_unfolding_all rfl
  let r := rationalBeta D l hl Ω X₀ Y₀ f₀ c₀ S E K
  let A := (sfWeilFrobeniusPullback D l hl Y₀ E.carrier).obj (R.obj K)
  let B := R.obj ((sfWeilFrobeniusPullback D l hl X₀ E.carrier).obj K)
  let r' := Eq.mp (congrArg (fun cat : Category.{u + 2}
      (sfRationalConstructibleCategory l E.carrier (D.geometricFiber Y₀).left) ↦
      @Quiver.Hom _ cat.toQuiver A B) hcat) r
  let c : IY.obj ((sfWeilFrobeniusPullback D l hl Y₀ E.carrier).obj (R.obj K)) ⟶
      IY.obj (R.obj ((sfWeilFrobeniusPullback D l hl X₀ E.carrier).obj K)) :=
    IY.map r'
  let d : IY.obj (R.obj ((sfWeilFrobeniusPullback D l hl X₀ E.carrier).obj K)) ⟶
      F.obj (IX.obj ((sfWeilFrobeniusPullback D l hl X₀ E.carrier).obj K)) :=
    q.hom.app ((sfWeilFrobeniusPullback D l hl X₀ E.carrier).obj K)
  let e : F.obj (IX.obj ((sfWeilFrobeniusPullback D l hl X₀ E.carrier).obj K)) ⟶
      F.obj (FX.obj (IX.obj K)) :=
    F.map (sfWeilStagePullbackIdentification D l hl X₀ Ω L K).inv
  exact a ≫ b ≫ c ≫ d ≫ e

end StageComparison

section ExchangeProof
attribute [local instance 2000] IntermediateField.algebra'
attribute [local irreducible] rationalBeta
  rationalDerivedPullback commonStageDerivedPullback
attribute [local irreducible] ScalarLocalization.category scalarReductionSourceDerived
  SheafOfModules.instCategory SheafOfModules.instAbelian
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted

private theorem commonBeta_normalization
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (D.geometricFiber X₀).left) :
    (CommonWeilPurity.beta D l hl f₀ Ω c₀ S).hom.app
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K) =
      betaAtStage D l hl Ω X₀ Y₀ f₀ c₀ S L K := by
  change (CommonWeilPurity.betaComponent D l hl f₀ Ω c₀ S
    ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K)).hom = _
  dsimp only [CommonWeilPurity.betaComponent, betaAtStage, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  simp only [rationalBeta_eq]
  dsimp only [RationalWeilPurity.beta, NatIso.ofComponents_hom_app, Iso.app_hom,
    FrobeniusExchange.geometricCompactification, zlGeometricCompactification,
    sourceFrobenius, targetFrobenius, operation]
  rfl

/-- Canonical exchange exists uniquely with these actual finite-stage components.
Source: canonical exchange convention; proof Steps 4--5
(blueprint: lem-pur-constant-purity-frobenius-square).
Proof: each rational component is the localized proper/open exchange conjugated by
rationalLeft. Coefficient naturality and the common cocycle identify their classes
under every enlargement. They therefore descend to the indicated transformation.
Inverse geometric Frobenius squares give inverse proper and open mates; their
composite supplies the inverse at every rational stage. Hence the transformation
is invertible. Every common-stage object is represented at its own finite stage,
so the displayed component normalization determines the isomorphism uniquely. -/
theorem beta_existsUnique :
    ∃! β : (operation D l hl Ω X₀ Y₀ f₀ c₀ S .closed).F ⋙
          targetFrobenius D l hl Ω Y₀ ≅
        sourceFrobenius D l hl Ω X₀ ⋙
          (operation D l hl Ω X₀ Y₀ f₀ c₀ S .closed).F,
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (K : sfRationalConstructibleCategory l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
          (D.geometricFiber X₀).left),
        β.hom.app ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K) =
          betaAtStage D l hl Ω X₀ Y₀ f₀ c₀ S L K := by
  let B := CommonWeilPurity.beta D l hl f₀ Ω c₀ S
  have hB := commonBeta_normalization D l hl Ω X₀ Y₀ f₀ c₀ S
  refine ⟨B, hB, ?_⟩
  intro B' hB'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact (hB' K.stage K.obj).trans (hB K.stage K.obj).symm

end ExchangeProof

/-- The actual exchange, selected only after all its components are uniquely fixed.
Source: compact-support exchange convention
(blueprint: lem-pur-constant-purity-frobenius-square). -/
def beta := (beta_existsUnique D l hl Ω X₀ Y₀ f₀ c₀ S).exists.choose

section ExchangeEquality
attribute [local instance 2000] IntermediateField.algebra'
attribute [local irreducible] rationalBeta rationalDerivedPullback
  commonStageDerivedPullback
attribute [local irreducible] ScalarLocalization.category scalarReductionSourceDerived
  SheafOfModules.instCategory SheafOfModules.instAbelian
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem beta_eq_common :
    beta D l hl Ω X₀ Y₀ f₀ c₀ S = CommonWeilPurity.beta D l hl f₀ Ω c₀ S := by
  apply Iso.ext
  apply NatTrans.ext
  funext V
  have hs := (beta_existsUnique D l hl Ω X₀ Y₀ f₀ c₀ S).exists.choose_spec V.stage V.obj
  change (beta D l hl Ω X₀ Y₀ f₀ c₀ S).hom.app V = _ at hs
  exact hs.trans (commonBeta_normalization D l hl Ω X₀ Y₀ f₀ c₀ S V.stage V.obj).symm

end ExchangeEquality

/-- The inverse exchange's right adjunction mate; no purity map defines this arrow.
Source: statement and proof Step 5; Mathlib mateEquiv
(blueprint: lem-pur-constant-purity-frobenius-square). -/
def exceptionalMate :=
  (mateEquiv (operation D l hl Ω X₀ Y₀ f₀ c₀ S .closed).adjunction
    (operation D l hl Ω X₀ Y₀ f₀ c₀ S .closed).adjunction
    (TwoSquare.mk _ _ _ _ (beta D l hl Ω X₀ Y₀ f₀ c₀ S).inv)).natTrans

/-- The actual mate is invertible because both horizontal operations are pullback
by geometric automorphisms.
Source: statement's e and its inverse-square interpretation
(blueprint: lem-pur-constant-purity-frobenius-square).
Proof: use inverse geometric Frobenius on source and target. Its compact-support
exchange is inverse to beta after the canonical pullback-composition and identity
constraints. Form the same right mates. Pasting mates commutes with horizontal
composition by the adjunction triangle identities, so their two composites are
identities after the same constraints. This supplies the inverse mate. -/
theorem exceptionalMate_isIso :
    IsIso (exceptionalMate D l hl Ω X₀ Y₀ f₀ c₀ S) := by
  have h := semilinearFieldOperationLifts D l hl X₀ Y₀ f₀
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
      (Padic.finiteCoefficientBase l Ω)) Ω
  let : (sourceFrobenius D l hl Ω X₀).IsEquivalence := h.2.2.1.2.1
  let : (targetFrobenius D l hl Ω Y₀).IsEquivalence := h.2.2.2.2.1
  exact isIso_mateEquiv_of_isEquivalence_of_fullyFaithful _ _
    (sourceFrobenius D l hl Ω X₀) (targetFrobenius D l hl Ω Y₀)
    (beta D l hl Ω X₀ Y₀ f₀ c₀ S).symm

/-- The exceptional Frobenius isomorphism with underlying arrow the inverse
compact-support exchange's right adjunction mate.
Source: statement's e
(blueprint: lem-pur-constant-purity-frobenius-square). -/
def exceptionalIso :=
  letI := exceptionalMate_isIso D l hl Ω X₀ Y₀ f₀ c₀ S
  asIso (exceptionalMate D l hl Ω X₀ Y₀ f₀ c₀ S)
end SquareData

section TwistedSource
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X₀ Y₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The published shifted Tate line with its inherited prime-invertibility data.
Source: canonical purity-source convention
(blueprint: lem-pur-constant-purity-frobenius-square). -/
def shiftedLine (d : ℕ) :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  RationalSmoothPurityCanonical.commonShiftedLine l Ω (D.geometricFiber X₀).left d

/-- Canonical Frobenius of the shifted line, represented at Q_l and using the
normalized pullback/shift comparison followed by the prescribed root-line map.
Source: Tate-and-shift comparison, proof Step 3
(blueprint: lem-pur-constant-purity-frobenius-square). -/
def shiftedLineTheta (d : ℕ) :
    (sourceFrobenius D l hl Ω X₀).obj
        (shiftedLine D l hl Ω X₀ d) ≅
      shiftedLine D l hl Ω X₀ d :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI : IsIso (D.geometricFrobenius X₀).hom := Iso.isIso_hom _
  sfWeilStagePullbackIdentification D l hl X₀ Ω (Padic.finiteCoefficientBase l Ω) _ ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion (Padic.finiteCoefficientBase l Ω)).mapIso
      (((rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
            (Padic.finiteCoefficientBase l Ω)) (D.geometricFrobenius X₀).hom).commShiftIso
          (2 * (d : ℤ))).app _ ≪≫
        (shiftFunctor _ (2 * (d : ℤ))).mapIso
          (FrobeniusCoefficientTwists.rationalDerivedLineMap l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
              (Padic.finiteCoefficientBase l Ω)) (D.geometricFrobenius X₀).hom (d : ℤ)))

/-- H is the recorded purity-source functor, with the even shift on the line.
Its fixed tensor symmetry and shift constraints give La*(-)(d)[2d].
Source: statement's H and the canonical purity-source conventions
(blueprint: lem-pur-constant-purity-frobenius-square). -/
abbrev source (f₀ : X₀ ⟶ Y₀) (d : ℕ) :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  RationalSmoothPurityCanonical.commonSource l Ω (FrobeniusExchange.fiberMap D f₀) d

/-- b_K is explicitly the canonical tensor comparison, the Tate-and-shift line
map, and the pullback compositor for the actual semilinear Frobenius square.
Source: definition of b in the statement and proof Step 3
(blueprint: lem-pur-constant-purity-frobenius-square). -/
def sourceSquare (f₀ : X₀ ⟶ Y₀) (d : ℕ)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left) :
    (sourceFrobenius D l hl Ω X₀).obj ((source D l hl Ω X₀ Y₀ f₀ d).obj K) ≅
      (source D l hl Ω X₀ Y₀ f₀ d).obj ((targetFrobenius D l hl Ω Y₀).obj K) :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  canonicalCommonStagePullbackTensor l Ω (D.geometricFrobenius X₀).hom
      (shiftedLine D l hl Ω X₀ d)
      ((commonStageDerivedPullback l Ω (FrobeniusExchange.fiberMap D f₀)).obj K) ≪≫
    (commonStageDerivedTensor l Ω (D.geometricFiber X₀).left).mapIso
      (Iso.prod (shiftedLineTheta D l hl Ω X₀ d)
        (podCommonSquarePullbackComponent l Ω (FrobeniusExchange.fiberMap D f₀)
          (D.geometricFrobenius X₀).hom (D.geometricFrobenius Y₀).hom
          (zlFrobenius_naturality D f₀) K))

/-- The usual twisted unit identification is tensoring the unit comparison by
the shifted line. Its tensor symmetry is the fixed purity-source convention.
Source: twisted and shifted identification in the statement
(blueprint: lem-pur-constant-purity-frobenius-square). -/
def sourceUnit (f₀ : X₀ ⟶ Y₀) (d : ℕ) :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  (commonStageDerivedTensor l Ω (D.geometricFiber X₀).left).mapIso
    (Iso.prod
      (Iso.refl
        (shiftedLine D l hl Ω X₀ d))
      (commonUnit D l hl Ω (FrobeniusExchange.fiberMap D f₀)))

/-- The canonical Frobenius on the identified twisted constant object uses the
actual constant Weil datum and the prescribed shifted root-line datum.
Source: canonical Tate structure, proof Step 3
(blueprint: lem-pur-constant-purity-frobenius-square). -/
def canonicalSourceTheta (f₀ : X₀ ⟶ Y₀) (d : ℕ) :
    (sourceFrobenius D l hl Ω X₀).obj
        ((source D l hl Ω X₀ Y₀ f₀ d).obj (unit D l hl Ω (D.geometricFiber Y₀).left)) ≅
      (source D l hl Ω X₀ Y₀ f₀ d).obj (unit D l hl Ω (D.geometricFiber Y₀).left) :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  (sourceFrobenius D l hl Ω X₀).mapIso (sourceUnit D l hl Ω X₀ Y₀ f₀ d) ≪≫
    canonicalCommonStagePullbackTensor l Ω (D.geometricFrobenius X₀).hom
      (shiftedLine D l hl Ω X₀ d)
      (unit D l hl Ω (D.geometricFiber X₀).left) ≪≫
    (commonStageDerivedTensor l Ω (D.geometricFiber X₀).left).mapIso
      (Iso.prod (shiftedLineTheta D l hl Ω X₀ d)
        (constantWeilAlgebraicallyClosedComplex l D hl X₀ Ω).str) ≪≫
    (sourceUnit D l hl Ω X₀ Y₀ f₀ d).symm
end TwistedSource

/-- The arithmetic point, retained as a model for its canonical geometric Spec k.
Source: statement, s = Spec k
(blueprint: lem-pur-constant-purity-frobenius-square). -/
abbrev point (D : FiniteFieldDatum.{u}) : Over (Spec (.of D.k₀)) := Over.mk (𝟙 _)

/-- The actual structure morphism as a map of arithmetic models.
Source: statement, a₀ : X₀ → Spec k₀
(blueprint: lem-pur-constant-purity-frobenius-square). -/
abbrev pointMap (D : FiniteFieldDatum.{u}) (X₀ : Over (Spec (.of D.k₀))) :
    X₀ ⟶ point D := Over.homMk X₀.hom

section StructureData
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Presentation data for the prescribed exceptional operations on the geometric
structure map. All geometric proof instances are inherited by base change.
Source: statement's fixed coefficient operations, def-pur-conventions
(blueprint: lem-pur-constant-purity-frobenius-square). -/
def systems :=
  letI : LocallyOfFiniteType (point D).hom :=
    locallyOfFiniteType_of_isOpenImmersion (𝟙 (Spec (.of D.k₀)))
  letI : QuasiCompact (point D).hom :=
    inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k₀))))
  letI : IsSeparated (pointMap D X₀).left := inferInstanceAs (IsSeparated X₀.hom)
  letI : LocallyOfFiniteType (pointMap D X₀).left :=
    inferInstanceAs (LocallyOfFiniteType X₀.hom)
  letI : QuasiCompact (pointMap D X₀).left := inferInstanceAs (QuasiCompact X₀.hom)
  @ConstructibleExceptionalCoefficients.System l inferInstance Ω
    inferInstance inferInstance inferInstance D hl
    (D.geometricFiber X₀).left (D.geometricFiber (point D)).left
    (FrobeniusExchange.fiberMap D (pointMap D X₀)) inferInstance inferInstance
    (FrobeniusExchange.fiber_finiteType D X₀).1
    (FrobeniusExchange.fiber_finiteType D X₀).2
    (FrobeniusExchange.fiber_finiteType D (point D)).1
    (FrobeniusExchange.fiber_finiteType D (point D)).2
    (zlFiberMap_isOver D (pointMap D X₀))
    (FrobeniusExchange.fiberMap_properties D (pointMap D X₀)).1
    (FrobeniusExchange.fiberMap_properties D (pointMap D X₀)).2.1
    (FrobeniusExchange.fiberMap_properties D (pointMap D X₀)).2.2
end StructureData

private theorem equivariance_of_mate {C : Type*} {D : Type*}
    [Category* C] [Category* D]
    (Q : C ⥤ C) (P : D ⥤ D) (H : D ⥤ C)
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    (γ : ∀ K : D, H.obj K ≅ G.obj K)
    (b : ∀ K : D, Q.obj (H.obj K) ≅ H.obj (P.obj K))
    (β : F ⋙ P ≅ Q ⋙ F)
    (hn : ∀ {K L : D} (a : K ⟶ L),
      (γ K).hom ≫ G.map a = H.map a ≫ (γ L).hom)
    (hc : ∀ K : D,
      F.map ((Q.mapIso (γ K)).inv ≫ (b K).hom ≫ (γ (P.obj K)).hom) ≫
        adj.counit.app (P.obj K) = β.inv.app (G.obj K) ≫ P.map (adj.counit.app K))
    (K : D) (θ : P.obj K ≅ K) :
    Q.map (γ K).hom ≫
        (mateEquiv adj adj (TwoSquare.mk _ _ _ _ β.inv)).natTrans.app K ≫
        G.map θ.hom =
      (b K).hom ≫ H.map θ.hom ≫ (γ K).hom := by
  have hm : (Q.mapIso (γ K)).inv ≫ (b K).hom ≫ (γ (P.obj K)).hom =
      (mateEquiv adj adj (TwoSquare.mk _ _ _ _ β.inv)).natTrans.app K := by
    apply (adj.homEquiv _ _).symm.injective
    simpa only [Adjunction.homEquiv_counit] using
      (hc K).trans (mateEquiv_counit adj adj (TwoSquare.mk _ _ _ _ β.inv) K).symm
  rw [← hm]
  simp only [Functor.mapIso_inv, Category.assoc]
  rw [← Category.assoc (Q.map (γ K).hom), ← Q.map_comp,
    Iso.hom_inv_id, Q.map_id, Category.id_comp, hn]

private theorem tensor_unit_square {C : Type*} [Category* C]
    (Q : C ⥤ C) (V : C × C ⥤ C)
    (μ : V ⋙ Q ≅ Q.prod Q ⋙ V)
    {T N U N' : C} (u : N ≅ U) (τ : Q.obj T ≅ T) (θ : Q.obj U ≅ U)
    (t : Q.obj N ≅ N') (a : N' ⟶ N)
    (h : t.hom ≫ a ≫ u.hom = Q.map u.hom ≫ θ.hom) :
    Q.map (V.map (Prod.mkHom (𝟙 T) u.hom)) ≫ μ.hom.app (T,U) ≫
        V.map (Prod.mkHom τ.hom θ.hom) ≫ V.map (Prod.mkHom (𝟙 T) u.inv) =
      μ.hom.app (T,N) ≫ V.map (Prod.mkHom τ.hom t.hom) ≫
        V.map (Prod.mkHom (𝟙 T) a) := by
  have hu := congrArg (fun z ↦ z ≫ u.inv) h
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hu
  have hn := μ.hom.naturality (Prod.mkHom (𝟙 T) u.hom)
  change Q.map (V.map (Prod.mkHom (𝟙 T) u.hom)) ≫ μ.hom.app (T,U) =
    μ.hom.app (T,N) ≫ V.map (Prod.mkHom (Q.map (𝟙 T)) (Q.map u.hom)) at hn
  rw [← Category.assoc (Q.map _), hn]
  simp only [Category.assoc, ← V.map_comp]
  congr 2
  ext
  · simp
  · change Q.map u.hom ≫ θ.hom ≫ u.inv = t.hom ≫ a
    exact hu.symm

section Conclusion
variable (P : PurityFiniteSetting.{u})
  (X₀ : Over (Spec (.of P.field.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  (c₀ : Compactification X₀.hom)
  (S : systems P.field P.coefficients.l P.coefficients.different P.coefficients.Qbar X₀)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The three morphism identities, with their actual constant, Tate, compact-support
exchange, adjunction mate and trace-normalized purity maps. The geometric point is
the canonical pullback presentation of Spec k; no extra arithmetic model is chosen.
Source: all three clauses of the statement
(blueprint: lem-pur-constant-purity-frobenius-square). -/
def Square (d : ℕ) [SmoothOfRelativeDimension d X₀.hom] : Prop :=
  let D := P.field
  let l := P.coefficients.l
  let hl := P.coefficients.different
  let Ω := P.coefficients.Qbar
  let Y₀ := point D
  let f₀ := pointMap D X₀
  letI : LocallyOfFiniteType Y₀.hom :=
    locallyOfFiniteType_of_isOpenImmersion (𝟙 (Spec (.of D.k₀)))
  letI : QuasiCompact Y₀.hom :=
    inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k₀))))
  letI : IsSeparated Y₀.hom :=
    inferInstanceAs (IsSeparated (𝟙 (Spec (.of D.k₀))))
  letI : IsSeparated f₀.left := inferInstanceAs (IsSeparated X₀.hom)
  letI : LocallyOfFiniteType f₀.left := inferInstanceAs (LocallyOfFiniteType X₀.hom)
  letI : QuasiCompact f₀.left := inferInstanceAs (QuasiCompact X₀.hom)
  letI : SmoothOfRelativeDimension d f₀.left :=
    inferInstanceAs (SmoothOfRelativeDimension d X₀.hom)
  letI : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D X₀).1
  letI : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D X₀).2
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D Y₀).2
  letI : IsSeparated ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    MorphismProperty.baseChange_obj (P := @IsSeparated) _ X₀ inferInstance
  letI : IsSeparated ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    MorphismProperty.baseChange_obj (P := @IsSeparated) _ Y₀ inferInstance
  letI : (FrobeniusExchange.fiberMap D f₀).IsOver (Spec (.of D.k)) :=
    zlFiberMap_isOver D f₀
  letI : IsSeparated (FrobeniusExchange.fiberMap D f₀) :=
    (FrobeniusExchange.fiberMap_properties D f₀).1
  letI : LocallyOfFiniteType (FrobeniusExchange.fiberMap D f₀) :=
    (FrobeniusExchange.fiberMap_properties D f₀).2.1
  letI : QuasiCompact (FrobeniusExchange.fiberMap D f₀) :=
    (FrobeniusExchange.fiberMap_properties D f₀).2.2
  letI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension d) :=
    smoothOfRelativeDimension_isStableUnderBaseChange d
  letI : SmoothOfRelativeDimension d (FrobeniusExchange.fiberMap D f₀) :=
    MorphismProperty.overPullbackMap (P := @SmoothOfRelativeDimension d)
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) f₀ inferInstance
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  let Q := sourceFrobenius D l hl Ω X₀
  let H := source D l hl Ω X₀ Y₀ f₀ d
  let G := (operation D l hl Ω X₀ Y₀ f₀ c₀ S .closed).G
  let K := unit D l hl Ω (D.geometricFiber Y₀).left
  let θ₀ := (constantWeilAlgebraicallyClosedComplex l D hl Y₀ Ω).str
  let θX := (constantWeilAlgebraicallyClosedComplex l D hl X₀ Ω).str
  let u := commonUnit D l hl Ω (FrobeniusExchange.fiberMap D f₀)
  let b := sourceSquare D l hl Ω X₀ Y₀ f₀ d K
  let θH := canonicalSourceTheta D l hl Ω X₀ Y₀ f₀ d
  let γ := @RationalSmoothPurityCanonical.commonIso P
    (D.geometricFiber X₀).left (D.geometricFiber Y₀).left inferInstance inferInstance
    (FrobeniusExchange.fiber_finiteType D X₀).1
    (FrobeniusExchange.fiber_finiteType D X₀).2
    (MorphismProperty.baseChange_obj (P := @IsSeparated) _ X₀ inferInstance)
    (FrobeniusExchange.fiber_finiteType D Y₀).1
    (FrobeniusExchange.fiber_finiteType D Y₀).2
    (MorphismProperty.baseChange_obj (P := @IsSeparated) _ Y₀ inferInstance)
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)
    (fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y)
    (FrobeniusExchange.fiberMap D f₀) (zlFiberMap_isOver D f₀)
    (FrobeniusExchange.fiberMap_properties D f₀).1
    (FrobeniusExchange.fiberMap_properties D f₀).2.1
    (FrobeniusExchange.fiberMap_properties D f₀).2.2
    (FrobeniusExchange.geometricCompactification D f₀ c₀) S d inferInstance K
  let e := exceptionalIso D l hl Ω X₀ Y₀ f₀ c₀ S
  (podCommonSquarePullbackComponent l Ω (FrobeniusExchange.fiberMap D f₀)
      (D.geometricFrobenius X₀).hom (D.geometricFrobenius Y₀).hom
      (zlFrobenius_naturality D f₀) K).hom ≫
      (commonStageDerivedPullback l Ω (FrobeniusExchange.fiberMap D f₀)).map θ₀.hom ≫
      u.hom =
    Q.map u.hom ≫ θX.hom ∧
    θH.hom = b.hom ≫ H.map θ₀.hom ∧
    Q.map γ.hom ≫ e.hom.app K ≫ G.map θ₀.hom = θH.hom ≫ γ.hom

private theorem geometricFiber_separated (D : FiniteFieldDatum.{u})
    (T : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom] :
    IsSeparated ((D.geometricFiber T).left ↘ Spec (.of D.k)) := by
  change IsSeparated (pullback.snd T.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
  exact (IsSeparated.isStableUnderBaseChange).of_isPullback
    (IsPullback.of_hasPullback T.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) inferInstance

section ConclusionProof
attribute [local instance 2000] IntermediateField.algebra'
attribute [local irreducible] rationalBeta rationalDerivedPullback
  commonStageDerivedPullback commonStageDerivedTensor
attribute [local irreducible] ScalarLocalization.category scalarReductionSourceDerived
  SheafOfModules.instCategory SheafOfModules.instAbelian
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The canonical constant Tate structure is carried by rational smooth purity
to the exceptional Frobenius structure defined by the compact-support adjunction mate.
The purity map is the published commonIso, constructed by rationalizing the normalized
integral trace transpose, hence the inverse geometric dualizing identification.
Source: smooth dualizing corollary proof, first sentence; purity/trace equivariance
proof Steps 1--2
(blueprint: lem-pur-constant-purity-frobenius-square).
Proof: base change preserves separated finite type and smooth dimension d.
The completed coefficient unit is finite Tor, with normalized constant reductions;
thus its canonical Frobenius provides the strict input to the purity theorem.
At every finite quotient the two pullback unit composites send each constant section
to itself and commute with reduction. Whole-system derived limits, rationalization
and common-stage inclusion give the first equality. Expand b using its tensor,
Tate-line, shift and pullback-composition comparisons. Naturality and the tensor-unit
normalization give the second equality without an extra scalar. Apply strict-data
purity and exceptional-counit equivariance at this unit. Naturality of the counit for
θ₀, followed by cancellation of θ₀ and inverse compact-support exchange, identifies
the purity-defined exceptional exchange with the right mate e by the adjunction
hom-equivalence. Substitute that identity and the second equality into the purity
square. The trace-transpose normalization of commonIso is exactly the purity whose
inverse gives the dualizing corollary. Only the canonical unit lattice is used.
The Lean reduction uses the existing common-stage naturality/counit theorem for
this last step and the separate comparison of the two pullback-square normalizations. -/
theorem constant_purity_frobenius_square (d : ℕ) [SmoothOfRelativeDimension d X₀.hom] :
    Square P X₀ c₀ S d := by
  let D := P.field
  let l := P.coefficients.l
  let hl := P.coefficients.different
  let Ω := P.coefficients.Qbar
  let Y₀ := point D
  let f₀ := pointMap D X₀
  let pointFt : LocallyOfFiniteType Y₀.hom :=
    locallyOfFiniteType_of_isOpenImmersion (𝟙 (Spec (.of D.k₀)))
  let pointQc : QuasiCompact Y₀.hom :=
    inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k₀))))
  let pointSep : IsSeparated Y₀.hom :=
    inferInstanceAs (IsSeparated (𝟙 (Spec (.of D.k₀))))
  let mapSep : IsSeparated f₀.left := inferInstanceAs (IsSeparated X₀.hom)
  let mapFt : LocallyOfFiniteType f₀.left := inferInstanceAs (LocallyOfFiniteType X₀.hom)
  let mapQc : QuasiCompact f₀.left := inferInstanceAs (QuasiCompact X₀.hom)
  let mapSmooth : SmoothOfRelativeDimension d f₀.left :=
    inferInstanceAs (SmoothOfRelativeDimension d X₀.hom)
  let geomFtX : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D X₀).1
  let geomQcX : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D X₀).2
  let geomFtY : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D Y₀).1
  let geomQcY : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D Y₀).2
  let geomSepX : IsSeparated ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    geometricFiber_separated D X₀
  let geomSepY : IsSeparated ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    geometricFiber_separated D Y₀
  let geomOver : (FrobeniusExchange.fiberMap D f₀).IsOver (Spec (.of D.k)) :=
    zlFiberMap_isOver D f₀
  let geomMapSep : IsSeparated (FrobeniusExchange.fiberMap D f₀) :=
    (FrobeniusExchange.fiberMap_properties D f₀).1
  let geomMapFt : LocallyOfFiniteType (FrobeniusExchange.fiberMap D f₀) :=
    (FrobeniusExchange.fiberMap_properties D f₀).2.1
  let geomMapQc : QuasiCompact (FrobeniusExchange.fiberMap D f₀) :=
    (FrobeniusExchange.fiberMap_properties D f₀).2.2
  let smoothStable : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension d) :=
    smoothOfRelativeDimension_isStableUnderBaseChange d
  let geomSmooth : SmoothOfRelativeDimension d (FrobeniusExchange.fiberMap D f₀) :=
    MorphismProperty.overPullbackMap (P := @SmoothOfRelativeDimension d)
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) f₀ inferInstance
  let invX : ∀ x : ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj X₀).left,
      Invertible (l : ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj X₀).left.residueField x) :=
    fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  let invY : ∀ y : ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj Y₀).left,
      Invertible (l : ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj Y₀).left.residueField y) :=
    fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  let invXFiber : ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
    fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  let invYFiber : ∀ y : (D.geometricFiber Y₀).left,
      Invertible (l : (D.geometricFiber Y₀).left.residueField y) :=
    fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  let Q := sourceFrobenius D l hl Ω X₀
  let H := source D l hl Ω X₀ Y₀ f₀ d
  let G := (operation D l hl Ω X₀ Y₀ f₀ c₀ S (fover := zlFiberMap_isOver D f₀) .closed).G
  let K := unit D l hl Ω (D.geometricFiber Y₀).left
  let θ₀ := (constantWeilAlgebraicallyClosedComplex l D hl Y₀ Ω).str
  let θX := (constantWeilAlgebraicallyClosedComplex l D hl X₀ Ω).str
  let u := commonUnit D l hl Ω (FrobeniusExchange.fiberMap D f₀)
  let b := sourceSquare D l hl Ω X₀ Y₀ f₀ d K
  let θH := canonicalSourceTheta D l hl Ω X₀ Y₀ f₀ d
  let γ := @RationalSmoothPurityCanonical.commonIso P
    (D.geometricFiber X₀).left (D.geometricFiber Y₀).left inferInstance inferInstance
    (FrobeniusExchange.fiber_finiteType D X₀).1
    (FrobeniusExchange.fiber_finiteType D X₀).2
    (geometricFiber_separated D X₀)
    (FrobeniusExchange.fiber_finiteType D Y₀).1
    (FrobeniusExchange.fiber_finiteType D Y₀).2
    (geometricFiber_separated D Y₀)
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)
    (fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y)
    (FrobeniusExchange.fiberMap D f₀) (zlFiberMap_isOver D f₀)
    (FrobeniusExchange.fiberMap_properties D f₀).1
    (FrobeniusExchange.fiberMap_properties D f₀).2.1
    (FrobeniusExchange.fiberMap_properties D f₀).2.2
    (FrobeniusExchange.geometricCompactification D f₀ c₀) S d geomSmooth K
  let e := exceptionalIso D l hl Ω X₀ Y₀ f₀ c₀ S (fover := zlFiberMap_isOver D f₀)
  change
    (podCommonSquarePullbackComponent l Ω (FrobeniusExchange.fiberMap D f₀)
        (D.geometricFrobenius X₀).hom (D.geometricFrobenius Y₀).hom
        (zlFrobenius_naturality D f₀) K).hom ≫
        (commonStageDerivedPullback l Ω (FrobeniusExchange.fiberMap D f₀)).map θ₀.hom ≫
        u.hom =
      Q.map u.hom ≫ θX.hom ∧
      θH.hom = b.hom ≫ H.map θ₀.hom ∧
      Q.map γ.hom ≫ e.hom.app K ≫ G.map θ₀.hom = θH.hom ≫ γ.hom
  have hu := commonUnit_frobenius D l hl Ω X₀ Y₀ f₀
  have hθ : θH.hom = b.hom ≫ H.map θ₀.hom := by
    obtain ⟨μ, hμ⟩ := (derivedPullbackTensorIso l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
        (Padic.finiteCoefficientBase l Ω))
      (D.geometricFrobenius X₀).hom 0 Ω).2.2.2.2.2.2.2.1
    let V := commonStageDerivedTensor l Ω (D.geometricFiber X₀).left
    let T := shiftedLine D l hl Ω X₀ d
    let N := (commonStageDerivedPullback l Ω (FrobeniusExchange.fiberMap D f₀)).obj K
    let U := unit D l hl Ω (D.geometricFiber X₀).left
    let τ := shiftedLineTheta D l hl Ω X₀ d
    let t := podCommonSquarePullbackComponent l Ω (FrobeniusExchange.fiberMap D f₀)
      (D.geometricFrobenius X₀).hom (D.geometricFrobenius Y₀).hom
      (zlFrobenius_naturality D f₀) K
    let a := (commonStageDerivedPullback l Ω (FrobeniusExchange.fiberMap D f₀)).map θ₀.hom
    let A := canonicalCommonStagePullbackTensor l Ω (D.geometricFrobenius X₀).hom T U
    let B := canonicalCommonStagePullbackTensor l Ω (D.geometricFrobenius X₀).hom T N
    let m := Q.map (V.map (Prod.mkHom (𝟙 T) u.hom))
    let z := V.map (Prod.mkHom τ.hom θX.hom)
    let w := V.map (Prod.mkHom (𝟙 T) u.inv)
    let c := V.map (Prod.mkHom τ.hom t.hom)
    let v := V.map (Prod.mkHom (𝟙 T) a)
    have hA : μ.hom.app (T, U) = A.hom := congrArg Iso.hom (hμ T U)
    have hB : μ.hom.app (T, N) = B.hom := congrArg Iso.hom (hμ T N)
    have ht : m ≫ μ.hom.app (T, U) ≫ z ≫ w = μ.hom.app (T, N) ≫ c ≫ v :=
      tensor_unit_square Q V μ u τ θX t a hu
    have h0 : θH.hom = m ≫ A.hom ≫ z ≫ w := by rfl
    have h1 := congrArg (fun q ↦ m ≫ q ≫ z ≫ w) hA.symm
    have h2 := congrArg (fun q ↦ q ≫ c ≫ v) hB
    have h3 : B.hom ≫ c ≫ v = b.hom ≫ H.map θ₀.hom :=
      (Category.assoc _ _ _).symm
    exact h0.trans (h1.trans (ht.trans (h2.trans h3)))
  refine ⟨hu, hθ, ?_⟩
  have hp := (rational_weil_purity_naturality_mate P f₀ c₀ S d).2
  have hb (V) : CommonWeilPurity.b D l hl f₀ Ω d V =
      sourceSquare D l hl Ω X₀ Y₀ f₀ d V := by
    simp only [CommonWeilPurity.b, CommonWeilPurity.shiftedLineFrobenius,
      sourceSquare, shiftedLineTheta, shiftedLine, commonFrobeniusSquare_eq]
    try rfl
  have hβ := beta_eq_common D l hl Ω X₀ Y₀ f₀ c₀ S
    (fover := zlFiberMap_isOver D f₀)
  have he := equivariance_of_mate
    (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω)
    (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω)
    (CommonWeilPurity.H D l hl f₀ Ω d)
    (operation D l hl Ω X₀ Y₀ f₀ c₀ S (fover := zlFiberMap_isOver D f₀) .closed).F
    (operation D l hl Ω X₀ Y₀ f₀ c₀ S (fover := zlFiberMap_isOver D f₀) .closed).G
    (operation D l hl Ω X₀ Y₀ f₀ c₀ S (fover := zlFiberMap_isOver D f₀) .closed).adjunction
    (commonWeilPurityGamma P f₀ c₀ S d)
    (CommonWeilPurity.b D l hl f₀ Ω d)
    (CommonWeilPurity.beta D l hl f₀ Ω c₀ S) hp.1 hp.2 K θ₀
  have hleft := congrArg
    (fun B : (operation D l hl Ω X₀ Y₀ f₀ c₀ S
        (fover := zlFiberMap_isOver D f₀) .closed).F ⋙ targetFrobenius D l hl Ω Y₀ ≅
        Q ⋙ (operation D l hl Ω X₀ Y₀ f₀ c₀ S
          (fover := zlFiberMap_isOver D f₀) .closed).F ↦
      Q.map γ.hom ≫
        (mateEquiv
          (operation D l hl Ω X₀ Y₀ f₀ c₀ S
            (fover := zlFiberMap_isOver D f₀) .closed).adjunction
          (operation D l hl Ω X₀ Y₀ f₀ c₀ S
            (fover := zlFiberMap_isOver D f₀) .closed).adjunction
          (TwoSquare.mk _ _ _ _ B.inv)).natTrans.app K ≫ G.map θ₀.hom) hβ
  have hright := congrArg (fun q ↦ q ≫ H.map θ₀.hom ≫ γ.hom)
    (congrArg Iso.hom (hb K))
  have heMain : Q.map γ.hom ≫ e.hom.app K ≫ G.map θ₀.hom =
      b.hom ≫ H.map θ₀.hom ≫ γ.hom := hleft.trans (he.trans hright)
  have hassoc : b.hom ≫ H.map θ₀.hom ≫ γ.hom =
      (b.hom ≫ H.map θ₀.hom) ≫ γ.hom := (Category.assoc _ _ _).symm
  exact heMain.trans (hassoc.trans (congrArg (fun q ↦ q ≫ γ.hom) hθ.symm))

end ConclusionProof

end Conclusion

end WeilConjectures.ConstantPurityFrobenius
