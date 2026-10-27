/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.Paper.SixFunctorDatum
public import Sheaf.Paper.SitePerfectComplex
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

import Sheaf.Paper.SitePerfectCoefficientDual
import Sheaf.Paper.TateTwistLocallyFree
import Sheaf.Paper.TwistPreservesFiniteness
import Sheaf.Algebra.Homology.LineUnboundedDerivedTensor
import Sheaf.Paper.IntegralLineReductionRestriction
import Sheaf.Algebra.Homology.TotalTensorSignedCoherence
import Sheaf.SixFunctors.CompletedTensorShiftRight
import Sheaf.Paper.CompletedLineTensorCoherence
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Perfect coefficient dual pairs and shifted Tate inverses

Source: current Weil blueprint, sec-six-functors/sk-thm-sf-dual-perfect,
proof, last sentence (blueprint: lem-sf-perfect-dual-pair-and-tate-stability).
The auxiliary propositions expand the conclusion, including its actual maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a b a' b'
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The displayed inverse, with every associator and unitor inserted.
Source: blueprint dual-perfect proof, coefficient biduality
(blueprint: lem-sf-perfect-dual-pair-and-tate-stability). -/
def sfCoefficientBidualInverse {B : Type a} [Category.{b} B] {H : Bᵒᵖ × B ⥤ B}
    (M : CoefficientClosedStructure H) (s : @SymmetricCategory B _ M.monoidal)
    (P : B) (c : M.monoidal.tensorUnit ⟶
      M.tensor.obj (P, H.obj (op P, M.monoidal.tensorUnit))) :
    H.obj (op (H.obj (op P, M.monoidal.tensorUnit)), M.monoidal.tensorUnit) ⟶ P :=
  (M.monoidal.leftUnitor _).inv ≫ M.tensor.map (Prod.mkHom c (𝟙 _)) ≫
    (M.monoidal.associator _ _ _).hom ≫
    M.tensor.map (Prod.mkHom (𝟙 P)
      ((s.braiding _ _).hom ≫ M.evaluation _ M.monoidal.tensorUnit)) ≫
    (M.monoidal.rightUnitor P).hom

/-- Coefficient dual closure, the specified bidual arrow, and identification of every
exact dual pair by the transpose of its evaluation. The coevaluation in the inverse
is the given coevaluation transported by that very transpose.
Source: blueprint dual-perfect proof, Steps 1--4
(blueprint: lem-sf-perfect-dual-pair-and-tate-stability). -/
def SfPerfectDualPair {B : Type a} [Category.{b} B] {H : Bᵒᵖ × B ⥤ B}
    (M : CoefficientClosedStructure H) (s : @SymmetricCategory B _ M.monoidal) : Prop :=
  ∀ (P : B), @IsDualizable B _ M.monoidal P →
    @IsDualizable B _ M.monoidal (H.obj (op P, M.monoidal.tensorUnit)) ∧
    IsIso (CategoryTheory.ringedSiteBidual M s M.monoidal.tensorUnit P) ∧
    ∀ (Q : B) (d : @ExactPairing B _ M.monoidal P Q),
      ∃ e : Q ≅ H.obj (op P, M.monoidal.tensorUnit),
        e.hom = M.transpose Q P M.monoidal.tensorUnit d.evaluation' ∧
        M.tensor.map (Prod.mkHom e.hom (𝟙 P)) ≫
          M.evaluation P M.monoidal.tensorUnit = d.evaluation' ∧
        CategoryTheory.ringedSiteBidual M s M.monoidal.tensorUnit P ≫
          sfCoefficientBidualInverse M s P
            (d.coevaluation' ≫ M.tensor.map (Prod.mkHom (𝟙 P) e.hom)) = 𝟙 P ∧
        sfCoefficientBidualInverse M s P
            (d.coevaluation' ≫ M.tensor.map (Prod.mkHom (𝟙 P) e.hom)) ≫
          CategoryTheory.ringedSiteBidual M s M.monoidal.tensorUnit P = 𝟙 _

/-- Tensor by the two given lines is inverse by the actual contraction components;
both functors preserve perfect objects, including the coefficient dual of P.
Source: blueprint dual-perfect proof, Step 8
(blueprint: lem-sf-perfect-dual-pair-and-tate-stability). -/
def SfPerfectLinePair {B : Type a} [Category.{b} B] {H : Bᵒᵖ × B ⥤ B}
    (M : CoefficientClosedStructure H) (L N : B)
    (e : M.tensor.obj (L, N) ≅ M.monoidal.tensorUnit)
    (f : M.tensor.obj (N, L) ≅ M.monoidal.tensorUnit) : Prop :=
  (∃ alpha : @tensorRight B _ M.monoidal L ⋙ @tensorRight B _ M.monoidal N ≅ 𝟭 B,
    ∃ beta : @tensorRight B _ M.monoidal N ⋙ @tensorRight B _ M.monoidal L ≅ 𝟭 B,
      (∀ K : B, alpha.hom.app K = (M.monoidal.associator K L N).hom ≫
        M.tensor.map (Prod.mkHom (𝟙 K) e.hom) ≫ (M.monoidal.rightUnitor K).hom) ∧
      (∀ K : B, beta.hom.app K = (M.monoidal.associator K N L).hom ≫
        M.tensor.map (Prod.mkHom (𝟙 K) f.hom) ≫ (M.monoidal.rightUnitor K).hom)) ∧
  (∀ K : B, @IsDualizable B _ M.monoidal K →
    @IsDualizable B _ M.monoidal (M.tensor.obj (K, L)) ∧
    @IsDualizable B _ M.monoidal (M.tensor.obj (K, N))) ∧
  ∀ P : B, @IsDualizable B _ M.monoidal P →
    @IsDualizable B _ M.monoidal
      (M.tensor.obj (H.obj (op P, M.monoidal.tensorUnit), L))

/-- The unit comparison is normalized by the tensor comparison and the right unitor.
This removes the possible scalar ambiguity in transporting evaluations.
Source: blueprint dual-perfect proof, coefficient evaluation normalization
(blueprint: lem-sf-perfect-dual-pair-and-tate-stability). -/
def SfLineUnitComparison
    {B : Type a} [Category.{b} B] {B' : Type a'} [Category.{b'} B']
    {H : Bᵒᵖ × B ⥤ B} {H' : B'ᵒᵖ × B' ⥤ B'}
    {M : CoefficientClosedStructure H} {s : @SymmetricCategory B _ M.monoidal}
    {M' : CoefficientClosedStructure H'} {s' : @SymmetricCategory B' _ M'.monoidal}
    {F : B ⥤ B'} (V : SixFunctorClosedComparison M s M' s' F)
    (o : F.obj M.monoidal.tensorUnit ≅ M'.monoidal.tensorUnit) : Prop :=
  ∀ K : B, V.tensor.hom.app (K, M.monoidal.tensorUnit) ≫
    M'.tensor.map (Prod.mkHom (𝟙 (F.obj K)) o.hom) ≫
    (M'.monoidal.rightUnitor (F.obj K)).hom = F.map (M.monoidal.rightUnitor K).hom

/-- Normalized scalar transport of the two evaluation maps, together with preservation
of perfect objects by the two resulting tensor functors.
Source: blueprint dual-perfect proof, Step 7
(blueprint: lem-sf-perfect-dual-pair-and-tate-stability). -/
def SfPerfectLineTransport
    {B : Type a} [Category.{b} B] {B' : Type a'} [Category.{b'} B']
    {H : Bᵒᵖ × B ⥤ B} {H' : B'ᵒᵖ × B' ⥤ B'}
    {M : CoefficientClosedStructure H} {s : @SymmetricCategory B _ M.monoidal}
    {M' : CoefficientClosedStructure H'} {s' : @SymmetricCategory B' _ M'.monoidal}
    {F : B ⥤ B'} (V : SixFunctorClosedComparison M s M' s' F)
    (L N : B) (e : M.tensor.obj (L, N) ≅ M.monoidal.tensorUnit)
    (f : M.tensor.obj (N, L) ≅ M.monoidal.tensorUnit) : Prop :=
  ∃ o : F.obj M.monoidal.tensorUnit ≅ M'.monoidal.tensorUnit,
    SfLineUnitComparison V o ∧
    ∃ (e' : M'.tensor.obj (F.obj L, F.obj N) ≅ M'.monoidal.tensorUnit)
      (f' : M'.tensor.obj (F.obj N, F.obj L) ≅ M'.monoidal.tensorUnit),
      V.tensor.hom.app (L, N) ≫ e'.hom = F.map e.hom ≫ o.hom ∧
      V.tensor.hom.app (N, L) ≫ f'.hom = F.map f.hom ≫ o.hom ∧
      SfPerfectLinePair M' (F.obj L) (F.obj N) e' f'

/-- Module sheaves for the coefficient line; this is only a type abbreviation.
Source: blueprint dual-perfect proof, line representatives
(blueprint: lem-sf-perfect-dual-pair-and-tate-stability). -/
abbrev sfLineModules (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  SheafOfModules.{u + 1}
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

/-- The signed line in its actual shifted single-complex representative.
Source: blueprint dual-perfect proof, Step 6
(blueprint: lem-sf-perfect-dual-pair-and-tate-stability). -/
def sfShiftedLineComplex (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (L : sfLineModules X R) (m s : ℤ) : CochainComplex (sfLineModules X R) ℤ :=
  (shiftFunctor _ s).obj
    ((HomologicalComplex.single _ (.up ℤ) 0).obj (coefficientTwistLine X (R := R) L m))

/-- The ordinary signed pairing: multiplication at zero and functional evaluation
for either order of a positive power and its internal dual.
Source: blueprint dual-perfect proof, Step 5
(blueprint: lem-sf-perfect-dual-pair-and-tate-stability). -/
def sfSignedLinePairing (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (L : sfLineModules X R)
    (m : ℤ) (U : X.ProEtᵒᵖ) :
    (coefficientTwistLine X L m).val.obj U →
      (coefficientTwistLine X L (-m)).val.obj U → R.obj.obj U :=
  match m with
  | .ofNat 0 => fun x y ↦ (@id (R.obj.obj U) x) * (@id (R.obj.obj U) y)
  | .ofNat (_n + 1) => fun x y ↦ y.app (op (Over.mk (𝟙 U.unop))) x
  | .negSucc _n => fun x y ↦ x.app (op (Over.mk (𝟙 U.unop))) y

/-- Representative normalization of opposite shifted-line contraction. The heterogeneous
identities are precisely the canonical degree transports from -s+s=0 and s-s=0;
they quantify over every transported section. The scalar is the signed total-tensor
shift multiplier (-1)^(s*s), in both orders, including odd s and characteristic two.
Source: blueprint dual-perfect proof, Steps 5--6
(blueprint: lem-sf-perfect-dual-pair-and-tate-stability). -/
def SfShiftedLineChainEvaluation (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (L : sfLineModules X R)
    (m s : ℤ)
    (f : (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X) R).obj
      (sfShiftedLineComplex X R L m s, sfShiftedLineComplex X R L (-m) (-s)) ⟶
        CategoryTheory.ringedSiteDualityUnitComplex.{u + 1, u, u} (ProEt.topology X) R) :
    Prop :=
  ∀ (U : X.ProEtᵒᵖ) (x : (coefficientTwistLine X L m).val.obj U)
    (y : (coefficientTwistLine X L (-m)).val.obj U)
    (x' : ((sfShiftedLineComplex X R L m s).X (-s)).val.obj U)
    (y' : ((sfShiftedLineComplex X R L (-m) (-s)).X s).val.obj U),
    HEq x' x → HEq y' y →
    HEq ((f.f 0).val.app U
      (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X) R
        (sfShiftedLineComplex X R L m s) (sfShiftedLineComplex X R L (-m) (-s))
        (-s) s 0 (neg_add_cancel s) U x' y'))
      ((s * s).negOnePow • sfSignedLinePairing X R L m U x y)

/-- Evaluation in a normalized ringed-site tensor presentation, characterized on the
actual K-flat shifted single complexes and the preceding section formula.
Source: blueprint dual-perfect proof, Steps 5--6
(blueprint: lem-sf-perfect-dual-pair-and-tate-stability). -/
def SfRingedShiftedLineEvaluation (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : sixFunctorRingedModel.{u, u + 1, u} (ProEt.topology X) R)
    (L : sfLineModules X R) (m s : ℤ)
    (e : M.closed.tensor.obj
      (DerivedCategory.Q.obj (sfShiftedLineComplex X R L m s),
        DerivedCategory.Q.obj (sfShiftedLineComplex X R L (-m) (-s))) ⟶
      M.closed.monoidal.tensorUnit) : Prop :=
  ∃ (hL : CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := R)
      (sfShiftedLineComplex X R L m s))
    (hN : CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := R)
      (sfShiftedLineComplex X R L (-m) (-s))),
    ∃ f : (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X) R).obj
      (sfShiftedLineComplex X R L m s, sfShiftedLineComplex X R L (-m) (-s)) ⟶
        CategoryTheory.ringedSiteDualityUnitComplex.{u + 1, u, u} (ProEt.topology X) R,
      SfShiftedLineChainEvaluation X R L m s f ∧
      (M.models.iso (ProEt.topology X) R M.closed
        (sfShiftedLineComplex X R L m s) (sfShiftedLineComplex X R L (-m) (-s))
        hL hN).hom ≫ e ≫ M.unitIso.hom = DerivedCategory.Q.map f

/-- A line pair in a finite-Tor domain is normalized by its fully faithful ordinary
ringed-site model. Equality, rather than an arbitrary line trivialization, fixes its
representatives. Both evaluation orders are prescribed independently.
Source: blueprint dual-perfect proof, Steps 5--7
(blueprint: lem-sf-perfect-dual-pair-and-tate-stability). -/
def SfNormalizedRingedLinePair
    {B : Type a} [Category.{b} B] {P : ObjectProperty B}
    {Q : ObjectProperty (Bᵒᵖ × B)} {H : Q.FullSubcategory ⥤ B}
    (M : SixFunctorClosedDomain P Q H) (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (A : sixFunctorRingedModel.{u, u + 1, u} (ProEt.topology X) R)
    {F : P.FullSubcategory ⥤ DerivedCategory (sfLineModules X R)}
    (V : SixFunctorClosedComparison M.closed M.symmetric A.closed A.symmetric F)
    (T : sfLineModules X R) (m s : ℤ) (L N : P.FullSubcategory)
    (e : M.closed.tensor.obj (L, N) ≅ M.closed.monoidal.tensorUnit)
    (f : M.closed.tensor.obj (N, L) ≅ M.closed.monoidal.tensorUnit) : Prop :=
  ∃ (hL : F.obj L = DerivedCategory.Q.obj (sfShiftedLineComplex X R T m s))
    (hN : F.obj N = DerivedCategory.Q.obj (sfShiftedLineComplex X R T (-m) (-s)))
    (o : F.obj M.closed.monoidal.tensorUnit ≅ A.closed.monoidal.tensorUnit),
    SfLineUnitComparison V o ∧
    ∃ (e₀ : A.closed.tensor.obj
        (DerivedCategory.Q.obj (sfShiftedLineComplex X R T m s),
          DerivedCategory.Q.obj (sfShiftedLineComplex X R T (-m) (-s))) ⟶
        A.closed.monoidal.tensorUnit)
      (f₀ : A.closed.tensor.obj
        (DerivedCategory.Q.obj (sfShiftedLineComplex X R T (-m) (-s)),
          DerivedCategory.Q.obj (sfShiftedLineComplex X R T m s)) ⟶
        A.closed.monoidal.tensorUnit),
      SfRingedShiftedLineEvaluation X R A T m s e₀ ∧
      (∃ f₁ : A.closed.tensor.obj
          (DerivedCategory.Q.obj (sfShiftedLineComplex X R T (-m) (-s)),
            DerivedCategory.Q.obj (sfShiftedLineComplex X R T (- -m) (- -s))) ⟶
          A.closed.monoidal.tensorUnit,
        HEq f₀ f₁ ∧ SfRingedShiftedLineEvaluation X R A T (-m) (-s) f₁) ∧
      V.tensor.hom.app (L, N) ≫
        A.closed.tensor.map (Prod.mkHom (eqToHom hL) (eqToHom hN)) ≫ e₀ =
          F.map e.hom ≫ o.hom ∧
      V.tensor.hom.app (N, L) ≫
        A.closed.tensor.map (Prod.mkHom (eqToHom hN) (eqToHom hL)) ≫ f₀ =
          F.map f.hom ≫ o.hom

/-- The finite-stage line assertion, in the actual finite-Tor category.
Source: blueprint dual-perfect proof, Steps 5--6 and 8
(blueprint: lem-sf-perfect-dual-pair-and-tate-stability). -/
def SfFinitePerfectLines
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
    [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    {n : ℕ} (S : SixFunctorDatum D C E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)))
    (X : SixFunctorSpace D) (m s : ℤ) : Prop :=
  ∃ (L N : (S.toSixFunctorOperationDatum.finiteTorDomain X).FullSubcategory)
    (e : (S.finiteClosed X).closed.tensor.obj (L, N) ≅
      (S.finiteClosed X).closed.monoidal.tensorUnit)
    (f : (S.finiteClosed X).closed.tensor.obj (N, L) ≅
      (S.finiteClosed X).closed.monoidal.tensorUnit),
    SfNormalizedRingedLinePair (S.finiteClosed X) X.obj.left
      (integralCoefficientCommRingSheaf C.l E X.obj.left n) (S.finiteModel X)
      (S.finiteModelComparison X).comparison (purTwistFiniteOne X.obj.left C.l E n)
      m s L N e f ∧ SfPerfectLinePair (S.finiteClosed X).closed L N e f

/-- A completed line and its rational image, with the same normalized evaluations.
Source: blueprint dual-perfect proof, integral and rational cases, Steps 5--8
(blueprint: lem-sf-perfect-dual-pair-and-tate-stability). -/
def SfIntegralRationalPerfectLines
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (M : SixFunctorCoefficientClosedModels l E X) (m s : ℤ) : Prop :=
  ∃ (L N : ObjectProperty.FullSubcategory
        (fun K : sfIntegralConstructibleCategory l E X ↦
          finiteTorConstructibleIntegral l E X K.obj))
    (e : M.integral.closed.tensor.obj (L, N) ≅ M.integral.closed.monoidal.tensorUnit)
    (f : M.integral.closed.tensor.obj (N, L) ≅ M.integral.closed.monoidal.tensorUnit),
    SfNormalizedRingedLinePair M.integral X
      (completedIntegralCommRingSheafUnrestricted l E X) M.model
      M.realization.comparison (purTwistIntegralModule X l E) m s L N e f ∧
    SfPerfectLinePair M.integral.closed L N e f ∧
    SfPerfectLineTransport M.rationalization.comparison L N e f

/-- The original coefficient field's already supplied completed and rational models.
Source: blueprint dual-perfect proof, coefficient stage convention
(blueprint: lem-sf-perfect-dual-pair-and-tate-stability). -/
def sfPerfectLineModels
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
    [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    {n : ℕ} {hn : 1 ≤ n} (S : SixFunctorDatum D C E n hn) (X : SixFunctorSpace D) :
    SixFunctorCoefficientClosedModels C.l E X.obj.left where
  integral := S.integralClosed X
  model := S.integralModel X
  realization := S.integralModelComparison X
  rational := S.rationalClosed X
  rationalization := S.rationalClosedComparison X

/-- Common-stage lines are images of the same normalized integral lines, via the
specified rationalization and common-stage inclusion, with evaluation preserved.
Source: blueprint dual-perfect proof, Step 7
(blueprint: lem-sf-perfect-dual-pair-and-tate-stability). -/
def SfCommonPerfectLines
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
    [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    {n : ℕ} {hn : 1 ≤ n} (S : SixFunctorDatum D C E n hn) (X : SixFunctorSpace D)
    (F : Padic.FiniteCoefficientFields C.l C.Qbar) (m s : ℤ) : Prop :=
  ∃ (L N : ObjectProperty.FullSubcategory
        (fun K : sfIntegralConstructibleCategory C.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar F) X.obj.left ↦
          finiteTorConstructibleIntegral C.l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar F) X.obj.left K.obj))
    (e : (S.coefficientClosedModels F X).integral.closed.tensor.obj (L, N) ≅
      (S.coefficientClosedModels F X).integral.closed.monoidal.tensorUnit)
    (f : (S.coefficientClosedModels F X).integral.closed.tensor.obj (N, L) ≅
      (S.coefficientClosedModels F X).integral.closed.monoidal.tensorUnit),
    SfNormalizedRingedLinePair (S.coefficientClosedModels F X).integral X.obj.left
      (completedIntegralCommRingSheafUnrestricted C.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar F) X.obj.left)
      (S.coefficientClosedModels F X).model
      (S.coefficientClosedModels F X).realization.comparison
      (purTwistIntegralModule X.obj.left C.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar F)) m s L N e f ∧
    ∃ o : (sixFunctorDomainChange _ _ _
        (S.coefficientClosedModels F X).rationalization.domain).obj
        (S.coefficientClosedModels F X).integral.closed.monoidal.tensorUnit ≅
          (S.coefficientClosedModels F X).rational.closed.monoidal.tensorUnit,
      SfLineUnitComparison (S.coefficientClosedModels F X).rationalization.comparison o ∧
      ∃ (e' : (S.coefficientClosedModels F X).rational.closed.tensor.obj
          ((sixFunctorDomainChange _ _ _
              (S.coefficientClosedModels F X).rationalization.domain).obj L,
            (sixFunctorDomainChange _ _ _
              (S.coefficientClosedModels F X).rationalization.domain).obj N) ≅
            (S.coefficientClosedModels F X).rational.closed.monoidal.tensorUnit)
        (f' : (S.coefficientClosedModels F X).rational.closed.tensor.obj
          ((sixFunctorDomainChange _ _ _
              (S.coefficientClosedModels F X).rationalization.domain).obj N,
            (sixFunctorDomainChange _ _ _
              (S.coefficientClosedModels F X).rationalization.domain).obj L) ≅
            (S.coefficientClosedModels F X).rational.closed.monoidal.tensorUnit),
        (S.coefficientClosedModels F X).rationalization.comparison.tensor.hom.app (L, N) ≫
          e'.hom = (sixFunctorDomainChange _ _ _
            (S.coefficientClosedModels F X).rationalization.domain).map e.hom ≫ o.hom ∧
        (S.coefficientClosedModels F X).rationalization.comparison.tensor.hom.app (N, L) ≫
          f'.hom = (sixFunctorDomainChange _ _ _
            (S.coefficientClosedModels F X).rationalization.domain).map f.hom ≫ o.hom ∧
        SfPerfectLineTransport (S.commonClosedComparison F X).comparison _ _ e' f'

/-- Perfect duals, actual dual-pair transposes and coefficient biduality, together
with evaluation-normalized inverse shifted Tate lines at all four coefficient stages.
The finite-field and coefficient parameters are exactly those of S; X need only be
finite type over its algebraic closure, as encoded by SixFunctorSpace.
Source: current blueprint, sk-thm-sf-dual-perfect proof, last sentence
(blueprint: lem-sf-perfect-dual-pair-and-tate-stability).

Proof: (1) For an exact pair compare its tensor adjunction with the recorded closed
adjunction by counit-compatible uniqueness of right adjoints. The component at the
unit is exactly the transpose of the given evaluation, and preserves that evaluation.
(2) Transport coevaluation along this isomorphism, then swap the exact pair using
symmetry. The coefficient dual is dualizable; site-perfect dual closure ensures the
same coefficient domain, with completed and finite-stage conventions.
(3) Apply the comparison to the swapped pair: its transpose is ringedSiteBidual,
hence is invertible. (4) Braiding naturality and involution show that the displayed
inverse composed with this bidual arrow is the original first triangle. Invertibility
gives the other inverse identity.
(5) Trivialize the published Tate line. Opposite signed powers evaluate by multiplication
or functional evaluation; the unbounded flat-line and integral reduction/restriction
results identify this with the actual derived and completed contractions.
(6) Extract the opposite shifts by totalTensor_signed_coherence. Both evaluation
scalars are (-1)^(s*s); they cancel in either triangle. The completed-tensor shift
comparison identifies these with the signed maps on every finite quotient and the
Roos product cone. (7) Rationalize, and then pass to a common finite coefficient
field. CompletedLineTensor scalar coherence preserves the evaluations; bilinearity
and the common-stage Hom colimit preserve their equations under field enlargement.
(8) Reassociate and contract to obtain the two natural tensor inverses. The shifted
lines are site-perfect, with translated finite-Tor bounds. ExactPairing.tensor shows
that both tensor functors preserve perfect objects, including the coefficient dual.
Dependencies: lem-sfb-dual-tensor-adjunctions, det-sp-unique-right-adjoint,
lem-sf-exact-pairing-symmetric-swap, prop-sf-dualizable, lem-sfb-braiding-naturality,
det-def-sp-tate-twist-locally-free, prop-weil-twist-preserves,
lem-pur-line-unbounded-derived-tensor, lem-pur-integral-line-reduction-restriction,
lem-pur-total-tensor-signed-coherence, lem-sf-completed-tensor-shift-right,
lem-pur-completed-line-tensor-coherence, lem-sf-exact-pairing-tensor. -/
theorem sfPerfectDualPairAndTateStability
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
    [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    {n : ℕ} (S : SixFunctorDatum D C E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)))
    (X : SixFunctorSpace D) :
    SfPerfectDualPair (S.finiteClosed X).closed (S.finiteClosed X).symmetric ∧
    SfPerfectDualPair (S.integralClosed X).closed (S.integralClosed X).symmetric ∧
    SfPerfectDualPair (S.rationalClosed X).closed (S.rationalClosed X).symmetric ∧
    SfPerfectDualPair (S.commonClosed X).closed (S.commonClosed X).symmetric ∧
    ∀ m s : ℤ, SfFinitePerfectLines S X m s ∧
      SfIntegralRationalPerfectLines C.l E X.obj.left (sfPerfectLineModels S X) m s ∧
      SfCommonPerfectLines S X (Padic.finiteCoefficientBase C.l C.Qbar) m s := by
  sorry

end WeilConjectures
