/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.CompactificationCoherence
public import Sheaf.Paper.ExchangeFunctoriality
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.FiniteTorAmplitudeSites

import Sheaf.Paper.PullbackTorAmplitude
import Sheaf.Paper.FiniteCoefficientTensorCtf
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.Paper.RefinementComparisonIsomorphism
import Sheaf.AlgebraicGeometry.ProperOpenComparisonSiteNormalization
import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
import Sheaf.Paper.DerivedPullbackTensorIso
import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
import Sheaf.SixFunctors.ProperOpenProjectionMate
import Sheaf.Paper.IntegralResidueTor
import Sheaf.SixFunctors.OpenTensorNormalization
import Sheaf.Paper.SfIntegralDirectImageConstructible
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Paper.CompletedOpenExchangeTransport
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients

/-!
# Projection transformations and compactification comparison

Source: main-20261015 blueprint, `sec-six-functors/sk-prop-sf-pf-coherence`,
`prop-sf-pf-coherence.proof.md`, compactification-independence sentence
(blueprint: lem-fix-projection-compactification-comparison).

The finite clause retains the two etale-origin witnesses and uses the actual common-
refinement composite. The other clauses use the normalized completed, localized and
common-stage operations of the recorded six-functor datum. Only rho is an isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.FixProjectionCompactification

/-- Package a given compactification with the identity base-change square. This selects
its projection from the recorded exchange/projection family without choosing any new map.
Source: prop-sf-pf-coherence.proof.md, chosen compactification
(blueprint: lem-fix-projection-compactification-comparison). -/
def identitySquare {D : FiniteFieldDatum.{u}} {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) (c : Compactification f.hom.left) : SixFunctorCompactifiedSquare D := by
  letI : LocallyOfFiniteType Y.obj.hom := Y.property.1
  letI : QuasiCompact Y.obj.hom := Y.property.2
  let Z : SixFunctorSpace D :=
    ⟨Over.mk (c.g ≫ Y.obj.hom),
      inferInstanceAs (LocallyOfFiniteType (c.g ≫ Y.obj.hom)),
      inferInstanceAs (QuasiCompact (c.g ≫ Y.obj.hom))⟩
  let i : X ⟶ Z := ObjectProperty.homMk
    (Over.homMk c.i (by
      change c.i ≫ c.g ≫ Y.obj.hom = X.obj.hom
      rw [← Category.assoc, ← c.comm]
      exact f.hom.w))
  let p : Z ⟶ Y := ObjectProperty.homMk (Over.homMk c.g rfl)
  have h : f = i ≫ p := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact c.comm
  exact
    { X := X, Y := Y, X' := X, Y' := Y, Z := Z, Z' := Z
      f := f, f' := f, g := 𝟙 Y, g' := 𝟙 X
      i := i, i' := i, p := p, p' := p, h := 𝟙 Z
      open_i := c.isOpenImmersion, open_i' := c.isOpenImmersion
      proper_p := c.isProper, proper_p' := c.isProper
      factorization := h, factorization' := h
      square := IsPullback.of_horiz_isIso ⟨by simp⟩
      properSquare := IsPullback.of_horiz_isIso ⟨by simp⟩
      openSquare := IsPullback.of_horiz_isIso ⟨by simp⟩
      squareComm := by simp, properComm := by simp, openComm := by simp }

/-- The displayed compactification comparison equation at a higher coefficient stage.
The tensor, projection and rho are all taken from the supplied normalized operation datum;
P is instantiated below with exactly the recorded finite-Tor domain at that stage.
Source: prop-sf-pf-coherence.proof.md, compactification-independence sentence
(blueprint: lem-fix-projection-compactification-comparison). -/
def higherLaw {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (T : ∀ X, B X ⥤ B X ⥤ B X)
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    (P : ∀ Y, ObjectProperty (B Y)) : Prop :=
  ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c₁ c₂ : Compactification f.hom.left) (K : B X) (L : B Y), P Y L →
    (A (identitySquare f c₁)).projectionComponent K L ≫
        (S.comparison f c₁ c₂).hom.app
          (((T X).obj K).obj ((S.pull f).obj L)) =
      ((T Y).map ((S.comparison f c₁ c₂).hom.app K)).app L ≫
        (A (identitySquare f c₂)).projectionComponent K L

/-- The finite-coefficient equation in fixed-scalar coordinates. The common-refinement
comparison is theta(d,c1) inverse followed by theta(d,c2), exactly as prescribed by
compactification_coherence. The retained target witness is transported by e; quantifying
over e keeps every presentation of the tensor object, rather than choosing an antecedent.
K is bounded constructible, and only L is required to have finite Tor amplitude.
Source: prop-sf-pf-coherence.proof.md, compactification-independence sentence
(blueprint: lem-fix-projection-compactification-comparison). -/
def finiteLaw (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (hl : IsUnit (C.l : D.k)) : Prop :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  ∀ {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c₁ c₂ d : Compactification f) (r₁ : d.Refinement c₁) (r₂ : d.Refinement c₂)
    (O : RefinementFiniteLevelOrigin C.l E n hn X)
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))))
    (OT : RefinementFiniteLevelOrigin C.l E n hn X),
    let K := refinementFiniteLevelFixedObject C.l E n hn X O
    let M := ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
    let T := ((derivedTensor M X).obj K).obj ((upperStar M f).leftDerivedFunctor.obj L)
    ∀ (e : refinementFiniteLevelFixedObject C.l E n hn X OT ≅ T),
    intrinsicFiniteTorsionConstructible C.l E n hn X
      ((sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing C.l E n)).functor.obj
        K) →
    finiteTorConstructible C.l E n hn Y
      ((sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing C.l E n)).functor.obj
        L) →
    let rhoK := (refinementComparisonIsomorphism D.k C.l hl E n hn f r₁ O).symm ≪≫
      refinementComparisonIsomorphism D.k C.l hl E n hn f r₂ O
    let rhoT := (rightDerivedLowerShriekOfCompactification M c₁).mapIso e.symm ≪≫
      (refinementComparisonIsomorphism D.k C.l hl E n hn f r₁ OT).symm ≪≫
      refinementComparisonIsomorphism D.k C.l hl E n hn f r₂ OT ≪≫
      (rightDerivedLowerShriekOfCompactification M c₂).mapIso e
    ((projectionMapOfCompactification M c₁).app K).app L ≫ rhoT.hom =
      ((derivedTensor M Y).map rhoK.hom).app L ≫
        ((projectionMapOfCompactification M c₂).app K).app L

/-- Projection transformations agree for any two compactifications, at every specified
coefficient stage, with no assertion of invertibility of a projection transformation.
The finite clause includes the actual input and target etale-origin witnesses. The
integral clause uses the uniform finite-reduction Tor predicate, and the two field
clauses range over their entire bounded constructible categories.
Source: main-20261015 blueprint, prop-sf-pf-coherence.proof.md,
compactification-independence sentence
(blueprint: lem-fix-projection-compactification-comparison).

Proof plan:
1. Put T=K tensor Lf*L. Pullback preserves L's finite Tor interval; tensoring with K
   preserves bounded constructibility. Constructible pro-etale origin supplies T's witness
   (lem-sf-pullback-tor-amplitude, lem-sf-tensor-ctf, lem-sf-proetale-constructible-origin).
2. Expand PF as proper counit projection followed by proper image of the open tensor map.
   Expand theta as proper composition followed by the inverse proper/open comparison
   (def-exchange-projection, def-sf-refinement-comparison-isomorphism). Site normalization
   and strict-tower proper/open calculus identify exactly this comparison.
3. Transpose the composite proper projection under the composite pull/push adjunction.
   Naturality of tensor-pullback moves the inner counit past tensor; composite-adjunction
   counit compatibility identifies it with the single composite counit
   (fix-prop-adjunctions, lem-pur-derived-pullback-tensor-iso).
4. Apply lem-sf-proper-open-tensor-compatibility to the refinement square with identity
   on X. It is valid also for noncartesian refinements. This gives the compatibility of
   the specified proper/open map with the open tensor and proper projection maps.
5. Paste that square with the proper counit-projection composite. Naturality in the first
   tensor input identifies PF1 (theta inverse tensor 1) with theta inverse PF2. Cancel
   theta at K and T, using prop-compactification-coherence-detailed on witnessed inputs.
6. Take a common refinement d. Its two identities imply the equation for
   rho=theta(d,c1) inverse theta(d,c2); independence and cocycle identify this with rho.
7. Integrally, lem-coef-integral-residue-tor gives uniform reduction bounds. Exact open
   extension preserves bounds and constructibility, and lem-sf-open-tensor-normalization
   gives normalization and Tor bounds. Proper pushforward and completed tensor/pullback
   preserve the intermediate constructible domains (lem-sf-integral-direct-image-
   constructible, lem-pur-integral-operations-preserve-constructible).
8. Repeat the equality in the derived category of normalized systems, using
   lem-sf-proper-open-tensor-compatibility there. All compactifying schemes are Noetherian
   and quasi-separated, so the opens are quasi-compact. The completed open comparison
   preserves completeness (lem-cbc-completed-extension-zero-comparison).
   lem-sf-integral-compactification-system-realization intertwines every specified map;
   applying its total-limit functor gives the integral equality. Use the completed
   comparisons of fix-lem-exchanges(4), without claiming finite evaluations detect maps.
9. Apply scalar localization to the integral equality for E, including denominators.
   For Qbar represent inputs and maps at one common finite field, apply that equality,
   and use the scalar-extension identity/cocycle of def-exchange-projection to obtain
   the same morphism class after every enlargement. No projection map is inverted.
-/
theorem comparison
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k)) :
    finiteLaw D C E n hn hl ∧
    higherLaw S.higher.integral S.higher.integralTensor S.higher.integralExchange
      (fun Y K ↦ finiteTorConstructibleIntegral C.l E Y.obj.left K.obj) ∧
    higherLaw S.higher.rational S.higher.rationalTensor S.higher.rationalExchange
      (fun _ _ ↦ True) ∧
    higherLaw S.closure.commonStage S.closure.commonStageTensor S.closure.commonStageExchange
      (fun _ _ ↦ True) := by
  sorry

end WeilConjectures.FixProjectionCompactification
