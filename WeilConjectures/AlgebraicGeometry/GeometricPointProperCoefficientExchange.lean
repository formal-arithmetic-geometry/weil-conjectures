/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinaryProperCoefficientDomain
public import WeilConjectures.AlgebraicGeometry.ScalarGeometricExchangeRectangle
public import WeilConjectures.AlgebraicGeometry.InternalScalarMateTransitivity
public import WeilConjectures.AlgebraicGeometry.StrictCoefficientProperReduction
public import WeilConjectures.SixFunctors.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.IntegralNativeDirectComparison
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientDerivedSystemEvaluationData
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded
public import WeilConjectures.AlgebraicGeometry.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.CompactSupportNativeSystemEvaluation
public import WeilConjectures.SixFunctors.CommonFieldLatticeGenerators
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistsOfUniverses
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import WeilConjectures.AlgebraicGeometry.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.SmoothPurityNormalizedEquivalence
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Proper exchange at ordinary condensed geometric fibres

Source: Bhatt--Scholze 6.7.5, 6.7.14, 6.8.14--15; Stacks 095T and 0GL6.
(blueprint: lem-pur-geometric-point-proper-coefficient-exchange).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.OrdinaryProper
open CondensedRing QuotientChange

/-- Canonical identity unitor for the actual ordinary derived inverse image.
Source: Stacks 07A6
(blueprint: lem-pur-geometric-point-proper-coefficient-exchange). -/
def pullId (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) : L Λ.X (𝟙 X) ≅ 𝟭 _ := by
  unfold L moduleObjectDerivedPullback
  exact CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ.X (𝟙 X) ≪≫
    Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ.X X) ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- Canonical identity unitor for the actual ordinary derived direct image.
Source: Stacks 07A6
(blueprint: lem-pur-geometric-point-proper-coefficient-exchange). -/
def pushId (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) : F Λ.X (𝟙 X) ≅ 𝟭 _ := by
  unfold F moduleObjectDerivedPushforward
  letI : PreservesFiniteColimits (CondensedRing.lowerStar Λ.X (𝟙 X)) :=
    preservesFiniteColimits_of_natIso (CondensedRing.lowerStarId Λ.X X).symm
  exact (CondensedRing.lowerStar Λ.X (𝟙 X)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryNatIso (CondensedRing.lowerStarId Λ.X X) ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- The conclusions are bundled only to keep the single theorem readable. Every map
in these fields is the existing normalized ordinary exchange or projection mate.
Source: Bhatt--Scholze 6.7--6.8; Stacks 095T, 0GL6, 0E47
(blueprint: lem-pur-geometric-point-proper-coefficient-exchange). -/
structure Conclusions (l : ℕ) [Fact l.Prime]
    {X' X Y' Y : Scheme.{u}} {hX : X' ⟶ X} {q' : X' ⟶ Y'}
    {q : X ⟶ Y} {h : Y' ⟶ Y} (sq : ChosenCartesianSquare hX q' q h) : Prop where
  /-- The actual unit-square-counit mate is invertible on every indicated input. -/
  exchange : ∀ (Λ : ScalarSixRing.{u})
    (K : DerivedCategory.{u + 1} (Modules Λ.X X)), Input l X Λ K →
      IsIso ((scalarAmbientExchange Λ.X sq).app K)
  /-- Direct image and the ordinary pullbacks in the integral square remain complete. -/
  complete : ∀ (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E.1)
    (_hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1))
    (K : DerivedCategory.{u + 1} (Modules (latticeIntegralRing.{u} l E).X X)),
    integralInput l E π X K →
    IntegralModelsEmbedded.completedComplete l E π Y
      ((F (latticeIntegralRing.{u} l E).X q).obj K) ∧
    IntegralModelsEmbedded.completedComplete l E π Y'
      ((L (latticeIntegralRing.{u} l E).X h).obj
        ((F (latticeIntegralRing.{u} l E).X q).obj K)) ∧
    IntegralModelsEmbedded.completedComplete l E π X'
      ((L (latticeIntegralRing.{u} l E).X hX).obj K) ∧
    IntegralModelsEmbedded.completedComplete l E π Y'
      ((F (latticeIntegralRing.{u} l E).X q').obj
        ((L (latticeIntegralRing.{u} l E).X hX).obj K))
  /-- Projection is for the actual normalized balancing mate, at both proper edges. -/
  projection : ∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ'), Change l a →
    ∀ (b : ∀ {U V : Scheme.{u}} (f : U ⟶ V),
      D a.hom.hom V ⋙ L Λ'.X f ≅ L Λ.X f ⋙ D a.hom.hom U),
    (∀ {U V : Scheme.{u}} (f : U ⟶ V), PullNormalized a.hom.hom f (b f)) →
    (∀ (K : DerivedCategory.{u + 1} (Modules Λ.X X)), Input l X Λ K →
      Input l X Λ' ((D a.hom.hom X).obj K) → IsIso ((rho a.hom.hom q (b q)).app K)) ∧
    (∀ (K : DerivedCategory.{u + 1} (Modules Λ.X X')), Input l X' Λ K →
      Input l X' Λ' ((D a.hom.hom X').obj K) →
        IsIso ((rho a.hom.hom q' (b q')).app K))
  /-- Equality of the two full scalar/geometric routes, before point evaluation. -/
  rectangle : ∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ'), Change l a →
    ∀ (b : ∀ {U V : Scheme.{u}} (f : U ⟶ V),
      D a.hom.hom V ⋙ L Λ'.X f ≅ L Λ.X f ⋙ D a.hom.hom U),
    (∀ {U V : Scheme.{u}} (f : U ⟶ V), PullNormalized a.hom.hom f (b f)) →
    ∀ (K : DerivedCategory.{u + 1} (Modules Λ.X X)), Input l X Λ K →
      Input l X Λ' ((D a.hom.hom X).obj K) →
      scalarExchangeLeft a.hom.hom sq b K = scalarExchangeRight a.hom.hom sq b K

/-- Proper exchange and coefficient projection, including arbitrary geometric points.
The finite-type alternative is stated on h followed by the structural map. In the other
alternative Y' is isomorphic to Spec of an arbitrary algebraically closed field; that
field is not required to be finite type over k.

Source: Bhatt--Scholze 6.7.5, 6.7.14, 6.8.14--15; Stacks 095T and 0GL6
(blueprint: lem-pur-geometric-point-proper-coefficient-exchange).

Proof: finite coefficients use ordinary etale proper base change and coefficient change.
Integral direct image preserves completeness and bounded constructibility. The ordinary
integral pullback theorem gives completeness of both exchange endpoints, also over the
geometric field. Reduction of the specified mate is finite proper exchange; derived
Nakayama proves it invertible. Quotient projections are the actual cone comparisons;
finite integral and field extensions are finite free; localization uses the qcqs proper
scalar comparison; the closure uses its finite-subextension colimit. The normalized
scalar/geometric rectangle transfers integral exchange to the rational and closure
inputs. Its mate calculation proves the displayed rectangle without any flatness
assumption, including the nonflat quotient changes. -/
theorem geometricPointProperCoefficientExchange
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] (hpl : p ≠ l)
    (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (q : X ⟶ Y) [q.IsOver (Spec (.of k))] [IsProper q]
    {X' Y' : Scheme.{u}} (h : Y' ⟶ Y) (q' : X' ⟶ Y') (hX : X' ⟶ X)
    (sq : ChosenCartesianSquare hX q' q h)
    (hh : (LocallyOfFiniteType (h ≫ (Y ↘ Spec (.of k))) ∧
        QuasiCompact (h ≫ (Y ↘ Spec (.of k))) ∧
        IsSeparated (h ≫ (Y ↘ Spec (.of k)))) ∨
      ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω), Nonempty (Y' ≅ Spec (.of Ω))) :
    Conclusions l sq := by
  sorry

/-- Naturality of the specified ambient exchange and projection maps.
Source: Stacks 07A6 and 0E47
(blueprint: lem-pur-geometric-point-proper-coefficient-exchange).

Proof: both maps are natural transformations, built from derived adjunction units,
counits, and the normalized pullback square; apply their naturality equations. -/
theorem comparisonNaturality
    {X' X Y' Y : Scheme.{u}} {hX : X' ⟶ X} {q' : X' ⟶ Y'}
    {q : X ⟶ Y} {h : Y' ⟶ Y} (sq : ChosenCartesianSquare hX q' q h)
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (b : D a.hom.hom Y ⋙ L Λ'.X q ≅ L Λ.X q ⋙ D a.hom.hom X)
    {K J : DerivedCategory.{u + 1} (Modules Λ.X X)} (f : K ⟶ J) :
    (L Λ.X h).map ((F Λ.X q).map f) ≫ (scalarAmbientExchange Λ.X sq).app J =
      (scalarAmbientExchange Λ.X sq).app K ≫ (F Λ.X q').map ((L Λ.X hX).map f) ∧
    (D a.hom.hom Y).map ((F Λ.X q).map f) ≫ (rho a.hom.hom q b).app J =
      (rho a.hom.hom q b).app K ≫ (F Λ'.X q).map ((D a.hom.hom X).map f) := by
  sorry

/-- The horizontal identity exchange is the canonical inverse-image unitor square.
Source: Stacks 07A6
(blueprint: lem-pur-geometric-point-proper-coefficient-exchange).

Proof: unfold the exchange mate, cancel the identity inverse-image unitors, and use
the two adjunction triangle identities. -/
theorem comparisonSchemeIdentity
    (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (q : X ⟶ Y)
    (sq : ChosenCartesianSquare (𝟙 X) q q (𝟙 Y))
    (K : DerivedCategory.{u + 1} (Modules Λ.X X)) :
    (scalarAmbientExchange Λ.X sq).app K ≫
        (F Λ.X q).map ((pullId Λ X).hom.app K) =
      (pullId Λ Y).hom.app ((F Λ.X q).obj K) := by
  sorry

/-- The vertical identity exchange is the canonical direct-image unitor square.
Source: Stacks 07A6
(blueprint: lem-pur-geometric-point-proper-coefficient-exchange).

Proof: transpose under the identity geometric adjunction and cancel its triangle
identities. The exchange reduces to the direct-image unitor square expressed by pushId. -/
theorem comparisonOtherIdentities
    (Λ : ScalarSixRing.{u}) {Y' Y : Scheme.{u}} (h : Y' ⟶ Y)
    (sq : ChosenCartesianSquare h (𝟙 Y') (𝟙 Y) h)
    (K : DerivedCategory.{u + 1} (Modules Λ.X Y)) :
    (scalarAmbientExchange Λ.X sq).app K ≫
        (pushId Λ Y').hom.app ((L Λ.X h).obj K) =
      (L Λ.X h).map ((pushId Λ Y).hom.app K) := by
  sorry

/-- The projection mate at an identity scheme map preserves the direct-image unitors.
Source: Stacks 07A6
(blueprint: lem-pur-geometric-point-proper-coefficient-exchange).

Proof: use PullNormalized to identify b with the ordinary tensor/pullback balancing
comparison at the identity scheme map. Transpose its hom under the two identity
geometric adjunctions. Cancel their units and counits by the triangle identities;
the remaining arrows are exactly the two pushId unitors displayed here. -/
theorem comparisonProjectionSchemeIdentity
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (X : Scheme.{u})
    (b : D a.hom.hom X ⋙ L Λ'.X (𝟙 X) ≅ L Λ.X (𝟙 X) ⋙ D a.hom.hom X)
    (hb : PullNormalized a.hom.hom (𝟙 X) b)
    (K : DerivedCategory.{u + 1} (Modules Λ.X X)) :
    (rho a.hom.hom (𝟙 X) b).app K ≫
        (pushId Λ' X).hom.app ((D a.hom.hom X).obj K) =
      (D a.hom.hom X).map ((pushId Λ X).hom.app K) := by
  sorry

/-- An identity coefficient change gives the canonical scalar identity comparison.
Source: Stacks 07A6
(blueprint: lem-pur-geometric-point-proper-coefficient-exchange).

Proof: the computation-counit normalization identifies the scalar pullback square
with the two scalar identity unitors; its mate is the corresponding unitor square. -/
theorem comparisonScalarIdentity
    (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (q : X ⟶ Y)
    (b : D (𝟙 Λ.X) Y ⋙ L Λ.X q ≅ L Λ.X q ⋙ D (𝟙 Λ.X) X)
    (hb : PullNormalized (𝟙 Λ.X) q b)
    (K : DerivedCategory.{u + 1} (Modules Λ.X X)) :
    (rho (𝟙 Λ.X) q b).app K =
      (scalarExtensionId Λ.X Y).hom.app ((F Λ.X q).obj K) ≫
        (F Λ.X q).map ((scalarExtensionId Λ.X X).inv.app K) := by
  sorry

/-- Projection mates compose under the canonical normalized scalar associators.
Source: Stacks 07A6, 07A4; the node's final mate computation
(blueprint: lem-pur-geometric-point-proper-coefficient-exchange).

Proof: use the K-flat computation-counit normalization to identify the scalar
associators with c tensor (b tensor x) mapped to cb tensor x. Transpose under the
final geometric adjunction; naturality and the intermediate triangle identity make
both transposes scalar extension of the original counit. This also covers nonflat
quotient changes and either identity coefficient arrow. -/
theorem comparisonScalarComposition
    {Λ₀ Λ₁ Λ₂ : ScalarSixRing.{u}} (a : Λ₀ ⟶ Λ₁) (b : Λ₁ ⟶ Λ₂)
    {X Y : Scheme.{u}} (q : X ⟶ Y)
    (b01 : D a.hom.hom Y ⋙ L Λ₁.X q ≅ L Λ₀.X q ⋙ D a.hom.hom X)
    (b12 : D b.hom.hom Y ⋙ L Λ₂.X q ≅ L Λ₁.X q ⋙ D b.hom.hom X)
    (b02 : D (a.hom.hom ≫ b.hom.hom) Y ⋙ L Λ₂.X q ≅
      L Λ₀.X q ⋙ D (a.hom.hom ≫ b.hom.hom) X)
    (h01 : PullNormalized a.hom.hom q b01) (h12 : PullNormalized b.hom.hom q b12)
    (h02 : PullNormalized (a.hom.hom ≫ b.hom.hom) q b02) :
    ∃ (βX : D a.hom.hom X ⋙ D b.hom.hom X ≅ D (a.hom.hom ≫ b.hom.hom) X)
      (βY : D a.hom.hom Y ⋙ D b.hom.hom Y ≅ D (a.hom.hom ≫ b.hom.hom) Y),
      SuccessiveNormalized a.hom.hom b.hom.hom _ rfl X βX ∧
      SuccessiveNormalized a.hom.hom b.hom.hom _ rfl Y βY ∧
      ∀ K : DerivedCategory.{u + 1} (Modules Λ₀.X X),
        βY.hom.app ((F Λ₀.X q).obj K) ≫ (rho _ q b02).app K =
          (D b.hom.hom Y).map ((rho _ q b01).app K) ≫
            (rho _ q b12).app ((D a.hom.hom X).obj K) ≫
              (F Λ₂.X q).map (βX.hom.app K) := by
  sorry

end AlgebraicGeometry.ProEtale.OrdinaryProper

namespace WeilConjectures
open AlgebraicGeometry AlgebraicGeometry.Scheme PurCompactSupport

/-- The actual whole-system projection mate. The reduction/pullback comparison in
RealizationModel is characterized on whole K-flat systems before any finite evaluation.
We take its geometric adjunction mate, then the canonical derived native presentation.
Source: Stacks 07A6, 0941; Bhatt--Scholze 6.7.5
(blueprint: lem-pur-geometric-point-proper-coefficient-exchange). -/
def wholeProjection
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (o : IntegralSystemRealization.Operations l E)
    (model : IntegralSystemRealization.RealizationModel l E o) :
    push (completed l E) f ⋙ (IntegralSystemRealization.calculus l E Y).reduction ⟶
      (IntegralSystemRealization.calculus l E X).reduction ⋙
        ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) f :=
  (mateEquiv (IntegralSystemRealization.ringedAdj l E f) (o.direct f).adj
    (TwoSquare.mk _ _ _ _ (model.reductionPull f).inv)).natTrans ≫
      Functor.whiskerLeft (IntegralSystemRealization.calculus l E X).reduction
        (IntegralSystemRealization.integralNativeDirectIso l E f (o.direct f)).hom

/-- Proper coefficient projection is an isomorphism of the entire normalized strict
reduction system. Its finite evaluation is the exact scalar-adjunction mate. Its
whole-system definition above fixes the mate before evaluating, retaining the K-flat
normalization from RealizationModel. Taking the canonical lift of an embedded finite
coefficient field includes it at every scheme universe.

Source: Bhatt--Scholze 6.5.11, 6.7.5; Stacks 0941, 07A6
(blueprint: lem-pur-geometric-point-proper-coefficient-exchange).

Proof: transpose the normalized whole-system reduction/pullback comparison under
both geometric adjunctions. The native presentation preserves those adjunctions.
The strict proper-reduction calculation identifies every evaluated component with
the actual quotient projection, with the displayed reductionEvaluation and
finiteReductionIso factors. The two-term quotient resolution makes these maps
invertible. Joint conservativity of derived-system evaluations proves invertibility
of this very whole-system mate. Its source is a normalized reduction, so transport
normalization across the system isomorphism. No faithfulness of finite evaluation
is used to define or identify the whole-system arrow. -/
theorem properWholeReductionSystem
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (o : IntegralSystemRealization.Operations l E)
    (model : IntegralSystemRealization.RealizationModel l E o) :
    (∀ (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ),
      (coefficientSequenceDerivedEvaluation l E Y n).map
          ((wholeProjection l E f o model).app K) ≫
        (strictCoefficientProperEvaluation l E f n).hom.app
          ((IntegralSystemRealization.calculus l E X).reduction.obj K) =
      ((IntegralSystemRealization.calculus l E Y).reductionEvaluation n).hom.app
          ((push (completed l E) f).obj K) ≫
        (finiteReductionIso l E Y n).inv.app ((push (completed l E) f).obj K) ≫
        (properComparison (reduction l E (n + 1) (Nat.le_add_left 1 n)) f).app K ≫
        (push (finite l E (n + 1) (Nat.le_add_left 1 n)) f).map
          ((finiteReductionIso l E X n).hom.app K ≫
            ((IntegralSystemRealization.calculus l E X).reductionEvaluation n).inv.app K)) ∧
    ∀ (K : DerivedCategory (scalarReductionSource l E X)),
      finiteTorConstructibleIntegral l E X K →
      IsIso ((wholeProjection l E f o model).app K) ∧
      IsNormalizedCoefficientSequence l E Y
        ((ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) f).obj
            ((IntegralSystemRealization.calculus l E X).reduction.obj K)) := by
  sorry

end WeilConjectures
