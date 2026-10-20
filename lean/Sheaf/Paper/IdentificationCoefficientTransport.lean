/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.Paper.SixFunctorDatum
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.ExchangeFunctoriality

import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.SixFunctors.IntegralOpenReductionComparison
import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
import Sheaf.SixFunctors.AmbientProperOpenPasting
import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients

/-! # Identity-point coefficient transport

Source: blueprint main-20261015, `sk-thm-sf-identification.proof.md`, normalized
trace at the point; `fix-lem-exchanges`, clauses (2) and (4)
(blueprint: lem-sf-identification-coefficient-transport).

## Main declarations

- `sfIdentityComposition`: the datum's specified compositor with the identity.
- `sfIdentityNormalizedCounit`: the identity-normalized counit nu.
- `sfIdentityTransportMate`: the conjugate of the inverse compositor.
- `SfIdentityStageLaws`: the displayed equations at one coefficient stage.
- `SfIdentityChange`: transport through the specified coefficient comparisons.
- `sfFiniteIdentityComparison`: the finite identity-compactification comparison.
- `identificationCoefficientTransport`: normalization at all four coefficient stages.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w v₁ w₁
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

/-- The canonical identity compactification at the geometric point.
Source: the identity compactification in the node's first paragraph
(blueprint: lem-sf-identification-coefficient-transport). -/
def sfPointIdentityCompactification (D : FiniteFieldDatum.{u}) :
    Compactification (𝟙 (Spec.{u} (.of D.k))) :=
  Compactification.ofIsProper (𝟙 (Spec.{u} (.of D.k)))

/-- Equality transport of a compactified support functor.
Source: coherent identifications in thm-sf-comp-composition
(blueprint: lem-sf-identification-coefficient-transport). -/
def sfSupportEquality {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) {X Y : SixFunctorSpace D}
    (f g : X ⟶ Y) (h : f = g) (c : Compactification f.hom.left) :
    S.support g (h ▸ c) ≅ S.support f c := by
  subst g
  exact Iso.refl _

/-- The specified support compositor with the identity composite transported to a.
Source: thm-sf-comp-composition and fix-lem-exchanges (2),(4)
(blueprint: lem-sf-identification-coefficient-transport). -/
def sfIdentityComposition {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (X : SixFunctorSpace D)
    (c : Compactification (sixFunctorStructure X).hom.left) :
    S.support (sixFunctorStructure X) c ⋙
      S.support (𝟙 (sixFunctorPoint D)) (sfPointIdentityCompactification D) ≅
        S.support (sixFunctorStructure X) c :=
  (S.composition (sixFunctorStructure X) (𝟙 (sixFunctorPoint D)) c
    (sfPointIdentityCompactification D)
    ((Category.comp_id (sixFunctorStructure X)).symm ▸ c)).symm ≪≫
      sfSupportEquality S (sixFunctorStructure X)
        (sixFunctorStructure X ≫ 𝟙 (sixFunctorPoint D))
        (Category.comp_id (sixFunctorStructure X)).symm c

/-- The identity-normalized counit, e composed with the inverse of v at J L.
Source: the displayed definition of nu
(blueprint: lem-sf-identification-coefficient-transport). -/
def sfIdentityNormalizedCounit {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (L : B (sixFunctorPoint D))
    (v : S.support (𝟙 (sixFunctorPoint D)) (sfPointIdentityCompactification D) ≅ 𝟭 _) :=
  v.inv.app ((S.exceptional (𝟙 (sixFunctorPoint D))
    (sfPointIdentityCompactification D)).obj L) ≫
      (S.exceptionalAdjunction (𝟙 (sixFunctorPoint D))
        (sfPointIdentityCompactification D)).counit.app L

/-- The inverse right mate, using the pasted composite adjunction and alpha inverse.
Source: the definition of c and the conjugation convention
(blueprint: lem-sf-identification-coefficient-transport). -/
def sfIdentityTransportMate {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (X : SixFunctorSpace D)
    (c : Compactification (sixFunctorStructure X).hom.left) :=
  conjugateIsoEquiv
    ((S.exceptionalAdjunction (sixFunctorStructure X) c).comp
      (S.exceptionalAdjunction (𝟙 (sixFunctorPoint D))
        (sfPointIdentityCompactification D)))
    (S.exceptionalAdjunction (sixFunctorStructure X) c)
    (sfIdentityComposition S X c).symm

/-- The compositor normalization and the three conclusions at one coefficient stage.
The counit equation is an equality of actual morphisms.
Source: the two displayed equations and isomorphism clauses
(blueprint: lem-sf-identification-coefficient-transport). -/
structure SfIdentityStageLaws {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (P : ∀ X, B X → Prop)
    (L : B (sixFunctorPoint D))
    (v : S.support (𝟙 (sixFunctorPoint D))
      (sfPointIdentityCompactification D) ≅ 𝟭 _) : Prop where
  composition_identity : ∀ (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (c : Compactification (sixFunctorStructure X).hom.left)
    (K : B X), P X K →
    (sfIdentityComposition S X c).hom.app K =
      v.hom.app ((S.support (sixFunctorStructure X) c).obj K)
  normalized_counit_iso : IsIso (sfIdentityNormalizedCounit S L v)
  mate_iso : ∀ (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left),
    IsIso ((sfIdentityTransportMate S X c).hom.app L)
  mate_is_normalized_counit : ∀ (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (c : Compactification (sixFunctorStructure X).hom.left),
    (sfIdentityTransportMate S X c).hom.app L =
      (S.exceptional (sixFunctorStructure X) c).map (sfIdentityNormalizedCounit S L v)
  counit_equation : ∀ (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left),
    (S.support (sixFunctorStructure X) c).map
        ((sfIdentityTransportMate S X c).hom.app L) ≫
      (S.exceptionalAdjunction (sixFunctorStructure X) c).counit.app L =
    (S.exceptionalAdjunction (sixFunctorStructure X) c).counit.app
        ((S.exceptional (𝟙 (sixFunctorPoint D)) (sfPointIdentityCompactification D)).obj L) ≫
      sfIdentityNormalizedCounit S L v

/-- Coefficient transport of the identity comparison through the supplied support square.
For integral reduction that square is normalized by the actual Roos projections; for
localization and common stages it is the specified scalar comparison.
Source: fix-lem-exchanges (2),(4), and reduction/limit unit projection normalization
(blueprint: lem-sf-identification-coefficient-transport). -/
def SfIdentityChange {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {B₁ : SixFunctorSpace D → Type v₁} [∀ X, Category.{w₁} (B₁ X)]
    {S : SixFunctorPushStage D B} {S₁ : SixFunctorPushStage D B₁}
    {F : ∀ X, B X ⥤ B₁ X} (Q : SixFunctorCoefficientComparison S S₁ F)
    (v : S.support (𝟙 (sixFunctorPoint D)) (sfPointIdentityCompactification D) ≅ 𝟭 _)
    (v₁ : S₁.support (𝟙 (sixFunctorPoint D)) (sfPointIdentityCompactification D) ≅ 𝟭 _) :
    Prop :=
  ∀ K : B (sixFunctorPoint D),
    (Q.supportAdjunction (𝟙 (sixFunctorPoint D))
        (sfPointIdentityCompactification D)).left.hom.app K ≫
      v₁.hom.app ((F (sixFunctorPoint D)).obj K) =
    (F (sixFunctorPoint D)).map (v.hom.app K)

/-- The finite identity comparison is the identity compactification, proper direct-image
identification, and the canonical direct-image identity, lifted through the full inclusion.
Source: finite identity compactification in thm-sf-comp-composition
(blueprint: lem-sf-identification-coefficient-transport). -/
def sfFiniteIdentityComparison
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorFiniteOperations D C E n hn) :
    (@SixFunctorPushStage.support.{u, u+2, u+2} D
      (sixFunctorFiniteCategory D C E n hn)
      (fun X ↦ inferInstanceAs (Category.{u+2} (sixFunctorFiniteCategory D C E n hn X)))
      S.finite) (𝟙 (sixFunctorPoint D)) (sfPointIdentityCompactification D) ≅
        Functor.id.{u+2, u+2} (sixFunctorFiniteCategory D C E n hn (sixFunctorPoint D)) :=
  ((intrinsicFiniteTorsionConstructible C.l E n hn
      (Spec (.of D.k))).fullyFaithfulι.{u+2, u+2}.whiskeringRight _).preimageIso
    (Functor.isoWhiskerRight
        (@SixFunctorPushStage.properIdentity.{u, u+2, u+2} D
          (sixFunctorFiniteCategory D C E n hn)
          (fun X ↦ inferInstanceAs (Category.{u+2} (sixFunctorFiniteCategory D C E n hn X)))
          S.finite _ _ (𝟙 (sixFunctorPoint D)) inferInstance)
        (intrinsicFiniteTorsionConstructible C.l E n hn (Spec (.of D.k))).ι ≪≫
      S.finiteDirectImage (𝟙 (sixFunctorPoint D)) ≪≫
      Functor.isoWhiskerLeft _
        (@sixFunctorDirectIdentity (Padic.coefficientExtensionRing C.l E n) _
          (Padic.finite_coefficientExtensionRing C.l E n hn) (Spec (.of D.k))) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

/-- The coefficient-stage transport statement, including finite, completed integral,
rational and common finite-stage coefficients.
Source: blueprint main-20261015, `sk-thm-sf-identification.proof.md`, normalized trace
(blueprint: lem-sf-identification-coefficient-transport).

Proof:
1. The identity clause of thm-sf-comp-composition computes the finite compositor.
   Integrally, the identity compactification is reduction followed by total limit.
   The identity-open case of lem-sf-integral-open-reduction-comparison fixes its
   comparison as the inverse actual unit of lem-coef-derived-system-evaluation-calculus.
   The reduction equations below characterize this same inverse on the point category;
   they use the datum's projection-normalized reduction comparisons.
2. Write a = p j and apply lem-sf-integral-compactification-comparison-bridge to
   the strict semilinear system S_p J_j of finite reductions. The finite-Tor bounds,
   compatible origins and A5 put it in the domain of
   lem-sf-integral-compactification-system-realization. Retain the identity outer
   compactification and the same compactification for the composite.
3. By lem-sf-ambient-proper-open-pasting its system proper/open comparison is identity.
   The bridge identifies the specified completed compositor of fix-lem-exchanges (2),(4)
   with C L(e_N) L R(C inverse). Naturality of the actual reconstruction unit u and
   the triangle L(e_N) u_(L N) = 1 give alpha u = 1, hence alpha = u inverse.
4. Apply raw scalar localization, whose morphisms are fractions, to this equality.
   Naturality holds on numerators and denominators. At algebraically closed coefficients,
   represent all objects and arrows at one common finite coefficient field and pass
   the equality through the supplied A5 coefficient comparisons.
5. Conjugate v inverse for I adjoint to J and the identity adjunction. The component
   formula of def-weil-pbc-adjunction-conjugate is e_L v_(J L) inverse, so nu is invertible.
6. For F adjoint to G, the composite adjunction counit is e_L I(mu_(J L)), as in
   def-weil-pbc-composite-adjunction. Substitute alpha = v F into its conjugate formula.
   Naturality of v inverse moves it past mu; the F-G triangle cancels the remaining
   unit and counit. The result is c_L = G(e_L v_(J L) inverse), giving c = G(nu)
   and invertibility of c.
7. Naturality of the exceptional counit at nu gives the displayed counit equation. -/
theorem identificationCoefficientTransport
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorDatum D C E n hn) :
    (@SfIdentityStageLaws.{u, u+2, u+2} D
      (sixFunctorFiniteCategory D C E n hn)
      (fun X ↦ inferInstanceAs (Category.{u+2} (sixFunctorFiniteCategory D C E n hn X)))
      S.finite S.toSixFunctorOperationDatum.finiteTorDomain
      (@SixFunctorDualityData.unit.{u, u+2, u+2} D
        (sixFunctorFiniteCategory D C E n hn)
        (fun X ↦ inferInstanceAs (Category.{u+2} (sixFunctorFiniteCategory D C E n hn X)))
        S.finite (sixFunctorFiniteHomPairs D C E n hn) S.finiteDuality)
      (sfFiniteIdentityComparison D C E n hn S.toSixFunctorFiniteOperations)) ∧
    (∃ vI : S.higher.integral.support (𝟙 (sixFunctorPoint D))
        (sfPointIdentityCompactification D) ≅ 𝟭 _,
      SfIdentityStageLaws S.higher.integral
        S.toSixFunctorOperationDatum.integralFiniteTorDomain
        S.higher.integralDuality.unit vI ∧
    ∃ vR : S.higher.rational.support (𝟙 (sixFunctorPoint D))
        (sfPointIdentityCompactification D) ≅ 𝟭 _,
      SfIdentityStageLaws S.higher.rational (fun _ ↦ ⊤)
        S.higher.rationalDuality.unit vR ∧
      SfIdentityChange S.higher.rationalization vI vR ∧
      (∀ m : ℕ, @SfIdentityChange.{u, u+2, u+2, u+2, u+2} D
        (fun X ↦ sfIntegralConstructibleCategory C.l E X.obj.left)
        (fun X ↦ inferInstanceAs (Category.{u+2}
          (sfIntegralConstructibleCategory C.l E X.obj.left)))
        (sixFunctorFiniteCategory D C E (m+1) (Nat.succ_le_succ (Nat.zero_le m)))
        (fun X ↦ inferInstanceAs (Category.{u+2}
          (sixFunctorFiniteCategory D C E (m+1) (Nat.succ_le_succ (Nat.zero_le m)) X)))
        _ _ _ (S.integralNormalization.reduction m) vI
        (sfFiniteIdentityComparison D C E (m+1) (Nat.succ_le_succ (Nat.zero_le m))
          (S.integralNormalization.finiteLevels m))) ∧
    ∃ vQ : S.closure.commonStage.support (𝟙 (sixFunctorPoint D))
        (sfPointIdentityCompactification D) ≅ 𝟭 _,
      SfIdentityStageLaws S.closure.commonStage (fun _ ↦ ⊤)
        S.closure.commonStageDuality.unit vQ ∧
    ∀ L : Padic.FiniteCoefficientFields C.l C.Qbar,
      ∃ vLI : (S.closure.coefficientStages L).integral.support
          (𝟙 (sixFunctorPoint D)) (sfPointIdentityCompactification D) ≅ 𝟭 _,
      ∃ vLR : (S.closure.coefficientStages L).rational.support
          (𝟙 (sixFunctorPoint D)) (sfPointIdentityCompactification D) ≅ 𝟭 _,
      SfIdentityStageLaws (S.closure.coefficientStages L).integral
          (fun X K ↦ finiteTorConstructibleIntegral C.l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L) X.obj.left K.obj)
          (S.closure.coefficientStages L).integralDuality.unit vLI ∧
      SfIdentityStageLaws (S.closure.coefficientStages L).rational (fun _ ↦ ⊤)
          (S.closure.coefficientStages L).rationalDuality.unit vLR ∧
      SfIdentityChange (S.closure.coefficientStages L).rationalization vLI vLR ∧
      SfIdentityChange (S.closure.commonStageComparison L) vLR vQ ∧
      ∀ m : ℕ, @SfIdentityChange.{u, u+2, u+2, u+2, u+2} D
        (fun X ↦ sfIntegralConstructibleCategory C.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L) X.obj.left)
        (fun X ↦ inferInstanceAs (Category.{u+2} (sfIntegralConstructibleCategory C.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L) X.obj.left)))
        (sixFunctorFiniteCategory D C
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L)
          (m+1) (Nat.succ_le_succ (Nat.zero_le m)))
        (fun X ↦ inferInstanceAs (Category.{u+2} (sixFunctorFiniteCategory D C
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L)
          (m+1) (Nat.succ_le_succ (Nat.zero_le m)) X)))
        _ _ _ ((S.coefficientIntegralNormalization L).reduction m) vLI
        (sfFiniteIdentityComparison D C
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L)
          (m+1) (Nat.succ_le_succ (Nat.zero_le m))
          ((S.coefficientIntegralNormalization L).finiteLevels m))) := by
  sorry

end WeilConjectures
