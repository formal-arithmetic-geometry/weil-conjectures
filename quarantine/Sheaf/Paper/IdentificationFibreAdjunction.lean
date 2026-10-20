/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Paper.PointFibreDerivedTensor
import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-! # Point-fibre transport of the pairing adjunction

Source: Weil blueprint, main-20261015, `sk-thm-sf-identification.proof.md`,
second sentence (blueprint: lem-sf-identification-fibre-adjunction).

The four concrete instances below use exactly the recorded completed, localized,
and common-stage tensor comparisons. Internal Hom is specified by its defining
left-tensor adjunction; thus any presentation of that right adjoint is allowed.
The evaluation equation uniquely specifies the comparison with coefficient Hom.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u c a d vc va vd

open CategoryTheory CategoryTheory.MonoidalCategory

namespace WeilConjectures

/-- The pairing-adjunction equation for a recorded point tensor comparison.
The right adjoint `Closed P` presents the derived internal Hom, uniquely up to its
counit-preserving isomorphism. In this presentation `Phi` is `curry b`. The displayed
hypothesis on `alpha` is precisely preservation of evaluation, not an arbitrary
identification of dual objects. `muIso.hom` is the inverse of the node's `t`, and
`epsilonIso.inv` is its `u`.
Source: blueprint identification proof, second sentence
(blueprint: lem-sf-identification-fibre-adjunction). -/
def PointPairingAdjunctionTransport
    {C : Type c} {A : Type a} {B : Type d}
    [Category.{vc} C] [Category.{va} A] [Category.{vd} B]
    [MonoidalCategory B] [MonoidalClosed B] {beta : BraidedCategory B}
    {I : C ⥤ A} {F : A ⥤ B} {T : C × C ⥤ A} {unit : A}
    (S : PointFibreDerivedTensorComparisonData I F T unit beta) : Prop :=
  letI := S.monoidal
  letI := S.strong
  ∀ (P : C) [Closed P] (Q : C) (b : P ⊗ Q ⟶ 𝟙_ C)
    (alpha : (I ⋙ F).obj ((ihom P).obj (𝟙_ C)) ≅
      (ihom ((I ⋙ F).obj P)).obj (𝟙_ B)),
    ((I ⋙ F).obj P ◁ alpha.hom) ≫ (ihom.ev ((I ⋙ F).obj P)).app (𝟙_ B) =
      (Functor.Monoidal.μIso (I ⋙ F) P ((ihom P).obj (𝟙_ C))).hom ≫
        (I ⋙ F).map ((ihom.ev P).app (𝟙_ C)) ≫
        (Functor.Monoidal.εIso (I ⋙ F)).inv →
    MonoidalClosed.curry
      ((Functor.Monoidal.μIso (I ⋙ F) P Q).hom ≫ (I ⋙ F).map b ≫
        (Functor.Monoidal.εIso (I ⋙ F)).inv) =
      (I ⋙ F).map (MonoidalClosed.curry b) ≫ alpha.hom

/-- Point fibre sends the adjoint of any point pairing to the coefficient adjoint,
through the evaluation-preserving comparison. All four coefficient stages are
included, using the canonical coherent tensor system, rather than a freely chosen
monoidal functor. A finite level is indexed by `m`, meaning exponent `m + 1`.
Source: blueprint main-20261015, `sk-thm-sf-identification.proof.md`, second sentence
(blueprint: lem-sf-identification-fibre-adjunction).

Proof:
1. Write `Phi = curry b`. The source evaluation law gives
   `b = (P ◁ Phi) ≫ ev_s`. Apply the point functor and use its tensorator's
   naturality in the second variable (lem-sf-point-fibre-derived-tensor).
   The transported pairing is consequently `(FP ◁ F(Phi))` followed by
   `muIso.hom ≫ F(ev_s) ≫ epsilonIso.inv`.
2. Substitute the evaluation-preserving equation for `alpha`. Bifunctoriality
   rewrites this as `(FP ◁ (F(Phi) ≫ alpha.hom)) ≫ ev_Lambda`.
3. By the evaluation formula of lem-pod-closed-uncurry-laws this is the uncurry
   of `F(Phi) ≫ alpha.hom`. The same node's uncurry-curry cancellation and
   injectivity of uncurry identify the coefficient curry with that composite.
The argument applies to the actual finite, completed integral, localized rational,
and common finite-stage algebraically closed comparisons without any change. -/
theorem identificationFibreAdjunction
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Omega : Type u) [Field Omega] [Algebra ℚ_[l] Omega] [IsAlgClosure ℚ_[l] Omega]
    (S : PointFibreDerivedTensorSystem D l hl Omega)
    (_canonical : PointFibreDerivedTensorCanonical D l hl Omega S) :
    (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
      (m : ℕ), PointPairingAdjunctionTransport (S.finite E m)) ∧
    (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      PointPairingAdjunctionTransport (S.integral E)) ∧
    (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      PointPairingAdjunctionTransport (S.rational E)) ∧
    PointPairingAdjunctionTransport S.qbar := by
  sorry

end WeilConjectures
