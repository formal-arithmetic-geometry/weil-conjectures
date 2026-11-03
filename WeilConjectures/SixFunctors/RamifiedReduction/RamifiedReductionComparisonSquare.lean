/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData

/-! # The mixed ramified extension and quotient reduction square

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-free-extension.proof.md, paragraph 3
(blueprint: lem-sf-ramified-reduction-comparison-square).

The canonical maps are reused from the published finite coefficient calculus.
All reassociations use the balanced scalar compositor, including on the pro-etale site.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.FiniteCoefficientAdjoints
open WeilConjectures.FiniteFreeCoefficients
open WeilConjectures.FiniteFreeCoefficients.Sites
open scoped CategoryTheory.Functor
namespace WeilConjectures.RamifiedReduction

variable {l : ℕ} [Fact l.Prime] {E : Type (u + 1)} [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The upper field at the base-uniformizer exponent n; its ring is B_n.
Source: blueprint main-20261015, lem-coef-finite-free-extension.proof.md, paragraph 3.
(blueprint: lem-sf-ramified-reduction-comparison-square). -/
def level {L : Type (u + 1)} [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L) (n : ℕ+) : Stage l E where
  field := L
  inclusion := ι
  exponent := n

/-- The vertical quotient is induced by the identity of the coefficient field.
Source: blueprint main-20261015, lem-coef-finite-free-extension.proof.md, paragraph 3.
(blueprint: lem-sf-ramified-reduction-comparison-square). -/
def reduction (s : Stage l E) (m : ℕ+) (h : (m : ℕ) ≤ (s.exponent : ℕ)) :
    Arrow s { s with exponent := m } where
  embedding := AlgHom.id (Padic l) s.field
  over_base := rfl
  level := h

/-- Dispatch to the compact-support counit transpose or its specified site transport.
Source: blueprint main-20261015, lem-coef-finite-free-extension.proof.md, paragraph 3.
(blueprint: lem-sf-ramified-reduction-comparison-square). -/
def omegaArrow (pro : Bool) {s t : Stage l E} (a : Arrow s t)
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f) :
    (scalar pro a.ringMap X).obj (omega pro s.ring c) ⟶ omega pro t.ring c := by
  cases pro
  · exact FiniteFreeCoefficients.omegaMap a.ringMap c
  · exact proOmegaMap a.ringMap c

/-- Evaluation and its signed double-dual transpose for the specified coefficient arrow.
Source: blueprint main-20261015, lem-coef-finite-free-extension.proof.md, paragraph 3.
(blueprint: lem-sf-ramified-reduction-comparison-square). -/
def Pairings (pro : Bool) {s t : Stage l E} (a : Arrow s t)
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f)
    (μ : TensorComparison pro a.ringMap X)
    (σs : tensor pro s.ring X ≅ (tensor pro s.ring X).flip)
    (σt : tensor pro t.ring X ≅ (tensor pro t.ring X).flip) : Prop :=
  ∀ K : D pro s.ring X, Sites.Ctf pro s.ring X K →
    (((tensor pro t.ring X).map (Sites.dualMap pro a.ringMap c μ
        (omegaArrow pro a c) K)).app ((scalar pro a.ringMap X).obj K) ≫
      evaluation pro t.ring X σt (omega pro t.ring c)
        ((scalar pro a.ringMap X).obj K) =
      μ.inv.app ((Sites.dual pro s.ring c).obj (op K), K) ≫
        (scalar pro a.ringMap X).map
          (evaluation pro s.ring X σs (omega pro s.ring c) K) ≫ omegaArrow pro a c) ∧
    ((scalar pro a.ringMap X).map
        (bidual pro s.ring X σs (omega pro s.ring c) K) ≫
      Sites.dualMap pro a.ringMap c μ (omegaArrow pro a c)
        ((Sites.dual pro s.ring c).obj (op K)) =
      bidual pro t.ring X σt (omega pro t.ring c) ((scalar pro a.ringMap X).obj K) ≫
        (Sites.dual pro t.ring c).map
          (Sites.dualMap pro a.ringMap c μ (omegaArrow pro a c) K).op)

end WeilConjectures.RamifiedReduction
