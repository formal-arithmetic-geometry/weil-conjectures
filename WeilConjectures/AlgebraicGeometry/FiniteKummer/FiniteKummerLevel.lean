/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.FinitePositiveReduction.FiniteReductionPositiveLineComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistIntegralBasis

/-! # Finite Kummer level with native condensed coefficients

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
lem-pur-finite-kummer-level.md and lem-pur-finite-kummer-level.proof.md.
(blueprint: lem-pur-finite-kummer-level).
The coefficient rings and finite twist are the current pulled-back condensed constructions.
The comparison is the existing Kummer root-power map, with no choice of frame.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.FiniteKummer

/-- The specified Kummer comparison from exponent n+1 to exponent N+1.
Source: finite-level comparison and its root-power normalization
(blueprint: lem-pur-finite-kummer-level). -/
def comparison (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) (n N : ℕ) (h : N ≤ n) :
    coefficientFiniteTwistOne l E T n ⟶ coefficientFiniteRootLine l E T n N :=
  eqToHom (congrArg (coefficientFiniteRootLine l E T n)
    (Nat.add_sub_of_le h).symm) ≫ coefficientFiniteRootComparison l E T n N (n - N)

/-- Pullback of any root presentation with the fixed native finite coefficient ring.
The map is the free-module adjunct of the actual root pullback and then the module adjunct.
Source: root pullback and tensor naturality in the final sentence of the proof
(blueprint: lem-pur-finite-kummer-level). -/
def pull (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {X T : Scheme.{u}} (f : X ⟶ T) (n r : ℕ) :
    (CondensedRing.upperStar (twistFiniteRing l E n) f).obj
      (coefficientFiniteRootLine l E T n r) ⟶ coefficientFiniteRootLine l E X n r :=
  ((CondensedRing.upperStarLowerStarAdjunction (twistFiniteRing l E n) f).homEquiv
    (coefficientFiniteRootLine l E T n r) (coefficientFiniteRootLine l E X n r)).symm
    (((Mod.freeForgetAdjunction (condensedRingObj (twistFiniteRing l E n) T)).homEquiv
      (rootsOfUnitySheaf T (l ^ (r + 1)))
      ((CondensedRing.lowerStar (twistFiniteRing l E n) f).obj
        (coefficientFiniteRootLine l E X n r))).symm
      (FinitePositiveReduction.rootsDirect T f (l ^ (r + 1)) ≫
        (ProEtale.lowerStar Ab.{u + 1} f).map
          ((Mod.freeForgetAdjunction (condensedRingObj (twistFiniteRing l E n) X)).unit.app
            (rootsOfUnitySheaf X (l ^ (r + 1))))))

end AlgebraicGeometry.ProEtale.FiniteKummer

namespace WeilConjectures.PurityFiniteSetting

open AlgebraicGeometry.ProEtale.FiniteKummer

/-- The arithmetic level and canonical finite Kummer isomorphism, with derived tensor and
arbitrary base change compatibility.

Source: latest blueprint `lem-pur-finite-kummer-level`, statement and companion proof.
Proof (blueprint steps 1--6):
(1) In the DVR write l = u*pi_E^e with u a unit. Applying the normalized valuation gives
v_l(pi_E)=1/e. Since the divisibility hypothesis gives n=e*N, positivity gives N≥1 and
(pi_E^n)=(l^N); moreover l^j belongs to (pi_E^n) exactly when e*j≥n, proving minimality.
(2) Choose an integral basis of size d. Reduction modulo l^N gives A ≅ (Z/l^N)^d.
At N=1, cardinalities of the residue quotient and the maximal-ideal filtration give
d=e*f, hence the displayed finite-free additive presentation and its scalar equation.
(3) Put R=Z_l,T, L=Z_l(1)_T and Q_N=(Z/l^N)_T. Compatible integral root and
residue bases identify the root tower with the coefficient tower. The level-N projection is
locally onto; its kernel is l^N L and its image is mu_(l^N), giving
0 -> L ->[l^N] L ->[p_N] mu_(l^N) -> 0.
(4) Tensor this cokernel sequence with A_T. Tensor preserves cokernels and l^N A=0,
so balancing over R and then Q_N gives L tensor_R A_T ≅ mu_(l^N) tensor_Q_N A_T,
with x tensor a mapped to p_N(x) tensor a. This is the canonical comparison implemented
by `comparison`; the native free-module adjunction defines its pullback map.
(5) For every derived object K, tensor a K-flat representative with the degree-zero
comparison. It is an isomorphism in every degree, yielding the displayed natural
unbounded-derived-tensor compatibility.
(6) For h:T' -> T, root pullback commutes with every power transition. Thus the pullback
map satisfies p_N,T' c_L = c_N h* p_N,T. Tensor pullback carries pure tensors to pure
tensors, so both routes in the displayed base-change square agree; local lifts and
sheafification give equality for every morphism, including identities and empty schemes.
-/
theorem finiteKummerLevel_condensed (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) :
    1 ≤ P.kummerLevel ∧
    P.level = P.ramificationIndex * P.kummerLevel ∧
    (-Real.log (Padic.coefficientExtensionAbsoluteValue P.coefficients.l P.extension
      (P.coefficients.l : P.extension)) / Real.log P.coefficients.l = 1) ∧
    (-Real.log (Padic.coefficientExtensionAbsoluteValue P.coefficients.l P.extension
      (Padic.coefficientExtensionUniformizer P.coefficients.l P.extension).val) /
        Real.log P.coefficients.l = (P.ramificationIndex : ℝ)⁻¹) ∧
    (P.level : ℝ) *
      (-Real.log (Padic.coefficientExtensionAbsoluteValue P.coefficients.l P.extension
        (Padic.coefficientExtensionUniformizer P.coefficients.l P.extension).val) /
          Real.log P.coefficients.l) = P.kummerLevel ∧
    Padic.coefficientExtensionIdeal P.coefficients.l P.extension P.level =
      Ideal.span ({(P.exponent : Padic.coefficientExtensionIntegers
        P.coefficients.l P.extension)} : Set (Padic.coefficientExtensionIntegers
          P.coefficients.l P.extension)) ∧
    (∃ r : P.Ring ≃+* (Padic.coefficientExtensionIntegers P.coefficients.l P.extension ⧸
        Ideal.span ({(P.exponent : Padic.coefficientExtensionIntegers
          P.coefficients.l P.extension)} : Set (Padic.coefficientExtensionIntegers
            P.coefficients.l P.extension))),
      ∀ x : Padic.coefficientExtensionIntegers P.coefficients.l P.extension,
        r (Ideal.Quotient.mk
          (Padic.coefficientExtensionIdeal P.coefficients.l P.extension P.level) x) =
        Ideal.Quotient.mk (Ideal.span ({(P.exponent : Padic.coefficientExtensionIntegers
          P.coefficients.l P.extension)} : Set (Padic.coefficientExtensionIntegers
            P.coefficients.l P.extension))) x) ∧
    (P.exponent : P.Ring) = 0 ∧
    (∀ j : ℕ, ((P.coefficients.l ^ j : ℕ) : P.Ring) = 0 → P.kummerLevel ≤ j) ∧
    ∀ n : ℕ, P.level = n + 1 →
      ∃ N : ℕ, P.kummerLevel = N + 1 ∧
        ∃ a : ZMod (P.coefficients.l ^ (N + 1)) →+*
            Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1),
          ∃ f : ℕ,
            Nat.card (Padic.coefficientExtensionResidueField P.coefficients.l P.extension) =
              P.coefficients.l ^ f ∧
            (∃ b : Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1) ≃+
                (Fin (P.ramificationIndex * f) → ZMod (P.coefficients.l ^ (N + 1))),
              ∀ (z : ZMod (P.coefficients.l ^ (N + 1)))
                (x : Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)),
                b (a z * x) = z • b x) ∧
            ∃ hNn : N ≤ n,
              (∀ (T : Scheme.{u})
                (_hT : ∀ x : T, IsUnit (P.coefficients.l : T.presheaf.stalk x)),
                IsIso (comparison P.coefficients.l P.extension T n N hNn) ∧
                ∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
                    (condensedRingObj (twistFiniteRing P.coefficients.l P.extension n) T)),
                  IsIso (((CondensedRing.derivedTensor
                    (twistFiniteRing P.coefficients.l P.extension n) T).obj K).map
                      ((DerivedCategory.singleFunctor _ 0).map
                        (comparison P.coefficients.l P.extension T n N hNn)))) ∧
              (∀ (T X : Scheme.{u}) (f : X ⟶ T)
                (_hT : ∀ x : T, IsUnit (P.coefficients.l : T.presheaf.stalk x))
                (_hX : ∀ x : X, IsUnit (P.coefficients.l : X.presheaf.stalk x)),
                (CondensedRing.upperStar
                  (twistFiniteRing P.coefficients.l P.extension n) f).map
                    (comparison P.coefficients.l P.extension T n N hNn) ≫
                      pull P.coefficients.l P.extension f n N =
                  pull P.coefficients.l P.extension f n n ≫
                    comparison P.coefficients.l P.extension X n N hNn) := by
  sorry

end WeilConjectures.PurityFiniteSetting
