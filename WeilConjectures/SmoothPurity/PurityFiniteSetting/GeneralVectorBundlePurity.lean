/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityBaseChange
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityDirectSum
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityFiniteReduction
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientTwistAnnihilator
public import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescentDefinitions

/-! # Vector-bundle purity over a general admissible field

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/cor-pur-vector-bundle-purity.md`, statement and
proof paragraphs (blueprint: cor-pur-vector-bundle-purity).

The theorem below records the current general-field interface.  Coefficients are
finite ordinary-etale modules over `A_{F,n} = ULift (Padic.coefficientExtensionRing ell E n)`,
the quotient `𝒪_F / ϖ_F^n`; the constructible finite-Tor category, integration trace,
Brown right adjoint, base-change equation, direct-sum equation, and finite-reduction
family along the canonical quotients `A_{F,n} → A_{F,m}` are the canonical declarations
already exposed by the supporting paper modules.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open WeilConjectures

namespace WeilConjectures.PurityFiniteSetting

/-- The general-field conclusion for vector-bundle purity.  The first conjunct
is the integration-normalized exceptional purity family; the next conjuncts
are its base-change and ordered direct-sum compatibilities.  The final
conjunct is the canonical finite quotient compatibility, including invertibility
on every finite constructible component.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/cor-pur-vector-bundle-purity.md`, statement
(blueprint: cor-pur-vector-bundle-purity). -/
def GeneralVectorBundlePurityConclusion
    (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) (_hn : 1 ≤ n)
    (B : Scheme.{u}) (hB : B ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType hB] [QuasiCompact hB]
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d] : Prop :=
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing ell E n)
  letI : Finite A := Equiv.ulift.finite_iff.mpr
    (Padic.finite_coefficientExtensionRing ell E n _hn)
  letI : IsNoetherian B := isNoetherian_of_locallyOfFiniteType hB
  letI : IsAffineHom (VectorBundleZeroSection.π B d F) :=
    (Etale.vectorIntegration_geometry B d F).1
  letI : LocallyOfFiniteType (VectorBundleZeroSection.π B d F) :=
    (Etale.vectorIntegration_geometry B d F).2.1
  ∃ c : Compactification (VectorBundleZeroSection.π B d F),
    letI := c.hasCompactification
    ∃ hA : ((ell ^ n : ℕ) : A) = 0,
      ∃ hN : IsUnit (ell : Γ(B, ⊤)),
        VectorPurityFunctorConclusion A (VectorBundleZeroSection.π B d F)
          (Etale.DerivedCategory.constructibleFiniteTor
            (ModuleCat.{u + 1} A) B)
          (Etale.vectorIntegrationCoefficient A (ell ^ n) hA B d F)
          (Etale.vectorBundleIntegration (ell ^ n)
            (Nat.pow_pos (Fact.out : ell.Prime).pos) A hA B
            (by simpa only [Nat.cast_pow] using hN.pow n) d F) ∧
        ∃ γ : VectorPurityGamma A (ell ^ n) hA B d F,
          VectorPurityGammaNormalized A (ell ^ n)
            (Nat.pow_pos (Fact.out : ell.Prime).pos) hA B
            (by simpa only [Nat.cast_pow] using hN.pow n) d F γ ∧
          (∀ K : (Etale.DerivedCategory.constructibleFiniteTor
            (ModuleCat.{u + 1} A) B).FullSubcategory, IsIso (γ.app K.obj)) ∧
          PurityBaseChangeEquation A (ell ^ n)
            (Nat.pow_pos (Fact.out : ell.Prime).pos) hA B
            (by simpa only [Nat.cast_pow] using hN.pow n) d F γ ∧
          PurityDirectSumEquation A (ell ^ n)
            (Nat.pow_pos (Fact.out : ell.Prime).pos) hA B
            (by simpa only [Nat.cast_pow] using hN.pow n) d F γ ∧
          ∀ (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n),
            let A' := ULift.{u + 1} (Padic.coefficientExtensionRing ell E m)
            letI : Finite (Padic.coefficientExtensionRing ell E m) :=
              Padic.finite_coefficientExtensionRing ell E m hm
            letI : Finite A' := inferInstanceAs (Finite A')
            let φ : A →+* A' := RingHom.ulift (Ideal.Quotient.factor
              (S := Padic.coefficientExtensionIdeal ell E n)
              (T := Padic.coefficientExtensionIdeal ell E m)
              (Ideal.pow_le_pow_right hmn))
            PurityScalarReductionEquation φ (ell ^ n)
              (Nat.pow_pos (Fact.out : ell.Prime).pos) hA B
              (by simpa only [Nat.cast_pow] using hN.pow n) d F γ

/-- Vector-bundle purity over any finite or algebraically closed field `k` with
`ell` different from the characteristic of `k`.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/cor-pur-vector-bundle-purity.md`, statement and
proof paragraphs 1-2 (blueprint: cor-pur-vector-bundle-purity).

Proof (postponed to stage 3), following the node's steps:
1. Put `A = A_{F,n}`, `N = ell^n`, `W = A_E(r)[2r]`; `N A = 0` since `ell = u ϖ_F^e`.
   Bundle frames make `E` and `B` Noetherian, separated and of finite type over `k`, and
   `N` is invertible on `B`.  Ordinary-etale vector-bundle purity gives the integration
   mate `γ_K = adj((1_K ⊗ t_π) P_K⁻¹)`, invertible for every complex; `α_K = γ_K⁻¹`.
2. The finite internal realization identifies the ctf categories over `k`; compact-support
   comparison and the specified Hom chain identify the realized etale counit with the
   counit of the constructible right adjoint, so `γ` is the asserted map and preserves
   the adjunction.
3. The geometric trace equation `g^* t_π = t_{π'} Rπ'_!(l) C_W`, tensored with `g^* K` by
   projection/exchange coherence and transposed, gives
   `e_K ∘ g'^* γ_K = γ_{π', g^* K} ∘ a_K`; hence `e_K` is invertible.
4. For `h = p q`, the ordered two-block trace equation, the projection/compositor
   identity and the composite-adjunction Hom bijection give the ordered direct-sum
   formula; the block sign `(-1)^{4rs}` is `1`.
5. For `1 ≤ m ≤ n`, scalar trace descent along `A_{F,n} → A_{F,m}` gives
   `t_m Rπ_{!,m}(l) q_W = u_B Q_B(t_n)` with `l` the balancing line map.
6. Scalar projection coherence and the mate of `q⁻¹` give
   `b_K Q_E(γ_{n,K}) = γ_{m, Q_B K} a_{scalar,K}`; both gamma maps and `a_scalar` are
   invertible, so `b_K` is, including at `K = A_B`; no flatness is used.
7. The transported counit and unit satisfy the triangle identities by naturality; at
   `K = A_B` this gives `ω_π ≅ A_E(r)[2r]`.  Rank zero uses the identity trace, and on
   an empty base all maps are unique. -/
theorem generalVectorBundlePurity
    (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    (_hk : Finite k ∨ IsAlgClosed k) (_hchar : ringChar k ≠ ell)
    (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) (hn : 1 ≤ n)
    (B : Scheme.{u}) (hB : B ⟶ Spec (CommRingCat.of k))
    [IsSeparated hB] [LocallyOfFiniteType hB] [QuasiCompact hB]
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    GeneralVectorBundlePurityConclusion ell E n hn B hB d F := by
  sorry

end WeilConjectures.PurityFiniteSetting
