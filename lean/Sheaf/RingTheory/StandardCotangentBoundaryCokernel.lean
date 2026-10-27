/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basic

/-!
# The degree-minus-one standard cotangent boundary cokernel

Source: Stacks Project, Cotangent Complex, Tags 08UP (remark-explicit-comparison-map)
and 08RB (lemma-relation-with-naive-cotangent-complex), explicit low-degree calculation
(blueprint: lem-trf-standard-cotangent-boundary-cokernel).

All polynomial rings and differential modules below are Mathlib constructions.
The tensor factors are written in the equivalent order `B ⊗ Ω`. The extension
cotangent is the actual kernel modulo its square, with the canonical `B`-action.
The boundary is constructed from the polynomial differential basis, rather than
supplied as an unspecified map. The final equivalence is pinned by its composite
with the quotient map and by its inverse on every conormal class.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open TensorProduct

namespace Algebra.StandardCotangentBoundary

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]

/-- Evaluation `ε : A[B] → B`. Source: Stacks, Tag 08UP
(blueprint: lem-trf-standard-cotangent-boundary-cokernel). -/
def epsilon : MvPolynomial B A →ₐ[A] B :=
  MvPolynomial.aeval (fun b : B ↦ b)

/-- The face `d₀(Y_p) = p`. Source: Stacks, Tag 08UP
(blueprint: lem-trf-standard-cotangent-boundary-cokernel). -/
def faceZero : MvPolynomial (MvPolynomial B A) A →ₐ[A] MvPolynomial B A :=
  MvPolynomial.aeval (fun p : MvPolynomial B A ↦ p)

/-- The face `d₁(Y_p) = X_{ε(p)}`. Source: Stacks, Tag 08UP
(blueprint: lem-trf-standard-cotangent-boundary-cokernel). -/
def faceOne : MvPolynomial (MvPolynomial B A) A →ₐ[A] MvPolynomial B A :=
  MvPolynomial.aeval (fun p : MvPolynomial B A ↦ MvPolynomial.X (epsilon A B p))

/-- The explicit section of the first polynomial augmentation.
Source: Stacks, Tag 08UP
(blueprint: lem-trf-standard-cotangent-boundary-cokernel).

Proof: Evaluating `Y_{X_b}` gives `ε(X_b) = b`, by the variable evaluation
identity twice (def-weil-pbc-mv-polynomial-ring). -/
theorem augmentationOne_section (b : B) :
    MvPolynomial.aeval (R := A) (epsilon A B) (MvPolynomial.X (MvPolynomial.X b)) = b := by
  sorry

/-- The augmentation of `Q₁ = A[A[B]]`, with the explicit section `b ↦ Y_{X_b}`.
Source: Stacks, Tag 08UP
(blueprint: lem-trf-standard-cotangent-boundary-cokernel). -/
def generatorsOne : Generators A B (MvPolynomial B A) where
  val := epsilon A B
  σ' b := MvPolynomial.X (MvPolynomial.X b)
  aeval_val_σ' := augmentationOne_section A B

/-- The explicit section of the second polynomial augmentation.
Source: Stacks, Tag 08UP
(blueprint: lem-trf-standard-cotangent-boundary-cokernel).

Proof: Evaluating `Z_{Y_{X_b}}` gives `ε(d₀(Y_{X_b})) = ε(X_b) = b`, by
three variable evaluations (def-weil-pbc-mv-polynomial-ring). -/
theorem augmentationTwo_section (b : B) :
    MvPolynomial.aeval (R := A) (fun f : MvPolynomial (MvPolynomial B A) A ↦
      epsilon A B (faceZero A B f))
      (MvPolynomial.X (MvPolynomial.X (MvPolynomial.X b))) = b := by
  sorry

/-- The augmentation of `Q₂ = A[Q₁]` sends `Z_f` to `ε(d₀f)`, with section
`b ↦ Z_{Y_{X_b}}`. Source: Stacks, Tag 08UP
(blueprint: lem-trf-standard-cotangent-boundary-cokernel). -/
def generatorsTwo : Generators A B (MvPolynomial (MvPolynomial B A) A) where
  val f := epsilon A B (faceZero A B f)
  σ' b := MvPolynomial.X (MvPolynomial.X (MvPolynomial.X b))
  aeval_val_σ' := augmentationTwo_section A B

/-- The actual module `M₁ = B ⊗_{Q₁} Ω[Q₁/A]`. Source: Stacks, Tag 08UP
(blueprint: lem-trf-standard-cotangent-boundary-cokernel). -/
abbrev ModuleOne := (generatorsOne A B).toExtension.CotangentSpace

/-- The actual module `M₂ = B ⊗_{Q₂} Ω[Q₂/A]`. Source: Stacks, Tag 08UP
(blueprint: lem-trf-standard-cotangent-boundary-cokernel). -/
abbrev ModuleTwo := (generatorsTwo A B).toExtension.CotangentSpace

/-- The tensor `b ⊗ df` in `M₁`. Source: Stacks, Tag 08UP
(blueprint: lem-trf-standard-cotangent-boundary-cokernel). -/
def differentialTensor (b : B) (f : MvPolynomial (MvPolynomial B A) A) : ModuleOne A B :=
  b ⊗ₜ[(generatorsOne A B).toExtension.Ring]
    KaehlerDifferential.D A (generatorsOne A B).toExtension.Ring f

/-- The alternating second boundary, defined on the basis `1 ⊗ dZ_f` by
`1 ⊗ df - 1 ⊗ dY_{d₀f} + 1 ⊗ dY_{d₁f}`. Source: Stacks, Tag 08UP
(blueprint: lem-trf-standard-cotangent-boundary-cokernel). -/
def boundary : ModuleTwo A B →ₗ[B] ModuleOne A B :=
  (generatorsTwo A B).cotangentSpaceBasis.constr B (fun f ↦
    differentialTensor A B 1 f -
      (generatorsOne A B).cotangentSpaceBasis (faceZero A B f) +
      (generatorsOne A B).cotangentSpaceBasis (faceOne A B f))

/-- The actual cokernel `E = M₁ / im ∂₂`. Source: Stacks, Tags 08UP and 08RB
(blueprint: lem-trf-standard-cotangent-boundary-cokernel). -/
abbrev Cokernel := ModuleOne A B ⧸ LinearMap.range (boundary A B)

/-- The symbol `t_p`, the quotient class of `1 ⊗ dY_p`. Source: Stacks, Tag 08UP
(blueprint: lem-trf-standard-cotangent-boundary-cokernel). -/
def symbol (p : MvPolynomial B A) : Cokernel A B :=
  (LinearMap.range (boundary A B)).mkQ ((generatorsOne A B).cotangentSpaceBasis p)

/-- The polynomial augmentation ideal `I = ker ε`. Source: Stacks, Tag 08UP
(blueprint: lem-trf-standard-cotangent-boundary-cokernel). -/
abbrev augmentationIdeal := (Generators.self A B).toExtension.ker

/-- The face difference belongs to `I`. Source: Stacks, Tag 08UP
(blueprint: lem-trf-standard-cotangent-boundary-cokernel).

Proof: Both composites `ε ∘ d₀` and `ε ∘ d₁` send `Y_p` to `ε(p)` and
agree on coefficients. Polynomial evaluation uniqueness makes them equal.
Consequently evaluation kills their difference, which is precisely membership
in the augmentation ideal. -/
theorem faceDifference_mem (f : MvPolynomial (MvPolynomial B A) A) :
    faceZero A B f - faceOne A B f ∈ augmentationIdeal A B := by
  sorry

/-- The conormal class `[d₀f - d₁f]`. Source: Stacks, Tag 08UP
(blueprint: lem-trf-standard-cotangent-boundary-cokernel). -/
def differenceClass (f : MvPolynomial (MvPolynomial B A) A) :
    (Generators.self A B).toExtension.Cotangent :=
  Extension.Cotangent.mk ⟨faceZero A B f - faceOne A B f, faceDifference_mem A B f⟩

/-- The proposed inverse on `I`, namely `h ↦ t_h - t_0`. Source: Stacks, Tags
08UP and 08RB (blueprint: lem-trf-standard-cotangent-boundary-cokernel). -/
def inverseRule (h : augmentationIdeal A B) : Cokernel A B :=
  symbol A B h.val - symbol A B 0

/-- The induced conormal comparison is a `B`-linear isomorphism with inverse
`[h] ↦ t_h - t_0`. The rule on `I` is additive, linear through `ε`, and kills `I²`.
Source: Stacks, Tags 08UP and 08RB, explicit boundary-cokernel calculation
(blueprint: lem-trf-standard-cotangent-boundary-cokernel).

Proof:
1. Write `D(f)` for the quotient of `1 ⊗ df`. The boundary relation gives
   `D(f) = t_{d₀f} - t_{d₁f}`. The universal derivation is additive, vanishes
   on `A`, and obeys the product rule through `ε ∘ d₀`. Polynomial expansion
   shows that the `t_p` generate `E` (def-weil-pbc-kahler-differentials and
   def-weil-pbc-mv-polynomial-ring).
2. For `f = Y_p`, the relation gives `t_{X_b} = 0`. Apply it to
   `Y_p - Y_{X_b}`, where `b = ε(p)`, to obtain `t_p = t_{p-X_b} - t_0`.
3. Define `s(h) = t_h - t_0`. Apply the relation to `Y_h + Y_k` and to
   `Y_0 + Y_0`. The latter gives `t_{2X_0} = -t_0`, and subtraction gives
   `s(h+k) = s(h)+s(k)`. Here the zero polynomial and `X_0` remain distinct.
4. Compare the relations for `Y_r Y_h` and `Y_r Y_0`, with `h ∈ I`.
   Subtraction gives `s(rh) = ε(r) s(h)`.
5. Thus `s(hk) = 0` for `h,k ∈ I`. Since `I²` consists of finite sums of
   these products, additivity kills `I²`. The rule descends to `I/I²`, and
   lifting `b ∈ B` by `X_b` proves that the descended map is `B`-linear.
6. The assumed annihilation of the boundary lets `ρ` descend to `E`.
   On `[h]`, its composite with the inverse is
   `[h-X_0] - [0-X_0] = [h]`. On `t_p`, the other composite is the identity
   by step 2. Generation and linearity give both identities. -/
theorem boundary_cokernel_equiv
    (rho : ModuleOne A B →ₗ[B] (Generators.self A B).toExtension.Cotangent)
    (rho_formula : ∀ (f : MvPolynomial (MvPolynomial B A) A) (b : B),
      rho (differentialTensor A B b f) = b • differenceClass A B f)
    (rho_boundary : rho.comp (boundary A B) = 0) :
    (∃ e : Cokernel A B ≃ₗ[B] (Generators.self A B).toExtension.Cotangent,
      e.toLinearMap.comp (LinearMap.range (boundary A B)).mkQ = rho ∧
      ∀ h : augmentationIdeal A B,
        e.symm (Extension.Cotangent.mk h) = inverseRule A B h) ∧
    (∀ h k : augmentationIdeal A B,
      inverseRule A B (h + k) = inverseRule A B h + inverseRule A B k) ∧
    (∀ (r : MvPolynomial B A) (h : augmentationIdeal A B),
      inverseRule A B (r • h) = epsilon A B r • inverseRule A B h) ∧
    (∀ h : augmentationIdeal A B,
      h.val ∈ augmentationIdeal A B ^ 2 → inverseRule A B h = 0) := by
  sorry

end Algebra.StandardCotangentBoundary
