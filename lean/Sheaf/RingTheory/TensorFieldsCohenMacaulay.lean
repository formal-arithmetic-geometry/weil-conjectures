/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.RingTheory.Depth
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Sheaf.RingTheory.PolynomialAlgebraCohenMacaulay
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Sheaf.RingTheory.FlatModuleAtPrime
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.GoingUp
import Sheaf.RingTheory.FlatLocalDepthFormula
import WeilConjectures.RingTheory.DepthLeSupportDimension

/-!
# Tensor products of fields are Cohen–Macaulay

Source: Stacks Project, Algebra, Tag 045M (lemma-tensor-fields-CM)
(blueprint: lem-trf-tensor-fields-cohen-macaulay).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Algebra.TensorProduct

/-- A tensor product of two field extensions, at least one finitely generated as a field,
is Noetherian and all its prime localizations are Noetherian local rings of depth equal
to their Krull dimension. Source: Stacks Project, Algebra, Tag 045M
(blueprint: lem-trf-tensor-fields-cohen-macaulay).

Proof, following the node's nine steps:
1. Swap the factors if necessary, so `K/k` is finitely generated. The finite transcendence
   basis lemma and the algebraic-generators finite-extension lemma write `K` as a finite
   extension of `F = k(t₁, …, tᵣ)`. Choose a finite `F`-basis of `K`; no separability is used.
2. Put `B = k[t₁, …, tᵣ]`, `W = B ∖ {0}`, and `P = L[t₁, …, tᵣ]`. The polynomial tensor
   isomorphism and localization-tensor-over-base identify `A = F ⊗[k] L` with `W⁻¹P`.
   The maps send `(b ⊗ l)/s` to `(b/s) ⊗ l` and preserve products.
3. A field has depth and dimension zero. Polynomial-algebra-CM makes `P` Noetherian
   and Cohen–Macaulay; localization-noetherian makes `A` Noetherian.
4. For a prime `p` of `A`, contract it to `r` in `P`. Localization-quotient-by-prime
   and the fraction formulas `f/g ↦ (f/1)/(g/1)` and `(a/s)/(b/t) ↦ at/(sb)` identify
   `A_p` with `P_r`. Thus `A_p` has depth equal to dimension and is Noetherian local.
5. Identify `K ⊗[k] L` with `A ⊗[F] K` by `(f ⊗ l) ⊗ x ↦ fx ⊗ l` and inverse
   `x ⊗ l ↦ (1 ⊗ l) ⊗ x`. A finite basis of `K/F` gives an `A`-basis, so this algebra
   is finite free, also in the inseparable case.
6. Finite-algebra-noetherian makes `T = K ⊗[k] L` Noetherian. Finite-free-flat and
   finite-algebra-is-integral make the global map `A → T` flat and integral.
7. For a prime `q` of `T`, put `p = q ∩ A`, `R = A_p`, `S = T_q`. Localization at a
   prime and localization-noetherian make both rings Noetherian local. The affine flat
   module local criterion makes `R → S` flat. Step 4 gives depth `R` equal to dimension `R`.
8. Localization-dimension-chains-below-prime and integral-incomparability applied to
   the global map `A → T` give dimension `S` at most dimension `R`. No integrality
   assertion about the map `R → S` is needed.
9. Flat-local-depth-formula gives depth `S` at least depth `R`. The nonzero finite
   `S`-module `S` has full support, so depth-le-support-dimension gives depth `S` at most
   dimension `S`. The inequalities force equality of depth and dimension. The swap
   in step 1 handles finite generation of `L/k` alone.
-/
theorem isNoetherianRing_and_local_depth_eq_dimension_of_fg
    {k : Type u} {K : Type v} {L : Type w} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L]
    (hfg : (⊤ : IntermediateField k K).FG ∨ (⊤ : IntermediateField k L).FG) :
    IsNoetherianRing (TensorProduct k K L) ∧
      ∀ (q : Ideal (TensorProduct k K L)) [q.IsPrime],
        IsNoetherianRing (Localization.AtPrime q) ∧
          IsLocalRing (Localization.AtPrime q) ∧
            (IsLocalRing.depth (R := Localization.AtPrime q)
              (Localization.AtPrime q) : WithBot ℕ∞) =
                ringKrullDim (Localization.AtPrime q) := by
  sorry

end Algebra.TensorProduct
