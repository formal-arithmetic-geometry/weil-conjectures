/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Sheaf.RingTheory.ProjectiveConeHilbertStandardDegrees
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.RingTheory.AssociatedGradedRing
public import Sheaf.AlgebraicGeometry.HilbertSamuelInvariant
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.LocalRing.Module

/-! # Simple residue extensions and Hilbert--Samuel comparison

Source: Hironaka, Certain numerical characters of singularities (1970), (9.1)--(9.6),
pp.162--164, Propositions 10--11 and Lemma 12, pp.164--167, and Remark (12.2),
pp.167--168 (blueprint: lem-trf-simple-residue-extension-hilbert-comparison).

The scalar extension and its evaluation map are constructed from the actual simple
subfield of the residue field. The numerical functions and degree sequence reuse the
published definitions, with no choices of comparison maps.
-/

@[expose] public section
set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace Hironaka

variable (k : Type u) (R : Type v) [Field k] [CommRing R] [IsLocalRing R] [Algebra k R]

/-- The tensor product `k(α) ⊗[k] R`, using the actual subfield of the residue field.
Source: Hironaka (1970), (9.1)--(9.6), pp.162--164
(blueprint: lem-trf-simple-residue-extension-hilbert-comparison). -/
abbrev simpleResidueTensor (α : IsLocalRing.ResidueField R) :=
  (IntermediateField.adjoin k {α}) ⊗[k] R

/-- Evaluation `a ⊗ r ↦ a r̄`. The second map is the canonical residue map, as a
`k`-algebra homomorphism. Source: Hironaka (1970), (9.6), pp.163--164
(blueprint: lem-trf-simple-residue-extension-hilbert-comparison). -/
noncomputable def simpleResidueEvaluation (α : IsLocalRing.ResidueField R) :
    simpleResidueTensor k R α →ₐ[k] IsLocalRing.ResidueField R :=
  Algebra.TensorProduct.productMap (IntermediateField.adjoin k {α}).val
    (IsScalarTower.toAlgHom k R (IsLocalRing.ResidueField R))

/-- Localization at the kernel of the canonical evaluation into the residue field.
Source: Hironaka (1970), (9.6), pp.163--164
(blueprint: lem-trf-simple-residue-extension-hilbert-comparison). -/
abbrev simpleResidueExtension (α : IsLocalRing.ResidueField R) :=
  @Localization.AtPrime (simpleResidueTensor k R α) _
    (RingHom.ker (simpleResidueEvaluation k R α).toRingHom)
    (RingHom.ker_isPrime (simpleResidueEvaluation k R α).toRingHom)

/-- The canonical map `R → (k(α) ⊗[k] R)_(ker ε)`, first including the right tensor
factor and then localizing. Source: Hironaka (1970), (9.6), pp.163--164
(blueprint: lem-trf-simple-residue-extension-hilbert-comparison). -/
noncomputable def simpleResidueExtensionMap (α : IsLocalRing.ResidueField R) :
    R →+* simpleResidueExtension k R α :=
  (algebraMap (simpleResidueTensor k R α) (simpleResidueExtension k R α)).comp
    Algebra.TensorProduct.includeRight.toRingHom

open Classical in
/-- The localized simple scalar extension has the same residue field, increases the
Hilbert--Samuel function by at least the transcendence summation, and preserves regularity
and the padded standard-degree sequence in the equality case.

The witnesses `ρ` and `σ` identify the residue fields canonically: the first agrees with
`ε` on the tensor product, and the second descends the first along the quotient map.
The image of the ambient maximal ideal is the quotient maximal ideal. All truncation
lengths in `quotientHilbertFunction` are finite here, so its `toNat` is lossless.

Source: Hironaka (1970), (9.1)--(9.6), pp.162--164, Propositions 10--11 and Lemma 12,
pp.164--167, and Remark (12.2), pp.167--168
(blueprint: lem-trf-simple-residue-extension-hilbert-comparison).

Proof (the node's nine steps):
1. The quotient-local-structure and surjective-image-noetherian lemmas give a nonzero
Noetherian local quotient `A = R/I` with residue field `L`. Lift `α` to `u ∈ R`.
The local-polynomial-tangent-extension lemma gives `S = R[V]_(m,V)` and its quotient
`C = A[V]_(m/I,V)`, with residue field `L`; `S` is regular when `R` is regular.
Their quotient identification follows coefficientwise, including the denominators.
2. If `α` is transcendental, `k(α) ⊗ R` is the localization of `R[t]` by nonzero
`k[t]` polynomials. Translate `t = V + u`; localization at the evaluation kernel gives
`R' = S` and `A' = C`. If `α` is algebraic with minimal polynomial `p`, tensoring the
presentation `k[t]/(p)` gives `R' = S/(g)` and `A' = C/(h)`, for `g = p(V+u)` and
its image `h ∈ C`. Both belong to the corresponding maximal ideals.
3. The quotient-local-structure and surjective-image-noetherian lemmas give the claimed
local and Noetherian structures. Evaluation at `V = 0` supplies the residue maps.
4. The local-polynomial-tangent-extension lemma identifies `gr C = (gr A)[Z]`.
The maximal-adic-graded-length-bridge lemma and a finite double sum give
`h_C(n) = sum_{a=0}^n h_A(a)`, hence `h_C(n) - h_C(n-1) = h_A(n)`, with `h_C(-1)=0`.
5. In the transcendental case this proves the comparison with equality and `e = 1`;
regularity follows from polynomial extension. The degree assertion follows in step 9.
6. In the algebraic case, multiplication by `h` gives the right-exact sequence from
`C/n^n` to `C/n^(n+1)` to `A'/m'^(n+1)`. Its kernel is
`K_n = (n^(n+1):h)/n^n`. Quotient scalars do not change module length. Apply
length-additive-short-exact to obtain `h_A'(n) = h_A(n) + length K_n`, proving the
inequality for `e = 0`, also at `n = 0` where `K_0 = 0`.
7. If equality holds and `R` is regular, `length K_1 = 0`. If `h` belonged to `n²`,
then `K_1 = C/n = L`, a contradiction. Thus `g ∉ N²`, and the
regular-hypersurface-initial-form lemma gives regularity of `R' = S/(g)`.
8. Extend the class of `g` to a cotangent basis, use regular-local-cotangent-dimension
and nakayama-local-generators to lift it to parameters of `S`. Apply the equality
clause of linear-sections-hilbert-standard-degrees to `(S,IS)` and the parameter `g`,
using `h_C = Λ h_A'`. It gives `ν*(S,IS) = ν*(R',I')`.
9. Quotient compatibility for the polynomial tangent cone gives `E(S,IS) = E(R,I)[Z]`.
Since `(G[Z])_+ = (G_+,Z)`, constant coefficient induces
`E[Z]/(G_+,Z)E[Z] ≅ E/G_+E`. Generator multiplicities agree in every positive degree;
therefore the sorted sequences, including their infinite tails, agree. Combine this
with step 5 or step 8. For `I = 0` both sequences are entirely infinite. -/
theorem simpleResidueExtensionHilbertComparison [IsNoetherianRing R]
    (α : IsLocalRing.ResidueField R) (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) :
    IsNoetherianRing (simpleResidueExtension k R α) ∧
    IsLocalRing (simpleResidueExtension k R α) ∧
    IsNoetherianRing
      ((simpleResidueExtension k R α) ⧸ I.map (simpleResidueExtensionMap k R α)) ∧
    IsLocalRing
      ((simpleResidueExtension k R α) ⧸ I.map (simpleResidueExtensionMap k R α)) ∧
    (∃ ρ : simpleResidueExtension k R α →+* IsLocalRing.ResidueField R,
      ρ.comp (algebraMap (simpleResidueTensor k R α) (simpleResidueExtension k R α)) =
          (simpleResidueEvaluation k R α).toRingHom ∧
      Function.Surjective ρ ∧
      RingHom.ker ρ = IsLocalRing.maximalIdeal (simpleResidueExtension k R α) ∧
      ∃ σ : ((simpleResidueExtension k R α) ⧸
          I.map (simpleResidueExtensionMap k R α)) →+* IsLocalRing.ResidueField R,
        σ.comp (Ideal.Quotient.mk (I.map (simpleResidueExtensionMap k R α))) = ρ ∧
        Function.Surjective σ ∧
        RingHom.ker σ = (IsLocalRing.maximalIdeal (simpleResidueExtension k R α)).map
          (Ideal.Quotient.mk (I.map (simpleResidueExtensionMap k R α)))) ∧
    (∀ n : ℕ,
      ((AlgebraicGeometry.HilbertSamuel.summation^[
          if IsAlgebraic k α then 0 else 1])
        (quotientHilbertFunction (IsLocalRing.maximalIdeal R) I)) n ≤
      quotientHilbertFunction (IsLocalRing.maximalIdeal (simpleResidueExtension k R α))
        (I.map (simpleResidueExtensionMap k R α)) n) ∧
    (IsRegularLocalRing R →
      quotientHilbertFunction (IsLocalRing.maximalIdeal (simpleResidueExtension k R α))
          (I.map (simpleResidueExtensionMap k R α)) =
        (AlgebraicGeometry.HilbertSamuel.summation^[if IsAlgebraic k α then 0 else 1])
          (quotientHilbertFunction (IsLocalRing.maximalIdeal R) I) →
      IsRegularLocalRing (simpleResidueExtension k R α) ∧
      nuStar I = nuStar (I.map (simpleResidueExtensionMap k R α))) := by
  sorry

end Hironaka
