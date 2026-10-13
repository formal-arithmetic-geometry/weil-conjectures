/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.Quotient.Basic
import Sheaf.RingTheory.RegularSequenceConormal

/-!
# Cotangent homology of the fraction field of a complete intersection

Source: Stacks Project, proof of Tag 07E1, using Tags 00S1, 00S7 and 00LN.
(blueprint: lem-weil-pbc-complete-intersection-fraction-field-cotangent-model)
-/

@[expose] public section

universe u v

namespace Algebra

/-- The cotangent homology of the fraction field of a polynomial complete intersection
is computed by one linear map between finite coordinate spaces.

Source: Stacks Project, More on Algebra, proof of Tag 07E1 (the displayed two-term
complex), with Algebra Tags 00S1, 00S7 and 00LN.
(blueprint: lem-weil-pbc-complete-intersection-fraction-field-cotangent-model)

Proof: Put `P = k[X₁,...,Xₙ]`, `I = (f)` and `A = P/I`. The classes of the regular
sequence give an `A`-basis of `I/I²`, indexed by `Fin f.length` (00LN). The polynomial
differentials give an `A`-basis of `A ⊗[P] Ω[P/k]`, indexed by `Fin n`. In these bases,
the conormal differential is a linear map `A^f.length → A^n`. Its kernel is the first
cotangent homology of this presentation. Independence of presentation (00S1) identifies
this kernel with `H1Cotangent k A`; the conormal exact sequence identifies its cokernel
with `KaehlerDifferential k A`. Localize at all nonzero elements of the domain `A`.
Localization is exact and sends these two free modules to the corresponding coordinate
spaces over `FractionRing A`; thus it preserves both the kernel and cokernel.
The localization comparisons for first cotangent homology and Kähler differentials
(00S7) identify the localized kernel and cokernel with those of the fraction field.
Finally transport the linear map and the two homology equivalences along `e`, obtaining
`δ` and the stated `K`-linear equivalences. This uses no dimension calculation.
-/
theorem exists_fractionField_completeIntersection_cotangent_model
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (n : ℕ) (f : List (MvPolynomial (Fin n) k))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) f)
    [IsDomain (MvPolynomial (Fin n) k ⧸ Ideal.ofList f)]
    (e : FractionRing (MvPolynomial (Fin n) k ⧸ Ideal.ofList f) ≃ₐ[k] K) :
    ∃ δ : (Fin f.length → K) →ₗ[K] (Fin n → K),
      Nonempty (H1Cotangent k K ≃ₗ[K] LinearMap.ker δ) ∧
      Nonempty (KaehlerDifferential k K ≃ₗ[K] ((Fin n → K) ⧸ LinearMap.range δ)) := by
  sorry

end Algebra
