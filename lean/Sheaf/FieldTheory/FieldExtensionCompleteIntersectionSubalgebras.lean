/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF lead L
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Regular.RegularSequence
import Sheaf.FieldTheory.FinitelyGeneratedFieldCompleteIntersectionModel

/-!
# Complete-intersection subalgebras in field extensions

Source: Stacks Project, Algebra, Lemma 07BV (blueprint:
`lem-weil-pbc-field-extension-complete-intersection-subalgebras`).
-/

@[expose] public section

universe u v

namespace FieldTheory

/-- Every finite subset of a field extension is contained in an affine complete
intersection subalgebra.  This is the first assertion of Stacks, Tag 07BV
(blueprint: lem-weil-pbc-field-extension-complete-intersection-subalgebras).

Proof plan from the node:
1. Form the subfield `L = k(E)` and choose a finite transcendence basis, using
   `lem-weil-pbc-finitely-generated-field-finite-transcendence-basis` and
   `def-weil-pbc-transcendence-basis`.
2. By `lem-weil-pbc-finitely-generated-field-complete-intersection-model`, choose a
   domain model `A = k[X]/(f)` with regular sequence `f`, embedded in `L` with
   fraction field `L`.
3. Write each member of `E` as a fraction in `A` and take the product `g` of its
   nonzero denominators (the empty product is one). The principal localization
   `A[1/g]` embeds in `L` and contains `E`; use `def-weil-ring-localization-away`.
4. Lift `g` to a polynomial `h`. Present this localization as
   `k[X,T]/(f,h T - 1)`. The old sequence stays regular after adjoining `T`, since
   multiplication is injective coefficientwise in each successive quotient.
   After those equations the quotient is the domain `A[T]`; `h T - 1` is nonzero
   by its constant coefficient, so is a nonzerodivisor. The final quotient is
   nonzero since it embeds in `L`. This uses `def-weil-pbc-regular-sequence` and
   `def-weil-pbc-mv-polynomial-ring`.
5. Compose the embedding with `L → K`. Applying the construction to the union
   of finite algebra-generating sets of two such images proves directedness;
   applying it to singletons proves their union is `K`. -/
theorem exists_completeIntersection_subalgebra
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (E : Finset K) :
    ∃ (n c : ℕ) (f : List (MvPolynomial (Fin n) k)),
      f.length = c ∧
      RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) f ∧
      ∃ (ι : ((MvPolynomial (Fin n) k ⧸ Ideal.ofList f) →ₐ[k] K)),
        Function.Injective ι ∧
          ∀ x : K, x ∈ E → ∃ y : (MvPolynomial (Fin n) k ⧸ Ideal.ofList f), ι y = x := by
  sorry

end FieldTheory
