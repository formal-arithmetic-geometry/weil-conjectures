/-
Copyright (c) 2026 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib

@[expose] public section

/-!
# Challenge: the `lean-eval` problem `weil_conjectures`

This is a `leanprover/comparator` challenge file. It reproduces, verbatim, the statement of
the problem `weil_conjectures` of [leanprover/lean-eval](https://github.com/leanprover/lean-eval)
(`LeanEval/AlgebraicGeometry/WeilConjectures.lean` at commit `85a88c3`, submitted by Junyan
Xu). The only changes are the module header and the dropped `@[eval_problem]` marker, which
comes from lean-eval's `EvalTools` package. Like the original, it imports only `Mathlib`.

The solution `LeanEvalWeil/Solution.lean` proves the identical statement with this
repository (`WeilConjectures/LeanEval/WeilConjectures.lean`).
-/

open CategoryTheory AlgebraicGeometry

namespace LeanEval.AlgebraicGeometry.WeilConjectures

/-- The **Weil conjectures** in terms of point counts: if `X` is a smooth complete
algebraic variety (geometrically irreducible) over a finite field `F` of dimension `d`,
then there exists multisets `Aᵢ` of Frobenius eigenvalues (which are algebraic integers)
such that for the finite extension `E / F` of degree `m`, we have
`#X(E) = ∑_{0 ≤ i ≤ 2d} (-1)ⁱ ∑_{α ∈ Aᵢ} αᵐ` (rationality of the zeta series).
Moreover, the multisets satisfy `A₀ = {1}`, the Poincaré duality (functional equation)
`A_{2d-i} = #Fᵈ / Aᵢ`, the "Riemann hypothesis" `|α| = #F^{i/2}` for all `α ∈ Aᵢ`,
and are invariant under all automorphisms of ℂ.

This statement does not include the identities between sizes of the multisets and
the Betti numbers of a complex variety defined over a number field whose reduction
modulo a prime ideal is `X`.

The Riemann hypothesis was first proved by Deligne while the rest were already established
by Grothendieck (with Artin, Verdier and earlier work of Dwork) using the theory of ℓ-adic
cohomology. -/
theorem weil_conjectures (F : Type*) [Finite F] [Field F]
    (X : Over (Spec (.of F))) [GeometricallyIrreducible X.hom] [IsProper X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    ∃ A : ℕ → Multiset ℂ, A 0 = {1} ∧
      (∀ i ≤ 2 * d, A (2 * d - i) = (A i).map (Nat.card F ^ d / · : ℂ → ℂ) ∧
        (∀ φ : ℂ ≃+* ℂ, (A i).map φ = A i) ∧
        ∀ α ∈ A i, IsIntegral ℤ α ∧ ‖α‖ = √(Nat.card F ^ i)) ∧
      ∀ (E : Type _) [Field E] [Algebra F E] [FiniteDimensional F E],
        Nat.card (.mk (Spec.map <| CommRingCat.ofHom <| algebraMap F E) ⟶ X) =
        ∑ i ∈ Finset.Iic (2 * d), (-1) ^ i * ((A i).map (· ^ Module.finrank F E)).sum := by
  sorry

end LeanEval.AlgebraicGeometry.WeilConjectures
