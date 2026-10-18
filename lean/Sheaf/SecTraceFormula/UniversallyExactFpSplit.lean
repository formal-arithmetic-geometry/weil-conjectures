module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# A universally exact sequence with finitely presented quotient splits

Source: literature/stacks-project/algebra.tex, Tags 058K and 058L
(blueprint: lem-trf-universally-exact-fp-split).
-/

@[expose] public section
set_option autoImplicit false

universe uR uA uB uC t

namespace LinearMap

/-- A universally exact sequence with finitely presented quotient admits a retraction.

Source: literature/stacks-project/algebra.tex, Tag 058L, `lemma-universally-exact-split`,
together with Tag 058K, `theorem-universally-exact-criteria`
(blueprint: lem-trf-universally-exact-fp-split).

Proof:
1. Exactness after tensoring with every module gives the finitely presented tensor
   injectivity tests required by `lem-trf-universal-injective-finite-test`.
2. A finite presentation of the quotient, the lifting argument of Tag 058K, and
   tensor right exactness produce a section of `p`.
3. The section is converted to a retraction of `i`: for each `b`, the element
   `b - s (p b)` lies uniquely in the image of `i`, and this factor is linear.
-/
theorem universallyExactFpSplit
    (R : Type uR) [CommRing R]
    (A : Type uA) [AddCommGroup A] [Module R A]
    (B : Type uB) [AddCommGroup B] [Module R B]
    (C : Type uC) [AddCommGroup C] [Module R C]
    (i : A →ₗ[R] B) (p : B →ₗ[R] C)
    (hi : Function.Injective i)
    (hp : Function.Surjective p)
    (hex : Function.Exact i p)
    [Module.FinitePresentation R C]
    (hTensor : ∀ (Q : Type (max uR uA uB uC t)) [AddCommGroup Q] [Module R Q],
      Function.Injective (i.rTensor Q) ∧
        Function.Surjective (p.rTensor Q) ∧
          Function.Exact (i.rTensor Q) (p.rTensor Q)) :
    ∃ r : B →ₗ[R] A, r.comp i = LinearMap.id := by
  sorry

end LinearMap
