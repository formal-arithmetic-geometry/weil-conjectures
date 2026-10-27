module

public import Sheaf.RepresentationTheory.RegularSL2Representation
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Sum

/-! # Integral coefficients of a lowest-weight SL₂ orbit

Source: Milne, Algebraic Groups, Proposition 22.14 and Lemma 22.15, pp.466–467;
the arbitrary-ring coefficient-comparison supplement in the DAG
(blueprint: lem-sfb-sl2-integral-orbit-coefficients).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace RepresentationTheory

/-- Integral orbit coefficients, including their three root/Weyl identities and
compatibility with arbitrary and successive scalar extensions. Submodules `W i`
are the specified summands; `DirectSum.IsInternal W` expresses their direct sum.

Source: Milne, Algebraic Groups, Proposition 22.14 and Lemma 22.15, pp.466–467,
and the DAG's arbitrary-ring supplement
(blueprint: lem-sfb-sl2-integral-orbit-coefficients).

Proof plan:
1. In a basis of the finite free module, substitute `(1,T,0,1)` in the regular
   matrix entries. The orbit is a finite polynomial with coefficients `a_n`.
   Naturality evaluates this polynomial over every base algebra; at zero `a_0=v`.
2. Decompose `a_n` in the specified direct sum. Over `B[T,U,U⁻¹]`, conjugation by
   `h(U)` compares `T^n U^(2i-q) a_(n,i)` with `T^n U^(2n-q) a_(n,i)`.
   Laurent coefficient independence over any ring gives `a_n ∈ W n` for `n≤q`
   and `a_n=0` otherwise. These are the desired `v_i`.
3. Equality at the universal polynomial variable determines every coefficient,
   proving uniqueness and `v_0=v`.
4. Compare the `T^i` coefficients in `x₊(S)x₊(T)v=x₊(S+T)v`. Apply `add_pow`
   (lem-pur-commutative-ring-binomial-expansion) and symmetry of binomial
   coefficients to obtain the upper-root formula.
5. Put `u=1+ST`. Inverting `u`, the Gauss identity is
   `x₋(S)x₊(T)=x₊(T/u)h(u⁻¹)x₋(S/u)`. The last factor fixes `v`, so its orbit
   is `∑ T^k u^(q-k) v_k`. All powers `q-k` are nonnegative.
6. Multiplication by `1+ST` on vector polynomials is injective: its constant
   coefficient forces `f_0=0`, then `f_r+Sf_(r-1)=0` inductively forces `f_r=0`.
   Hence all its powers are injective. In a basis, the localization equality
   descends to `B[S,T]`, with no domain, reducedness or flatness assumption.
7. Expand `(1+ST)^(q-k)` by `add_pow` and compare `T^i` coefficients. Substituting
   `j=i-k` yields the lower-root binomial coefficients without cancelling factorials.
8. Over `B[T,T⁻¹]`, use
   `w x₊(T)=x₊(-T⁻¹)h(-T⁻¹)x₋(T⁻¹)`. Its action on `v` gives
   `∑ T^i w v_i = (-T)^q ∑ (-T⁻¹)^k v_k`. Laurent coefficient comparison
   gives `w v_i=(-1)^i v_(q-i)` with the stated Weyl sign.
9. Evaluate the universal identities at any `z` in any base algebra. The degree-one
   upper coefficient is `choose (i+1) 1 v_(i+1)=(i+1)v_(i+1)`.
10. Applying any algebra map to polynomial coordinates carries the coefficients to
    `1⊗v_i`; uniqueness identifies these with the coefficients over the new base.
    The tensor comparison sends `e⊗(d⊗v_i)` to `(d•e)⊗v_i`, so successive
    base changes agree. Zero vectors and positive-characteristic binomials are allowed.
-/
theorem exists_unique_sl2_integral_orbit_coefficients
    (B : Type u) [CommRing B] (q : ℕ)
    (V : Type v) [AddCommGroup V] [Module B V] [Module.Free B V] [Module.Finite B V]
    (W : Fin (q + 1) → Submodule B V) (hW : DirectSum.IsInternal W)
    [∀ i, Module.Free B (W i)] [∀ i, Module.Finite B (W i)]
    (ρ : RegularSL2Representation B V)
    (hweight : ∀ (C : Type u) [CommRing C] [Algebra B C]
      (t : Cˣ) (i : Fin (q + 1)) (a : W i),
      ρ.app C (sl2Torus t) (1 ⊗ₜ[B] (a : V)) =
        ((t ^ (2 * (i.val : ℤ) - (q : ℤ)) : Cˣ) : C) • (1 ⊗ₜ[B] (a : V)))
    (v : W 0)
    (hfixed : ∀ (C : Type u) [CommRing C] [Algebra B C] (z : C),
      ρ.app C (sl2Lower z) (1 ⊗ₜ[B] (v : V)) = 1 ⊗ₜ[B] (v : V)) :
    ∃ a : ∀ i : Fin (q + 1), W i,
      a 0 = v ∧
      ρ.app (Polynomial B) (sl2Upper Polynomial.X) (1 ⊗ₜ[B] (v : V)) =
        ∑ i : Fin (q + 1), (Polynomial.X : Polynomial B) ^ i.val • (1 ⊗ₜ[B] (a i : V)) ∧
      (∀ b : ∀ i : Fin (q + 1), W i,
        ρ.app (Polynomial B) (sl2Upper Polynomial.X) (1 ⊗ₜ[B] (v : V)) =
          ∑ i : Fin (q + 1), (Polynomial.X : Polynomial B) ^ i.val • (1 ⊗ₜ[B] (b i : V)) → b = a) ∧
      (∀ (C : Type u) [CommRing C] [Algebra B C] (z : C) (i : Fin (q + 1)),
        ρ.app C (sl2Upper z) (1 ⊗ₜ[B] (a i : V)) =
          ∑ k : Fin (q + 1), if i.val ≤ k.val then
            ((Nat.choose k.val (k.val - i.val) : C) * z ^ (k.val - i.val)) •
              (1 ⊗ₜ[B] (a k : V)) else 0) ∧
      (∀ (C : Type u) [CommRing C] [Algebra B C] (z : C) (i : Fin (q + 1)),
        ρ.app C (sl2Lower z) (1 ⊗ₜ[B] (a i : V)) =
          ∑ k : Fin (q + 1), if k.val ≤ i.val then
            ((Nat.choose (q - k.val) (i.val - k.val) : C) * z ^ (i.val - k.val)) •
              (1 ⊗ₜ[B] (a k : V)) else 0) ∧
      (∀ (C : Type u) [CommRing C] [Algebra B C] (i : Fin (q + 1)),
        ρ.app C (sl2Weyl C) (1 ⊗ₜ[B] (a i : V)) =
          (-1 : C) ^ i.val • (1 ⊗ₜ[B] (a ⟨q - i.val, by omega⟩ : V))) ∧
      (∀ (i : Fin (q + 1)) (hi : i.val < q),
        (TensorProduct.lid B V)
          ((Polynomial.lcoeff B 1).rTensor V
            (ρ.app (Polynomial B) (sl2Upper Polynomial.X) (1 ⊗ₜ[B] (a i : V)))) =
          (i.val + 1) • (a ⟨i.val + 1, by omega⟩ : V)) ∧
      (∀ (D : Type u) [CommRing D] [Algebra B D]
        (c : Fin (q + 1) → D ⊗[B] V),
        (ρ.app (Polynomial D) (sl2Upper Polynomial.X) (1 ⊗ₜ[B] (v : V)) =
          ∑ i : Fin (q + 1), (Polynomial.X : Polynomial D) ^ i.val •
            (TensorProduct.AlgebraTensorModule.cancelBaseChange
              B D (Polynomial D) (Polynomial D) V) (1 ⊗ₜ[D] c i)) ↔
          c = fun i ↦ 1 ⊗ₜ[B] (a i : V)) ∧
      (∀ (D : Type u) [CommRing D] [Algebra B D],
        ρ.app (Polynomial D) (sl2Upper Polynomial.X) (1 ⊗ₜ[B] (v : V)) =
          ∑ i : Fin (q + 1), (Polynomial.X : Polynomial D) ^ i.val • (1 ⊗ₜ[B] (a i : V))) ∧
      (∀ (D E : Type u) [CommRing D] [CommRing E] [Algebra B D] [Algebra B E]
        [Algebra D E] [IsScalarTower B D E] (e : E) (d : D) (i : Fin (q + 1)),
        (TensorProduct.AlgebraTensorModule.cancelBaseChange B D E E V)
          (e ⊗ₜ[D] (d ⊗ₜ[B] (a i : V))) = (d • e) ⊗ₜ[B] (a i : V)) := by
  sorry

end RepresentationTheory
