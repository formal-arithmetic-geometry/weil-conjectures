module

public import Sheaf.RepresentationTheory.IntegralSl2LatticeHom
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.FreeModule.Basic
import Sheaf.RepresentationTheory.Sl2RationalPolynomialModel
import Mathlib.AlgebraicGeometry.Gluing

/-! # Integration of integral divided-power sl₂ lattices

Source: Milne, Algebraic Groups (2017), Section 23h, equation (153), pp.509--510,
and Theorem 23.70, pp.507--508. The integral two-chart argument is supplied by the DAG.
(blueprint: lem-sfb-sl2-lattice-integration)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace RepresentationTheory

/-- The integral weight-j submodule L ∩ ker(H-j), using the canonical inclusion in ℚ ⊗ L.
Source: Milne, equation (152), p.510
(blueprint: lem-sfb-sl2-lattice-integration). -/
def sl2LatticeWeight (L : Type u) [AddCommGroup L] [Module ℤ L]
    (H : Module.End ℚ (ℚ ⊗[ℤ] L)) (j : ℤ) : Submodule ℤ L :=
  LinearMap.ker
    ((H.restrictScalars ℤ).comp (TensorProduct.mk ℤ ℚ L 1) -
      j • TensorProduct.mk ℤ ℚ L 1)

/-- An integral sl₂ lattice stable under all divided powers integrates uniquely over every
commutative base ring. Integral divided powers are specified by their scalar-extension
identity; since L is free, such lifts, when they exist, are unique. The root restrictions
are stated for every common nilpotence bound N and every family of these unique lifts.
This avoids choosing integral matrices or a nilpotence bound in the definition.
The torus restriction is tested on pure tensors from every integral weight space; these
span by `hL`, so it specifies exactly the automorphism D(s).

Source: Milne, Section 23h, equation (153), pp.509--510, and Theorem 23.70, pp.507--508.
The integral assertion is the explicit agent-supplied supplement recorded in the DAG,
not a claim that Milne states integral lattice integration as a separate theorem.
(blueprint: lem-sfb-sl2-lattice-integration).

Proof plan (the six steps of the DAG):
1. Apply lem-sfb-sl2-rational-polynomial-model to W = ℚ ⊗ L. On each binary-form summand
   use P(X,Y) ↦ P(aX+cY,bX+dY). Substitution respects multiplication. Its upper and lower
   restrictions are the divided-power exponentials and its diagonal weights are n-2i.
2. The integral divided powers satisfy the binomial identities, by embedding in rational
   endomorphisms. Thus X₊(t)X₊(u)=X₊(t+u), and similarly for X₋. The integral weight
   projections supplied by `hL` give D(s)D(s⁻¹)=1. Set Nw=X₊(1)X₋(-1)X₊(1).
3. On the two charts D(a), D(c) of ℤ[a,b,c,d]/(ad-bc-1), factor the universal matrix as
   x₋(c/a)diag(a,a⁻¹)x₊(b/a), respectively
   w x₋(-a/c)diag(-c,(-c)⁻¹)x₊(d/c). The corresponding integral matrix products and
   their inverses define actual chart morphisms into GL(L).
4. Both products agree rationally with step 1. The overlap is an integral Laurent
   polynomial ring and injects into its rationalization, so they agree integrally.
   Apply lem-weil-pbc-scheme-morphism-gluing to glue them.
5. On the four product charts, the same injectivity argument descends the rational
   multiplication law. The identity follows from the D(a) formula. The resulting
   morphism is a group homomorphism and its matrix entries are regular functions.
6. The three restrictions follow on D(a). After any base change B, both charts and
   factorizations still hold. Any homomorphism with these restrictions has the same
   image of w and thus the same chart formulas. Gluing uniqueness proves uniqueness,
   also for nonreduced B. For the zero lattice all automorphisms are the identity;
   trivial summands have constant identity formulas.
-/
theorem existsUnique_sl2_lattice_integration
    (L : Type u) [AddCommGroup L] [Module ℤ L]
    [Module.Free ℤ L] [Module.Finite ℤ L]
    (E F H : Module.End ℚ (ℚ ⊗[ℤ] L))
    (hHE : H * E - E * H = (2 : ℚ) • E)
    (hHF : H * F - F * H = (-2 : ℚ) • F)
    (hEF : E * F - F * E = H)
    (hE : IsNilpotent E) (hF : IsNilpotent F)
    (hH : ∃ (d : ℕ) (b : Module.Basis (Fin d) ℚ (ℚ ⊗[ℤ] L)) (weight : Fin d → ℤ),
      ∀ i : Fin d, H (b i) = (weight i : ℚ) • b i)
    (hL : DirectSum.IsInternal (sl2LatticeWeight L H))
    (hdivE : ∀ m : ℕ, ∃ D : Module.End ℤ L,
      D.baseChange ℚ = ((m.factorial : ℚ)⁻¹) • E ^ m)
    (hdivF : ∀ m : ℕ, ∃ D : Module.End ℤ L,
      D.baseChange ℚ = ((m.factorial : ℚ)⁻¹) • F ^ m)
    (B : Type v) [CommRing B] :
    ∃! ρ : IntegralSl2LatticeHom B L,
      (∀ (N : ℕ) (dE dF : ℕ → Module.End ℤ L),
        E ^ N = 0 → F ^ N = 0 →
        (∀ m : ℕ, (dE m).baseChange ℚ = ((m.factorial : ℚ)⁻¹) • E ^ m) →
        (∀ m : ℕ, (dF m).baseChange ℚ = ((m.factorial : ℚ)⁻¹) • F ^ m) →
        ∀ (A : CommAlgCat.{max u v} B) (a : A),
          (ρ.app A (Matrix.SpecialLinearGroup.transvection
            (zero_ne_one : (0 : Fin 2) ≠ 1) a)).toLinearMap =
              ∑ m ∈ Finset.range N, a ^ m • (dE m).baseChange A ∧
          (ρ.app A (Matrix.SpecialLinearGroup.transvection
            (one_ne_zero : (1 : Fin 2) ≠ 0) a)).toLinearMap =
              ∑ m ∈ Finset.range N, a ^ m • (dF m).baseChange A) ∧
      (∀ (A : CommAlgCat.{max u v} B) (s : Aˣ) (j : ℤ)
        (l : sl2LatticeWeight L H j) (a : A),
        ρ.app A (integralSl2Diagonal s) (a ⊗ₜ[ℤ] (l : L)) =
          (↑(s ^ j) : A) • (a ⊗ₜ[ℤ] (l : L))) := by
  sorry

end RepresentationTheory
