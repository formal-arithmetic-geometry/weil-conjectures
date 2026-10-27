module

public import Mathlib.Algebra.Lie.SerreConstruction
public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.Lie.Weights.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.RootSystem.BaseExists

/-!
# The rational Serre presentation theorem

Source: Milne, Algebraic Groups (2017), Appendix C.19--C.26, pp.611--613,
and Theorem 23.63, pp.503--504, with its characteristic-zero extension p.508.
(blueprint: lem-sfb-serre-rational-presentation)

The presented algebra is Mathlib's actual quotient `Matrix.ToLieAlgebra`, not
an abstract algebra satisfying the relations. The auxiliary map names the images
of its free generators. All root-space assertions use ordinary weight spaces.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace LieAlgebra

/-- The image of a free generator in the quotient by the Serre ideal.
Source: Milne, Algebraic Groups, Theorem 23.63, p.504.
(blueprint: lem-sfb-serre-rational-presentation) -/
noncomputable def rationalSerreGenerator {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (g : CartanMatrix.Generators (Fin r)) : Matrix.ToLieAlgebra ℚ A :=
  LieSubmodule.Quotient.mk' (CartanMatrix.Relations.toIdeal ℚ A) (FreeLieAlgebra.of ℚ g)

/-- The rational Serre quotient realizes the prescribed reduced root system.
Source: Milne, Algebraic Groups, C.19--C.26, pp.611--613; Theorem 23.63,
pp.503--504, and its characteristic-zero extension p.508.
(blueprint: lem-sfb-serre-rational-presentation)

Proof plan, following the eight steps of the node:
1. If the roots are empty, spanning makes V zero and the generator-free quotient
   zero. Otherwise the reflection group acts faithfully on the finite spanning
   root set. Average a rational dot product over it. Orthogonality gives
   c_a(x) = 2 B(x,a)/B(a,a), coroot spanning, injectivity and equivariance.
2. Extend scalars to the reals, avoid the finitely many root hyperplanes, and use
   lem-sfb-root-chamber-simple-transitivity to obtain a base. It is rational
   because its vectors are rational and independent. For ANY base the root and
   coroot families satisfy lem-sfb-root-base-rational-integral-spans, so its
   simple coroots form a rational basis of the dual space.
3. Reflections of distinct simple roots imply off-diagonal Cartan entries are
   nonpositive. The form gives symmetric vanishing and diagonal entries two.
   Apply lem-sfb-serre-graded-triangular-quotient. Its zero component has basis H_i,
   simple components are the nonzero lines E_i and F_i, and mixed-sign and higher
   single-root degrees vanish. Jacobi identifies degrees with adjoint weights.
4. The Serre relations make ad E_i and ad F_i nilpotent on every generator.
   The iterated derivation formula propagates local nilpotence to every Lie
   word and finite linear sum. Apply lem-sfb-integrable-sl2-reflection-automorphism
   to obtain automorphisms taking degree beta to its simple reflection.
5. Positive definiteness finds a positive simple pairing at any positive
   nonzero degree. Reflection strictly lowers its integral height; mixed signs
   are impossible. Induct down to a simple root. Do the same for roots of R.
   Reflection automorphisms then show that precisely R occurs, with dimension
   one at each root. The finite root set proves finite dimensionality.
6. Transport each simple sl2 triple along these automorphisms. Equivariance
   identifies its H element with c_a, and its opposite root bracket is H.
   The normalization a(H)=2 identifies the coroot uniquely.
7. A solvable ideal splits into weight intersections by polynomial projectors
   for a rational Cartan element separating the finite set of weights. A
   nonzero root intersection contains its sl2 triple, contradicting solvability.
   Thus the ideal lies in the zero component; bracketing with the simple root
   vectors and separation by the base forces it to vanish. This is precisely
   HasTrivialRadical, as specified by def-wf-semisimple-lie-algebra.
8. The ordinary weight spaces span the quotient. Its Cartan centralizer is the
   zero-weight component, so the independent H_i span a maximal abelian
   subalgebra. All constructions include the empty, rank-zero case.
-/
theorem rationalSerrePresentation
    (V : Type u) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (R : Set V) (c : R → Module.Dual ℚ V)
    (hfinite : R.Finite) (hne : ∀ a : R, (a : V) ≠ 0)
    (hspan : Submodule.span ℚ R = ⊤)
    (htwo : ∀ a : R, c a a = 2)
    (hint : ∀ a b : R, ∃ n : ℤ, c a b = (n : ℚ))
    (hreflect : ∀ a : R, Set.BijOn (fun v : V ↦ v - c a v • (a : V)) R R)
    (hreduced : ∀ a : R,
      R ∩ (Submodule.span ℚ ({(a : V)} : Set V) : Set V) = {(a : V), -(a : V)}) :
    (∃ (r : ℕ) (b : Module.Basis (Fin r) ℚ V),
      (∀ i, b i ∈ R) ∧
      ∀ a : R, (∀ i, ∃ n : ℤ, b.repr a i = (n : ℚ)) ∧
        ((∀ i, 0 ≤ b.repr a i) ∨ (∀ i, b.repr a i ≤ 0))) ∧
    (∀ (r : ℕ) (b : Module.Basis (Fin r) ℚ V) (hb : ∀ i, b i ∈ R),
      (∀ a : R, (∀ i, ∃ n : ℤ, b.repr a i = (n : ℚ)) ∧
        ((∀ i, 0 ≤ b.repr a i) ∨ (∀ i, b.repr a i ≤ 0))) →
      ∀ A : Matrix (Fin r) (Fin r) ℤ,
      (∀ i j, (A i j : ℚ) = c ⟨b i, hb i⟩ (b j)) →
      FiniteDimensional ℚ (Matrix.ToLieAlgebra ℚ A) ∧
      HasTrivialRadical ℚ (Matrix.ToLieAlgebra ℚ A) ∧
      LinearIndependent ℚ (fun i ↦ rationalSerreGenerator A (CartanMatrix.Generators.H i)) ∧
      (∃ h : LieSubalgebra ℚ (Matrix.ToLieAlgebra ℚ A),
        h.toSubmodule = Submodule.span ℚ
          (Set.range (fun i ↦ rationalSerreGenerator A (CartanMatrix.Generators.H i))) ∧
        IsLieAbelian h ∧
        (∀ k : LieSubalgebra ℚ (Matrix.ToLieAlgebra ℚ A),
          h ≤ k → IsLieAbelian k → k = h) ∧
        ∃ θ : h ≃ₗ[ℚ] Module.Dual ℚ V,
          (∀ i, ∃ t : h,
            (t : Matrix.ToLieAlgebra ℚ A) =
              rationalSerreGenerator A (CartanMatrix.Generators.H i) ∧
            θ t = c ⟨b i, hb i⟩) ∧
          (⨆ a : V, (LieModule.weightSpace (Matrix.ToLieAlgebra ℚ A)
            (fun t : h ↦ θ t a)).toSubmodule) = ⊤ ∧
          (∀ a : V, a ≠ 0 →
            ((LieModule.weightSpace (Matrix.ToLieAlgebra ℚ A)
              (fun t : h ↦ θ t a)).toSubmodule ≠ ⊥ ↔ a ∈ R)) ∧
          (∀ a : R, Module.finrank ℚ
            (LieModule.weightSpace (Matrix.ToLieAlgebra ℚ A) (fun t : h ↦ θ t a)) = 1) ∧
          (∀ a : R, ∃ (t : h) (e f : Matrix.ToLieAlgebra ℚ A),
            θ t = c a ∧
            e ∈ LieModule.weightSpace (Matrix.ToLieAlgebra ℚ A) (fun s : h ↦ θ s a) ∧
            f ∈ LieModule.weightSpace (Matrix.ToLieAlgebra ℚ A) (fun s : h ↦ θ s (-a)) ∧
            ⁅e, f⁆ = (t : Matrix.ToLieAlgebra ℚ A) ∧ θ t a = 2)) ∧
      (r = 0 → Subsingleton (Matrix.ToLieAlgebra ℚ A))) := by
  sorry

end LieAlgebra
