module

public import Sheaf.Algebra.Lie.SplitSemisimpleRootDecomposition
public import Sheaf.Algebra.Lie.RationalHighestWeightModules
public import Mathlib.Algebra.Lie.BaseChange
import Sheaf.Algebra.Lie.PerfectLieHyperplaneCriterion
import Mathlib.Algebra.Lie.Sl2
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Mathlib.LinearAlgebra.Trace

/-!
# Classification of rational modules of a split semisimple Lie algebra

Source: Milne, Algebraic Groups (2017), Theorem 23.70, proof (a), (b), (d),
printed pp. 507–508; the independent highest-weight argument expanded in the DAG
(blueprint: lem-sfb-split-lie-module-classification).

All weight spaces below are ordinary simultaneous eigenspaces. Finite sums are
internal sums of invariant subspaces, each identified with a chosen highest-weight module.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w t

open scoped TensorProduct

namespace LieAlgebra

open Classical in
/-- Classification, scalar endomorphisms, and absolute simplicity of the chosen rational
highest-weight modules, together with the integral ordinary weight decomposition.

Source: Milne, Algebraic Groups (2017), Theorem 23.70, proof (a), (b), (d),
printed pp. 507–508; split highest-weight input from Serre, Complex Semisimple
Lie Algebras, Chapter VII, expanded as follows in the DAG
(blueprint: lem-sfb-split-lie-module-classification).

Proof plan:
1. The coroot brackets and root decomposition show that the Lie algebra is perfect,
including in rank zero. By `lem-sfb-perfect-lie-hyperplane-criterion`, complete
reducibility reduces to splitting simple invariant hyperplanes in arbitrary modules.
2. If the action is zero, use a linear complement. Otherwise its image is semisimple by
`lem-sfb-semisimple-lie-surjective-image`. Its faithful trace form is nondegenerate by
`lem-sfb-faithful-semisimple-trace-form`. For dual bases define the Casimir c = sum x_i x^i.
3. Trace cyclicity (`lem-pc-finite-dimensional-trace-cyclic`) proves invariance of the
trace form. Expanding in dual bases gives [z,c] = 0, and
`def-weil-endomorphism-trace` gives trace(c) = dim(image of the action).
4. Perfectness kills the one-dimensional quotient. Hence c maps into the hyperplane,
and its restriction has the same nonzero trace. Simplicity makes that restriction
injective and therefore invertible. Its inverse composed with c is an equivariant
retraction. Split its kernel and induct on dimension to obtain finite simple sums.
5. For a rational sl2 triple use `lem-sfb-sl2-invariant-complement` to reduce to a
simple summand. Over an algebraic closure take a last nonzero raising of an eigenvector.
`lem-sfb-sl2-primitive-lowering-string` makes its weight a nonnegative integer n.
The rational simultaneous kernel of H-n and E is nonzero by Gaussian elimination.
6. The lowering string spans a nonzero invariant subspace: the primitive formulas
and `lem-sfb-sl2-primitive-string-vanishing` show it ends at n. Simplicity and distinct
weights give a basis, so H is rationally diagonalizable with integral eigenvalues.
7. Apply this to the simple coroot triples. By
`lem-sfb-root-base-rational-integral-spans` they form a rational basis and every
coroot is an integral combination. Commuting rational spectral projections give
the finite ordinary weight decomposition, with every weight in P.
8. A maximal weight of a simple summand has a highest vector. The sl2 primitive
formula makes it dominant. Its cyclicity gives a surjection from the explicit
Verma module of `lem-sfb-verma-monomial-weight-basis`.
9. In that Verma module, finite-support interpolation extracts the top component.
Every proper invariant subspace has zero top component, so their sum is the unique
maximal proper submodule. All simple highest-weight quotients of the same weight
are therefore isomorphic, including arbitrary-dimensional ones. Apply this to the
chosen module from `lem-sfb-rational-highest-weight-modules`. The top space is a line.
10. The common positive-root kernel is Cartan invariant and decomposes into weights.
A nonzero vector of weight mu in it generates a quotient of the Verma module of mu.
Its weights lie below mu, whereas the chosen module's weights lie below lambda.
Thus lambda <= mu <= lambda. The kernel is precisely the highest-weight line.
11. Isomorphisms preserve this line and its weight, so distinct weights give
nonisomorphic modules. An endomorphism acts by a rational scalar on the line;
cyclicity makes it that scalar on the whole module, including the zero endomorphism.
12. For any field extension, tensor the finite rational weight decomposition.
Rational interpolation projectors still split every invariant subspace into weights.
The common positive-root kernel is the kernel of one finite rational matrix;
Gaussian elimination commutes with every field extension, so it remains the top line.
A maximal weight in a nonzero invariant subspace supplies a vector on that line.
Cyclicity then makes the subspace the entire scalar extension, which is nonzero.
13. Combine complete reducibility with the simple-module identification. The zero
module uses the empty sum. For the zero Lie algebra every subspace is invariant,
so simple modules are one-dimensional; the chosen vector identifies L(0) with Q.

The parameters P and D are specified by their defining membership equivalences,
and the chosen family L and vectors vtop are arbitrary choices satisfying the
highest-weight existence theorem. No choice of an unidentified object is made. -/
theorem split_lie_module_classification
    (g : Type u) [LieRing g] [LieAlgebra ℚ g] [FiniteDimensional ℚ g]
    [HasTrivialRadical ℚ g] (H : LieSubalgebra ℚ g) [IsLieAbelian H]
    (hmax : ∀ A : LieSubalgebra ℚ g, H ≤ A → IsLieAbelian A → A = H)
    (hsplit : ∀ h : H, (⨆ a : ℚ, (ad ℚ g (h : g)).eigenspace a) = ⊤)
    (R : Set (Module.Dual ℚ H))
    (hR : ∀ α : Module.Dual ℚ H, α ∈ R ↔
      α ≠ 0 ∧ LieModule.weightSpace g (α : H → ℚ) ≠ ⊥)
    (c : R → H)
    (hc : ∀ α : R,
      (c α : g) ∈ Submodule.span ℚ {z : g | ∃ x y : g,
        x ∈ LieModule.weightSpace g (α.1 : H → ℚ) ∧
        y ∈ LieModule.weightSpace g ((-α.1) : H → ℚ) ∧ ⁅x, y⁆ = z} ∧
      α.1 (c α) = 2)
    (Δ : Finset R) (b : Module.Basis Δ ℚ (Module.Dual ℚ H))
    (hb : ∀ i : Δ, b i = i.1.1)
    (hcoords : ∀ α : R,
      (∃ n : Δ → ℕ, α.1 = ∑ i : Δ, (n i : ℚ) • i.1.1) ∨
      (∃ n : Δ → ℕ, -α.1 = ∑ i : Δ, (n i : ℚ) • i.1.1))
    (P : Submodule ℤ (Module.Dual ℚ H))
    (hP : ∀ μ : Module.Dual ℚ H, μ ∈ P ↔
      ∀ α : R, ∃ n : ℤ, μ (c α) = (n : ℚ))
    (D : Set P) (hD : ∀ lam : P, lam ∈ D ↔
      ∀ i : Δ, 0 ≤ (lam : Module.Dual ℚ H) (c i))
    (L : D → Type v) [∀ lam : D, AddCommGroup (L lam)]
    [∀ lam : D, Module ℚ (L lam)] [∀ lam : D, LieRingModule g (L lam)]
    [∀ lam : D, LieModule ℚ g (L lam)]
    [∀ lam : D, FiniteDimensional ℚ (L lam)]
    [∀ lam : D, LieModule.IsIrreducible ℚ g (L lam)]
    (vtop : ∀ lam : D, L lam)
    (hvtop : ∀ lam : D, vtop lam ≠ 0 ∧
      (∀ h : H, ⁅(h : g), vtop lam⁆ = (lam.1 : Module.Dual ℚ H) h • vtop lam) ∧
      (∀ α : R, (∃ n : Δ → ℕ, α.1 = ∑ i : Δ, (n i : ℚ) • i.1.1) →
        ∀ x : g, x ∈ LieModule.weightSpace g (α.1 : H → ℚ) → ⁅x, vtop lam⁆ = 0) ∧
      LieSubmodule.lieSpan ℚ g ({vtop lam} : Set (L lam)) = ⊤) :
    (∀ (V : Type w) [AddCommGroup V] [Module ℚ V]
      [LieRingModule g V] [LieModule ℚ g V] [FiniteDimensional ℚ V],
      ∃ (n : ℕ) (lam : Fin n → D) (N : Fin n → LieSubmodule ℚ g V),
        DirectSum.IsInternal (fun i : Fin n ↦ (N i).toSubmodule) ∧
        (∀ i : Fin n, Nonempty (N i ≃ₗ⁅ℚ,g⁆ L (lam i)))) ∧
    (∀ lam mu : D, Nonempty (L lam ≃ₗ⁅ℚ,g⁆ L mu) ↔ lam = mu) ∧
    (∀ (lam : D) (f : L lam →ₗ⁅ℚ,g⁆ L lam),
      ∃ a : ℚ, ∀ m : L lam, f m = a • m) ∧
    (∀ (lam : D) (S : Type w) [AddCommGroup S] [Module ℚ S]
      [LieRingModule g S] [LieModule ℚ g S] [LieModule.IsIrreducible ℚ g S]
      (v : S), v ≠ 0 →
      (∀ h : H, ⁅(h : g), v⁆ = (lam.1 : Module.Dual ℚ H) h • v) →
      (∀ α : R, (∃ n : Δ → ℕ, α.1 = ∑ i : Δ, (n i : ℚ) • i.1.1) →
        ∀ x : g, x ∈ LieModule.weightSpace g (α.1 : H → ℚ) → ⁅x, v⁆ = 0) →
      Nonempty (S ≃ₗ⁅ℚ,g⁆ L lam)) ∧
    (∀ (lam : D) (K : Type t) [Field K] [Algebra ℚ K],
      LieModule.IsIrreducible K (K ⊗[ℚ] g) (K ⊗[ℚ] L lam)) ∧
    (∀ lam : D,
      Module.finrank ℚ (LieModule.weightSpace (L lam)
        ((lam.1 : Module.Dual ℚ H) : H → ℚ)) = 1 ∧
      (LieModule.weightSpace (L lam)
        ((lam.1 : Module.Dual ℚ H) : H → ℚ)).toSubmodule =
          Submodule.span ℚ {vtop lam} ∧
      ∀ m : L lam,
        (∀ α : R, (∃ n : Δ → ℕ, α.1 = ∑ i : Δ, (n i : ℚ) • i.1.1) →
          ∀ x : g, x ∈ LieModule.weightSpace g (α.1 : H → ℚ) → ⁅x, m⁆ = 0) →
        m ∈ Submodule.span ℚ {vtop lam}) ∧
    (∀ (V : Type w) [AddCommGroup V] [Module ℚ V]
      [LieRingModule g V] [LieModule ℚ g V] [FiniteDimensional ℚ V],
      ∃ Ω : Finset (Module.Dual ℚ H),
        (∀ μ ∈ Ω, μ ∈ P ∧ LieModule.weightSpace V (μ : H → ℚ) ≠ ⊥) ∧
        DirectSum.IsInternal (fun μ : Ω ↦
          (LieModule.weightSpace V (μ.1 : H → ℚ)).toSubmodule)) ∧
    (Subsingleton g →
      (∀ lam : D, ∃ e : L lam ≃ₗ[ℚ] ℚ, e (vtop lam) = 1 ∧
        ∀ (x : g) (m : L lam), ⁅x, m⁆ = 0) ∧
      ∀ (S : Type w) [AddCommGroup S] [Module ℚ S]
        [LieRingModule g S] [LieModule ℚ g S] [LieModule.IsIrreducible ℚ g S],
        Nonempty (S ≃ₗ[ℚ] ℚ)) := by
  sorry

end LieAlgebra
