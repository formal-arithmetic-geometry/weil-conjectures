module

public import Mathlib.AlgebraicGeometry.Group.Abelian
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Mathlib.LinearAlgebra.TensorProduct.Basic
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor

/-! # Endomorphism span of symmetric ample invertible modules

Source: Raynaud, Faisceaux amples sur les schemas en groupes, Proposition XI 1.14,
p. 170; the agent reconstruction uses Milne, Abelian Varieties, I sections 8--14
and II Lemma 1.3 (blueprint: lem-sfb-abelian-symmetric-ample-endomorphism-span).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- A positive tensor power of any symmetric ample invertible module is a finite,
nonempty tensor product of endomorphism pullbacks of a fixed symmetric ample module.
Source: Raynaud, Proposition XI 1.14, p. 170; reconstructed from Milne, Abelian
Varieties, I sections 8--14 and II Lemma 1.3
(blueprint: lem-sfb-abelian-symmetric-ample-endomorphism-span).

Proof:
1. By lem-sfb-polarization-calculus-over-field, set lambda = phi_L and
u = lambda^{-1} phi_M in End_k(A) tensor Q, with Rosati involution dagger.
By lem-sfb-ample-polarization-positive-spectrum, u is dagger-fixed and Q[u]
is a finite-dimensional commutative algebra split over R, with u strictly positive
in every real coordinate.
2. By lem-sfb-split-real-algebra-positive-squares, write u as a nonempty sum
of squares q_j^2 in Q[u]. Rational linearity and dagger(u) = u imply that dagger
fixes each polynomial q_j in u, so u = sum dagger(q_j) q_j.
3. Clear all finitely many denominators in End_k(A) tensor Q, using
def-weil-pbc-module-tensor-product: for a positive integer D there are actual
endomorphisms b_j with rational images D q_j. Thus sum dagger(b_j) b_j = D^2 u.
4. Form N = M^{tensor D^2} tensor (tensor_j b_j^* L)^{-1}. Group homomorphisms
commute with inversion, so symmetry of L and M, pullback composition
(def-pc-module-pullback), and tensor compatibility
(lem-weil-pbc-module-pullback-tensor) make N symmetric. Additivity and the
pullback formula of lem-sfb-polarization-calculus-over-field give phi_N = 0
in rational homomorphisms. Its symmetric-kernel clause gives N^{tensor 2} = O_A
up to isomorphism. Cancel tensor inverses and repeat each b_j twice to obtain
a = 2 D^2 and the required nonempty finite tensor product. -/
theorem IsAbelianVariety.symmetric_ample_endomorphism_span
    {k : Type u} [Field k] (A : Over (Spec (.of k)))
    [GrpObj A] [IsAbelianVariety A]
    (L M : A.left.Modules) [L.IsInvertible] [M.IsInvertible]
    (hLsym : Nonempty ((Scheme.Modules.tensorPullback (ι[A]).left).obj L ≅ L))
    (hMsym : Nonempty ((Scheme.Modules.tensorPullback (ι[A]).left).obj M ≅ M))
    (hLamp : Scheme.Modules.IsAmple A.left L)
    (hMamp : Scheme.Modules.IsAmple A.left M) :
    ∃ a : ℕ, 1 ≤ a ∧ ∃ r : ℕ, 1 ≤ r ∧ ∃ b : Fin r → (A ⟶ A),
      (∀ j : Fin r, IsMonHom (b j)) ∧
      Nonempty (M.tensorPow a ≅
        (List.ofFn (fun j : Fin r ↦ (Scheme.Modules.tensorPullback (b j).left).obj L)).foldr
          (fun P Q ↦ P ⊗ Q) (𝟙_ A.left.Modules)) := by
  sorry

end AlgebraicGeometry
