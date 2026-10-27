module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Eigenspace.Pi

/-! # Stable p-power spans of commuting matrices

Source: Milne, Algebraic Groups (2017), Proposition 17.80, printed p.378, and the
restricted operation preceding Proposition 11.36, p.223
(blueprint: lem-sfb-commuting-p-power-stable-image).

The stable-span formulation and its imperfect-field descent are the agent-supplied
linear-algebra expansion recorded in the DAG, rather than a theorem printed in Milne.
Scalar extension is the actual tensor-to-matrix map, built from Mathlib's base-change
map and its finite-product tensor equivalences. Diagonalizability is expressed by
conjugation by a unit matrix, with no perfectness assumption on the base field.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Matrix

/-- The span of the `p ^ r`th powers of matrices in `W`, including `r = 0`.
Source: the stable-span expansion of Milne, Proposition 17.80, p.378
(blueprint: lem-sfb-commuting-p-power-stable-image). -/
def pPowerSpan {k : Type u} [Field k] {n : ℕ}
    (W : Submodule k (Matrix (Fin n) (Fin n) k)) (p r : ℕ) :
    Submodule k (Matrix (Fin n) (Fin n) k) :=
  Submodule.span k ((fun X : Matrix (Fin n) (Fin n) k ↦ X ^ (p ^ r)) '' (W : Set _))

/-- The canonical map `K ⊗[k] W → Mat_n(K)`, sending `a ⊗ X` to the matrix
whose `(i,j)` entry is `a * algebraMap k K (X i j)`. It is the base change of the
subspace inclusion followed by the tensor equivalences for the two finite indices.
Source: the scalar-extension identification in the expansion of Milne,
Proposition 17.80, p.378 (blueprint: lem-sfb-commuting-p-power-stable-image). -/
def scalarExtensionMap {k : Type u} [Field k] (K : Type v) [Field K] [Algebra k K]
    {n : ℕ} (W : Submodule k (Matrix (Fin n) (Fin n) k)) :
    K ⊗[k] W →ₗ[K] Matrix (Fin n) (Fin n) K :=
  ((LinearMap.pi fun i : Fin n ↦
      (TensorProduct.piScalarRight k K K (Fin n)).toLinearMap.comp (LinearMap.proj i)).comp
    (TensorProduct.piRight k K K (fun _ : Fin n ↦ Fin n → k)).toLinearMap).comp
      (LinearMap.baseChange K W.subtype)

/-- Stable p-power spans commute with arbitrary scalar extension and are precisely
the geometrically diagonalizable matrices of a commuting p-power-closed matrix space.
Source: the agent-supplied expansion of Milne, Proposition 17.80, printed p.378;
restricted powers before Proposition 11.36, p.223; additive Jordan decomposition
preceding Proposition 17.74, pp.376--377
(blueprint: lem-sfb-commuting-p-power-stable-image).

Proof plan, following the seven DAG steps:
1. Extend a basis of any subspace to a basis of the matrix space. After tensoring,
   the original basis vectors remain independent and span its scalar extension.
   The remaining coordinate functionals test membership of a matrix defined over k.
   This proves injectivity of the canonical tensor map and descent of membership.
2. For commuting matrices, the characteristic-p binomial formula gives
   `(sum a_i X_i)^(p^r) = sum a_i^(p^r) X_i^(p^r)`. All scalar-extended matrices
   still commute. This proves one inclusion of the scalar-extension identity;
   taking `1 ⊗ X` proves the other. For r = 0 this is the identity on W.
3. Closure under pth powers implies W_(r+1) is contained in W_r, and step 2 gives
   W_(r+1) = span of pth powers of W_r. Strict inclusions lower finite dimension,
   so equality occurs and the recurrence propagates it. Its stable value is p-closed.
4. Work over L, which is algebraically closed and hence perfect. Apply
   lem-sfb-additive-jordan-linear-compatibility to a finite basis of L ⊗ W.
   Sufficiently large p-power iterates kill all nilpotent parts, leaving commuting
   diagonalizable powers. By step 2 these powers span L ⊗ W_r.
5. For diagonalizable operators the generalized eigenspaces are ordinary eigenspaces.
   Apply lem-sfb-commuting-joint-generalized-eigenspaces-span to the commuting powers.
   The joint eigenspaces span, so every linear combination is diagonalizable.
   The empty family gives the zero subspace.
6. Conversely, for a diagonalizable X in L ⊗ W, span its iterated p-powers to obtain E.
   In an eigenbasis all elements of E are diagonal, so the p-power map is injective.
   On a basis of E, taking pth roots of coefficients in L proves independence of the
   pth powers and their spanning property, hence surjectivity of the p-power map on E.
   Thus X is a p^rth power in E for every r and lies in every L ⊗ W_r.
7. At an index beyond both stabilization and the bound in step 4, steps 5 and 6
   identify L ⊗ W_infty with the diagonalizable subset of L ⊗ W. The coordinate
   membership test of step 1 descends this equivalence to matrices in W.
   The cases W = 0 and n = 1 require no nonzero-vector or dimension assumption. -/
theorem commuting_p_power_stable_image
    (k : Type u) [Field k] (L : Type v) [Field L] [Algebra k L] [IsAlgClosure k L]
    (p : ℕ) [CharP k p] (hp : 0 < p) (n : ℕ) (hn : 1 ≤ n)
    (W : Submodule k (Matrix (Fin n) (Fin n) k))
    (hcomm : ∀ X ∈ W, ∀ Y ∈ W, X * Y = Y * X)
    (hpow : ∀ X ∈ W, X ^ p ∈ W) :
    (∀ (K : Type (max u w)) [Field K] [Algebra k K],
      Function.Injective (scalarExtensionMap K W) ∧
        ∀ r : ℕ,
          LinearMap.range (scalarExtensionMap K (pPowerSpan W p r)) =
            Submodule.span K
              ((fun Y : Matrix (Fin n) (Fin n) K ↦ Y ^ (p ^ r)) ''
                (LinearMap.range (scalarExtensionMap K W) : Set _))) ∧
    Antitone (pPowerSpan W p) ∧
    ∃ W_infty : Submodule k (Matrix (Fin n) (Fin n) k),
      W_infty ≤ W ∧
      (∃ R : ℕ, ∀ r : ℕ, R ≤ r → pPowerSpan W p r = W_infty) ∧
      (∀ X ∈ W_infty, X ^ p ∈ W_infty) ∧
      (∀ X : Matrix (Fin n) (Fin n) k,
        X ∈ W_infty ↔ X ∈ W ∧
          ∃ (P : (Matrix (Fin n) (Fin n) L)ˣ) (d : Fin n → L),
            (↑P⁻¹ : Matrix (Fin n) (Fin n) L) * X.map (algebraMap k L) *
              (↑P : Matrix (Fin n) (Fin n) L) = Matrix.diagonal d) ∧
      (∀ Y : Matrix (Fin n) (Fin n) L,
        Y ∈ LinearMap.range (scalarExtensionMap L W_infty) ↔
          Y ∈ LinearMap.range (scalarExtensionMap L W) ∧
            ∃ (P : (Matrix (Fin n) (Fin n) L)ˣ) (d : Fin n → L),
              (↑P⁻¹ : Matrix (Fin n) (Fin n) L) * Y *
                (↑P : Matrix (Fin n) (Fin n) L) = Matrix.diagonal d) := by
  sorry

end Matrix
