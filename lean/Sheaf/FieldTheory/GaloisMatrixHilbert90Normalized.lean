module
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.LocallyConstant.Basic

/-! Normalized locally constant matrix cocycles; the nontrivial finite-descent step remains.
(blueprint: lem-sc-galois-matrix-hilbert90-normalized) -/
@[expose] public section
universe u
namespace Field
/-- Matrix Hilbert 90 in positive dimension. A locally constant cocycle factors through a
finite Galois quotient. On the resulting finite-dimensional vector space, sum the twisted
Galois translates of each vector. The cocycle law makes these sums invariant. Linear
independence of distinct field automorphisms shows that the invariant sums span: a linear
functional killing them would have all coefficients zero, including its coefficient at the
identity, hence would itself be zero. Extracting a basis of invariant vectors and putting
its vectors into columns gives the required invertible matrix.
(blueprint: lem-sc-galois-matrix-hilbert90-normalized) -/
theorem exists_galois_matrix_invariant_basis_normalized (K : Type u) [Field K] (n : ℕ)
    (b : Gal(SeparableClosure K/K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    (hb : IsLocallyConstant b)
    (hn : n ≠ 0)
    (hcoc : ∀ g h, b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) = b (g * h)) :
    ∃ t : Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K),
      ∀ g, b g * Matrix.GeneralLinearGroup.map g.toRingHom t = t := by sorry
end Field
