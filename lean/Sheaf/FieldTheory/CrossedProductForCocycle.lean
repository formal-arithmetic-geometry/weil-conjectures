module

public import Sheaf.FieldTheory.BrauerScalarDefect

@[expose] public section

universe u

namespace Field

open scoped TensorProduct

/-- A prescribed continuous cocycle gives splitting and scalar-defect data.

Proof: write `G = Gal(Ksep/K)` and `c(g,h) = z(1,g,g*h)`. Equivariance and the
homogeneous cycle equation give
`c(g,h) * c(g*h,j) = g(c(h,j)) * c(g,h*j)`.
Since G is profinite, uncurry the iterated continuous cochain by the exponential law
for compact Hausdorff spaces. Its values are discrete, so c is locally constant with
finite image. A finite clopen cover gives an open normal subgroup N such that c is
constant on pairs of N-cosets. Shrink N to fix every value of c. Its fixed field L is
finite Galois over K, and c is inflated from a cocycle on Gamma = Gal(L/K) with values
in L-units.

On the L-space with basis indexed by Gamma define the monomial matrix B(g) by
`B(g) e_j = c(g,j) e_(g*j)`. Its nonzero coefficients are units, so it is invertible.
The cocycle equation gives `B(g) * g(B(h)) = c(g,h) * B(g*h)` on each basis vector.
No normalization is needed: the cocycle equation gives `c(1,j) = c(1,1)`, hence B(1)
is scalar. Thus `T_g(M) = B(g) * g(M) * B(g)^(-1)` is an actual semilinear action on
the matrix algebra, with T_1 the identity. Let A be its invariant K-subalgebra.

For completeness, finite Galois descent here is a vector-space argument. For any v
and a in L the sum over g of `g(a) * T_g(v)` is invariant. These invariant vectors
span over L: if an L-linear functional kills all such sums, linear independence of
the distinct field automorphisms forces it to kill T_1(v) = v for every v. Choose an
L-basis of invariant vectors. Invariant linear combinations have coefficients in K,
so it is also a K-basis of A. Therefore `L tensor_K A -> Matrix Gamma Gamma L` is an
algebra isomorphism. A is finite dimensional and simple: a nonzero ideal extends to
a nonzero ideal of the full matrix algebra, hence to the whole algebra; dimensions
then force the original ideal to be all of A. A central element becomes scalar after
extension, and invariance forces its scalar into K. Thus A is central simple.

Extend the splitting to Ksep and identify Gamma with Fin n for n = card Gamma > 0.
Inflate B along G -> Gamma; this is locally constant, and G acts on its coefficients
through Gamma. The monomial identity is exactly the required scalar-defect equation.
For a in A, invariance reads `g(e(1 tensor a)) = B(g)^(-1) * e(1 tensor a) * B(g)`,
which is the required descent equation. All objects are constructed from c.

Source: Stacks Project, Theorem 03R7, surjectivity argument, and Section 0DVG.
The explicit monomial matrices and descent argument fill in the construction omitted
by that sketch; this proof is written by an agent.
(blueprint: new-crossed-product-for-cocycle). -/
theorem exists_crossedProduct_data_for_cocycle (K : Type u) [Field K]
    (z : ContinuousCohomology.cocycles (galoisUnitsTopRep K) 2) :
    ∃ (A : CSA.{u, u} K) (n : ℕ) (hn : n ≠ 0)
      (e : (SeparableClosure K ⊗[K] A) ≃ₐ[SeparableClosure K]
        Matrix (Fin n) (Fin n) (SeparableClosure K))
      (b : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →
        Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K)),
      IsLocallyConstant b ∧
      (∀ (g : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : A),
        (e (1 ⊗ₜ[K] a)).map g =
          ((b g)⁻¹).val * e (1 ⊗ₜ[K] a) * (b g).val) ∧
      (∀ g h, b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) =
        Matrix.GeneralLinearGroup.scalar (Fin n) (galoisUnitsCocycleValue K z g h) *
          b (g * h)) := by
  sorry

end Field
