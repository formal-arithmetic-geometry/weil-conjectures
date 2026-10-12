module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.Biproducts

@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
namespace AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The coordinate morphism admits a kernel fork with source G(z-1).

Source: the two-chart calculation in
`dag/nodes/sec-picard-framework/lem-sc-p1-proj-coordinate-short-exact.json`,
proof steps 1 and 2, and Stacks Project, Tag 01MN for the twisting sheaves.
(blueprint: lem-sc-p1-proj-coordinate-kernel-fork).

Proof: Write μ_i(d) for G whiskered with multiplication by x_i from O(d)
to O(d+1). Define f by its two components -μ_1(z-1) and μ_0(z-1),
transporting (z-1)+1 to z. Commutativity of coordinate multiplication implies
f followed by (μ_0(z), μ_1(z)) is zero. On D+(x_0), multiplication by x_0
is invertible for every twist, and remains invertible after tensoring with G.
For a morphism (a,b) killed by the quotient map, set t=μ_0(z-1)^{-1} b.
The equation μ_0(z)a+μ_1(z)b=0 and commutativity give a=-μ_1(z-1)t;
t is unique because its second component is b. On D+(x_1), instead set
t=-μ_1(z-1)^{-1} a; the same equation gives b=μ_0(z-1)t, uniquely.
These local factorizations agree on overlaps by uniqueness. The sheaf gluing
property therefore gives a unique global factorization for every kernel fork,
which is exactly the universal property IsLimit. No arbitrary witness is
used to define f: it is the displayed binary biproduct lift. Tensoring needs
no flatness because the local inverses still exist. The calculation covers
the zero module, modules with torsion, characteristic two, and every integer z.
-/
theorem exists_proj_coordinate_kernel_fork
    (k : Type u) [Field k]
    (G : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules) (z : ℤ) :
    ∃ (f : G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (z - 1) ⟶
        (G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) z) ⊞
        (G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) z))
      (h : f ≫ biprod.desc
        (G ◁ Proj.twistMul z (MvPolynomial.X_mem_homogeneousSubmodule_one k (0 : Fin 2)))
        (G ◁ Proj.twistMul z (MvPolynomial.X_mem_homogeneousSubmodule_one k (1 : Fin 2))) = 0),
      Nonempty (IsLimit (KernelFork.ofι f h)) := by
  sorry

end AlgebraicGeometry
