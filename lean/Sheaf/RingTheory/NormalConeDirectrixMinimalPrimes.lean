module

public import WeilConjectures.RingTheory.AssociatedGradedRing
public import WeilConjectures.RingTheory.GradedAlgebra.Standard
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# The polynomial vertex and minimal-prime components of a normal cone

Source: the filtered-algebra synthesis in the DAG, supported by Stacks Project,
Algebra, Tags 00IP, 00NZ and 00EW
(blueprint: lem-trf-normal-cone-directrix-minimal-primes).

The fibre is written with the residue field on the left of the tensor product.
The canonical component quotient is presented by its initial-form relations:
in degree n its kernel consists of the classes of elements of I^n intersect p.
The polynomial vertex quotient takes coefficients in B_0; the standard-grading
identification B_0 = k identifies its codomain with k[T_1,...,T_e].
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace Ideal

/-- The canonical action of R/I on R/m, given by the quotient factor map.
Source: the quotient construction in the DAG's filtered-algebra synthesis
(blueprint: lem-trf-normal-cone-directrix-minimal-primes). -/
@[instance_reducible]
noncomputable def normalConeResidueAlgebra {R : Type u} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) :
    Algebra (R ⧸ I) (IsLocalRing.ResidueField R) :=
  (Ideal.Quotient.factor hI).toAlgebra

/-- The normal-cone residue fibre, with its canonical quotient scalar action.
Source: the associated-graded tensor construction in the DAG's synthesis
(blueprint: lem-trf-normal-cone-directrix-minimal-primes). -/
noncomputable abbrev normalConeFibre {R : Type u} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) : Type u :=
  letI := normalConeResidueAlgebra I hI
  IsLocalRing.ResidueField R ⊗[R ⧸ I] associatedGraded I

/-- The tensor-product ring structure on the normal-cone fibre.
Source: the tensor construction in the DAG's synthesis
(blueprint: lem-trf-normal-cone-directrix-minimal-primes). -/
noncomputable instance normalConeFibreCommRing {R : Type u} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) :
    CommRing (normalConeFibre I hI) :=
  letI := normalConeResidueAlgebra I hI
  inferInstanceAs (CommRing (IsLocalRing.ResidueField R ⊗[R ⧸ I] associatedGraded I))

/-- The canonical residue-field algebra structure on the fibre.
Source: the tensor construction in the DAG's synthesis
(blueprint: lem-trf-normal-cone-directrix-minimal-primes). -/
noncomputable instance normalConeFibreAlgebra {R : Type u} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) :
    Algebra (IsLocalRing.ResidueField R) (normalConeFibre I hI) :=
  letI := normalConeResidueAlgebra I hI
  inferInstanceAs
    (Algebra (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R ⧸ I] associatedGraded I))

/-- The residue-fibre initial class of a representative a in I^n.
Source: degreewise quotient calculation, step 3 of the DAG's synthesis
(blueprint: lem-trf-normal-cone-directrix-minimal-primes). -/
noncomputable def normalConeFibreClass {R : Type u} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) (n : ℕ) (a : (I ^ n : Ideal R)) :
    normalConeFibre I hI :=
  letI := normalConeResidueAlgebra I hI
  1 ⊗ₜ[R ⧸ I] DirectSum.of (associatedGradedPiece I) n (Submodule.Quotient.mk a)

/-- The initial-form relations presenting the canonical component quotient of the fibre.
For p contained in m, the degree-n quotient is (I^n+p)/(m*I^n+p), hence this
ideal is exactly the kernel of the canonical map to gr_(I mod p)(R/p) tensor k.
Indeed a representative x in I^n maps to zero precisely when x=b+a with
b in m*I^n and a in p; then a=x-b lies in I^n intersect p. Conversely every
such a maps to zero. The homogeneous kernels span the kernel additively and
form an ideal, so taking their ideal span changes nothing.
Source: step 3 of the DAG's filtered-algebra synthesis
(blueprint: lem-trf-normal-cone-directrix-minimal-primes). -/
noncomputable def normalConeFibreComponentRelations
    {R : Type u} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) (p : Ideal R) :
    Ideal (normalConeFibre I hI) :=
  Ideal.span {z | ∃ (n : ℕ) (a : (I ^ n : Ideal R)),
    a.val ∈ p ∧ z = normalConeFibreClass I hI n a}

/-- Every minimal-prime component contains the polynomial vertex of the flat normal cone.
The component map is the quotient by `normalConeFibreComponentRelations`, the concrete
initial-form presentation of the canonical map q_p. The vertex map applies the
canonical degree-zero projection to every polynomial coefficient. Its target is
B_0[T], canonically k[T], so its kernel is precisely ker(epsilon composed with theta).
The coefficient conditions say that theta preserves the total grading, assigning
degree one to each variable and degree d to a coefficient in the d-th piece of B.

Source: filtered-algebra synthesis in the DAG, supported by Stacks Project,
Algebra, Tags 00IP, 00NZ and 00EW
(blueprint: lem-trf-normal-cone-directrix-minimal-primes).

Proof: (1) Each G_j is finite over A=R/I by Noetherianity. It is an A-linear
retract of the flat direct sum G, so tensoring injections shows it is flat.
(2) Apply lem-weil-pbc-finite-flat-local-free to make every G_j finite free.
(3) The quotient-tensor calculation gives F_j=I^j/m*I^j and the component
quotient (I^j+p)/(m*I^j+p), with exactly the relations constructed above.
(4) Both kernels are homogeneous, so work with a homogeneous class h of degree n.
Degree zero is injective on the component quotient; for e=0 the vertex kills
all positive degrees. Otherwise a counterexample has n>0, e>0 and a
representative a in I^n intersect p. (5) The residue field contains Q and is
infinite. By lem-trf-infinite-field-top-form-direction, the nonzero vertex
polynomial H has a direction v with H(v) nonzero. Complete v to a basis and
apply the corresponding invertible linear substitution in the variables.
(6) Its T_1^n coefficient is the nonzero scalar H(v), since positive-degree
B coefficients have smaller variable degree. The polynomial is monic after
rescaling, so lem-weil-pbc-monic-polynomial-nonzerodivisor makes h regular on F.
(7) Multiplication by the initial class of a between finite free pieces of G
has an injective residue matrix. Lift a left inverse over k; its product with
the original matrix reduces to the identity, has unit determinant, and is
invertible by its adjugate. Thus multiplication is injective in every degree,
including rank-zero sources. (8) By lem-weil-pbc-krull-intersection-jacobson,
the I-adic filtration on R is separated. A nonzero b annihilated by a would
have a nonzero initial form killed by one of these injective maps. Hence a
is regular on R. (9) Since a lies in the minimal prime p, the theorem
lem-weil-pbc-reduced-zerodivisors-union-minimal-primes contradicts regularity.
(10) The homogeneous conclusion gives the kernel inclusion. The quotient
universal property descends the vertex map; it is surjective and graded
because the original vertex map is surjective and graded. -/
theorem normalCone_directrix_minimalPrimes
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Algebra ℚ R] [IsReduced R]
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R)
    [Module.Flat (R ⧸ I) (associatedGraded I)]
    {B : Type v} [CommRing B] [Algebra (IsLocalRing.ResidueField R) B]
    (𝒜 : ℕ → Submodule (IsLocalRing.ResidueField R) B)
    [GradedAlgebra 𝒜] [GradedAlgebra.IsStandard 𝒜]
    (e : ℕ) (θ : normalConeFibre I hI ≃ₐ[IsLocalRing.ResidueField R]
      MvPolynomial (Fin e) B)
    (hθ : ∀ (n : ℕ) (a : (I ^ n : Ideal R)) (b : Fin e →₀ ℕ),
      MvPolynomial.coeff b (θ (normalConeFibreClass I hI n a)) ∈ 𝒜 (n - b.degree) ∧
      (n < b.degree → MvPolynomial.coeff b (θ (normalConeFibreClass I hI n a)) = 0)) :
    ∀ p ∈ minimalPrimes R,
      RingHom.ker (Ideal.Quotient.mk (normalConeFibreComponentRelations I hI p)) ≤
        RingHom.ker
          ((MvPolynomial.map (GradedRing.projZeroRingHom' 𝒜)).comp θ.toRingHom) := by
  sorry

end Ideal
