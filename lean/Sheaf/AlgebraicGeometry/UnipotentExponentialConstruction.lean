module

public import Sheaf.AlgebraicGeometry.FiniteVectorGroup
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie
public import WeilConjectures.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary
import Sheaf.AlgebraicGeometry.AffineGroupTensorReconstruction
import Mathlib.RingTheory.Nilpotent.Exp

/-! # The unipotent exponential: construction and functoriality

Source: Milne, Algebraic Groups (2017), 10.7--10.8 and 14.28--14.31,
printed pp.188--189 and 287--289.
(blueprint: lem-sfb-unipotent-exponential-construction)

The tangent space is the existing GrpObj.Lie, identified with schemeTangentSpace at the
identity by GrpObj.lieIdentityTangentEquiv. The embedding into U_n is a closed embedding
into the existing GL_n with upper unitriangular matrices on every algebra's points.
The additive vector scheme is written in an arbitrary finite basis; no basis is fixed
as an extra hypothesis on G. No inverse to the exponential is asserted.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped TensorProduct MonObj

namespace AlgebraicGeometry.UnipotentExponential

variable {k : Type u} [Field k]
variable {G : Over (Spec (.of k))} [GrpObj G]

/-- The image of i lies in the upper unitriangular group, over every test algebra.
Source: Milne 14.3 and 14.31 (blueprint: lem-sfb-unipotent-exponential-construction). -/
def IsUnitriangular {n : ℕ} (i : G ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k) : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra k R] (x : points G R),
    (∀ a : Fin n,
      (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k R (x ≫ i)).val ⟨a⟩ ⟨a⟩ = 1) ∧
    (∀ a b : Fin n, b < a →
      (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k R (x ≫ i)).val ⟨a⟩ ⟨b⟩ = 0)

/-- The scalar extension of di, with its tensor of matrices identified entrywise with
matrices over R. This uses only the existing differential and canonical tensor maps.
Source: Milne 10.8 and 14.31 (blueprint: lem-sfb-unipotent-exponential-construction). -/
def matrixDifferential {n : ℕ}
    (i : G ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k) [IsMonHom i]
    (R : Type u) [CommRing R] [Algebra k R] :
    R ⊗[k] GrpObj.Lie G →ₗ[R] Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n)) R :=
  letI : LieRing (Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n)) k) :=
    LieRing.ofAssociativeRing
  LinearMap.pi (fun a ↦ LinearMap.pi (fun b ↦
    (TensorProduct.AlgebraTensorModule.rid k R R).toLinearMap ∘ₗ
      ((LinearMap.proj b ∘ₗ LinearMap.proj a ∘ₗ
        (GeneralLinearGroup.RationalHom.differential i).toLinearMap).baseChange R)))

/-- The matrix formula characterizing an exponential morphism in the chosen vector coordinates.
The factorial coefficients are inverted in k and then act on matrices over R.
Source: Milne 14.28--14.31 (blueprint: lem-sfb-unipotent-exponential-construction). -/
def IsExponential {n d : ℕ}
    (i : G ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k) [IsMonHom i]
    (b : Module.Basis (Fin d) k (GrpObj.Lie G))
    (E : FiniteVectorGroup.scheme k d ⟶ G) : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra k R] (X : R ⊗[k] GrpObj.Lie G),
    (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k R
      (FiniteVectorGroup.point b R X ≫ E ≫ i)).val =
        ∑ r ∈ Finset.range n, ((r.factorial : k)⁻¹) • matrixDifferential i R X ^ r

/-- The tangent space is finite-dimensional and scalar extension identifies it with precisely
those strictly upper triangular matrices whose dual-number point belongs to G.
Source: Milne 10.7--10.8 and 14.31
(blueprint: lem-sfb-unipotent-exponential-construction).
Proof (step 1): write G as the polynomial quotient of unitriangular coordinates by J.
Every equation vanishes at the identity, so substitution epsilon X leaves epsilon times
its linear part. These linear forms cut out the tangent space. Choose a basis of their
span and row-reduce the finite coefficient matrix over k. The pivots remain units in
every k-algebra, including the zero algebra. The free-variable basis therefore base-changes
to the kernel over R. The differential of the closed immersion is injective and its image
has zero diagonal and lower entries. This also proves finite-dimensionality over k. -/
theorem tangent_description [CharZero k] [IsAffine G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    {n : ℕ} (hn : 0 < n)
    (i : G ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k) [IsClosedSubgroupScheme i]
    (hi : IsUnitriangular i) :
    FiniteDimensional k (GrpObj.Lie G) ∧
    ∀ (R : Type u) [CommRing R] [Algebra k R],
      Function.Injective (matrixDifferential i R) ∧
      (∀ M : Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n)) R,
        M ∈ LinearMap.range (matrixDifferential i R) ↔
          ∃ x : points G (DualNumber R),
            GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k (DualNumber R)
              (x ≫ i) = GeneralLinearGroup.dualUnit M) ∧
      (∀ (X : R ⊗[k] GrpObj.Lie G) (a b : Fin n), b ≤ a →
        matrixDifferential i R X ⟨a⟩ ⟨b⟩ = 0) := by
  sorry

/-- The finite matrix exponential defines the unique morphism from the additive tangent scheme
having the specified matrices on all algebra-valued points.
Source: Milne 14.31, printed p.288
(blueprint: lem-sfb-unipotent-exponential-construction).
Proof (steps 1--5): a product of n strictly upper triangular matrices vanishes. Every finite
rational representation of G has a flag with trivial one-dimensional quotients: use
lem-sfb-unitriangular-subgroup-rational-fixed-vector, descend the coaction to the quotient
using lem-sfb-rational-representation-comodule-dictionary, and induct on dimension.
Its differential is strictly upper triangular in the resulting basis, even over R, by
substitution into the matrix coordinate functions. Exponentiate each differential using
lem-sfb-nilpotent-exponential-identities. Expansion over dual numbers gives the tensor
rule D_(V tensor W)=D_V tensor 1 + 1 tensor D_W. Its summands commute and are nilpotent,
so their exponential is the tensor of the exponentials. The trivial differential is zero;
equivariant maps intertwine the finite sums. Thus lem-sfb-affine-group-tensor-reconstruction
gives a unique point g_X. Its given representation is precisely the displayed finite sum.
The construction commutes with coefficient maps by the same uniqueness. Evaluate it at
the universal vector over k[t_1,...,t_d] to obtain the actual morphism. Polynomial evaluation
recovers g_X at every point; injectivity of the closed immersion gives characterization
and uniqueness. The empty basis uses the universal algebra k and its zero vector. -/
theorem construction [CharZero k] [IsAffine G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    {n : ℕ} (hn : 0 < n)
    (i : G ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k) [IsClosedSubgroupScheme i]
    (hi : IsUnitriangular i) {d : ℕ} (b : Module.Basis (Fin d) k (GrpObj.Lie G)) :
    ∃! E : FiniteVectorGroup.scheme k d ⟶ G, IsExponential i b E := by
  sorry

/-- The exponential is natural in the coefficient algebra.
Source: Milne 14.31, printed p.288
(blueprint: lem-sfb-unipotent-exponential-construction).
Proof (step 5): base change carries each differential matrix entry and each factorial
coefficient to its image. The finite sum is therefore preserved. The characterized
points agree after composing with i, and its injectivity on points proves the equality.
Equivalently, the constructed scheme morphism commutes with precomposition by Spec alpha. -/
theorem coefficients_natural [CharZero k] [IsAffine G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    {n : ℕ} (hn : 0 < n)
    (i : G ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k) [IsClosedSubgroupScheme i]
    (hi : IsUnitriangular i) {d : ℕ} (b : Module.Basis (Fin d) k (GrpObj.Lie G))
    (E : FiniteVectorGroup.scheme k d ⟶ G) (hE : IsExponential i b E)
    (R S : Type u) [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]
    (α : R →ₐ[k] S) (X : R ⊗[k] GrpObj.Lie G) :
    points.map G α (FiniteVectorGroup.point b R X ≫ E) =
      FiniteVectorGroup.point b S (α.toLinearMap.rTensor (GrpObj.Lie G) X) ≫ E := by
  sorry

/-- Changing the unitriangular embedding gives the same exponential morphism.
Source: Milne 14.31, all-representations characterization, printed p.288
(blueprint: lem-sfb-unipotent-exponential-construction).
Proof (step 6): reconstruction characterizes the point by its exponential action in every
rational representation, independently of an embedding. Apply that characterization to
j as a representation to obtain its finite-sum formula, using nilpotence of size m.
Both constructions give the same point in every algebra. Their universal points agree,
so their scheme morphisms agree. In the present formulation this says that the same E
satisfies the characterization for j. -/
theorem embedding_independent [CharZero k] [IsAffine G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (i : G ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k) [IsClosedSubgroupScheme i]
    (hi : IsUnitriangular i)
    (j : G ⟶ GeneralLinearGroup (ULift.{u} (Fin m)) k) [IsClosedSubgroupScheme j]
    (hj : IsUnitriangular j) {d : ℕ} (b : Module.Basis (Fin d) k (GrpObj.Lie G))
    (E : FiniteVectorGroup.scheme k d ⟶ G) (hE : IsExponential i b E) :
    IsExponential j b E := by
  sorry

/-- Exponentials commute with every homomorphism of the stated unipotent groups.
Source: Milne, naturality square before Proposition 14.32, printed p.289
(blueprint: lem-sfb-unipotent-exponential-construction).
Proof (step 6): for each representation s of H, composition on dual-number points gives
D_(s f)=D_s df. The all-representations characterization of the constructed exponential
therefore makes s(f(exp_G X)) and s(exp_H(df X)) the same finite exponential. Take s=j,
the closed unitriangular representation of H; its injectivity on R-points proves equality.
The differential here is the existing postcomposition map, with its actual scalar extension. -/
theorem hom_natural [CharZero k] [IsAffine G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    {H : Over (Spec (.of k))} [GrpObj H] [IsAffine H.left]
    [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (i : G ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k) [IsClosedSubgroupScheme i]
    (hi : IsUnitriangular i)
    (j : H ⟶ GeneralLinearGroup (ULift.{u} (Fin m)) k) [IsClosedSubgroupScheme j]
    (hj : IsUnitriangular j)
    {d e : ℕ} (b : Module.Basis (Fin d) k (GrpObj.Lie G))
    (c : Module.Basis (Fin e) k (GrpObj.Lie H))
    (E : FiniteVectorGroup.scheme k d ⟶ G) (hE : IsExponential i b E)
    (F : FiniteVectorGroup.scheme k e ⟶ H) (hF : IsExponential j c F)
    (f : G ⟶ H) [IsMonHom f]
    (R : Type u) [CommRing R] [Algebra k R] (X : R ⊗[k] GrpObj.Lie G) :
    (FiniteVectorGroup.point b R X ≫ E) ≫ f =
      FiniteVectorGroup.point c R ((GrpObj.differential f).toLinearMap.baseChange R X) ≫ F := by
  sorry

/-- Commuting tangent matrices exponentiate additively into the group law of G.
Source: Milne 14.31, formula (93), printed p.288
(blueprint: lem-sfb-unipotent-exponential-construction).
Proof (step 7): the differential carries X+Y to the sum A+B. All three matrices are strictly
upper triangular and hence nilpotent. For commuting A and B, the finite exponential identity
of lem-sfb-nilpotent-exponential-identities gives exp(A+B)=exp(A)exp(B). The defining formula
for E and multiplicativity of i give equality of the two points after composition with i.
Its injectivity proves the claim. For n=1 all tangent matrices are zero. No inverse to E
is used or constructed. -/
theorem commuting_add [CharZero k] [IsAffine G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    {n : ℕ} (hn : 0 < n)
    (i : G ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k) [IsClosedSubgroupScheme i]
    (hi : IsUnitriangular i) {d : ℕ} (b : Module.Basis (Fin d) k (GrpObj.Lie G))
    (E : FiniteVectorGroup.scheme k d ⟶ G) (hE : IsExponential i b E)
    (R : Type u) [CommRing R] [Algebra k R] (X Y : R ⊗[k] GrpObj.Lie G)
    (hXY : Commute (matrixDifferential i R X) (matrixDifferential i R Y)) :
    FiniteVectorGroup.point b R (X + Y) ≫ E =
      (FiniteVectorGroup.point b R X ≫ E) * (FiniteVectorGroup.point b R Y ≫ E) := by
  sorry

end AlgebraicGeometry.UnipotentExponential
