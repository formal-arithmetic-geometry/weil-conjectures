module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Representation
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.CategoryTheory.Monoidal.Grp
import Sheaf.AlgebraicGeometry.FreeQuotientGrassmannProjective
import WeilConjectures.AlgebraicGeometry.AffineFreeMapZeroLocus
import WeilConjectures.AlgebraicGeometry.LocalClosedLocusGluing
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.MultiplicativeTypeLargestSubtorus
import Sheaf.AlgebraicGeometry.StandardGroupSchemes

/-! # Torus-stable simple submodules of normalized operator algebras

Source: auxiliary argument from Milne, Algebraic Groups (2017), Propositions 7.29--7.30,
printed p.146, and Borel fixed point Corollary 17.3, printed p.353
(blueprint: lem-sfb-torus-normalized-simple-submodule).

The representation is a morphism to the existing general linear group scheme, with
IsMonHom expressing compatibility with the group law. The chosen finite basis identifies
GL(M) with the matrix group scheme. Scalar extensions use R tensor M, canonically
identified with M tensor R by symmetry. The span of the base-changed operators is precisely
the image of R tensor B in End_R(R tensor M); over a field this image is faithful.
-/

set_option autoImplicit false

@[expose] public section

universe u

open CategoryTheory
open scoped TensorProduct MonObj

namespace AlgebraicGeometry

/-- A split torus normalizing a unital operator algebra stabilizes a simple submodule.
Source: auxiliary argument from Milne, Propositions 7.29--7.30, p.146, and
Corollary 17.3, p.353 (blueprint: lem-sfb-torus-normalized-simple-submodule).

Proof:
1. The dimensions of nonzero B-stable subspaces form a nonempty finite set, since M
itself is stable. Choose its minimum d and a subspace W of dimension d. Every B-stable
subspace of dimension d is simple by minimality.
2. The free-quotient Grassmannian of rank dim(M)-d parametrizes rank-d subbundles by
its universal kernel. Locally a quotient matrix is [I A], whose kernel is (-Av,v),
so the sequence is locally split and remains exact under every base change. This
includes d=dim(M), where the Grassmannian is Spec k.
3. Choose a basis of B, which is finite-dimensional inside End_k(M). The maps from
the universal kernel to the universal quotient induced by these basis operators
vanish on a closed subscheme X. Affine free-map zero loci and local closed-locus
gluing construct X with its scheme structure; its points over any test scheme are
exactly the B-stable rank-d subbundles.
4. The Grassmannian is projective, hence proper. Closed immersions and composites
are proper, so X is proper and finite type. W supplies a k-point, making X nonempty.
5. The representation acts on the Grassmannian by L to gL. Normalization gives
b(g l)=g((g inverse b g)l), so this action preserves the universal closed locus X
over every coefficient algebra. The factorization criterion gives an action on X;
the action identities follow from those of the representation and uniqueness.
6. The split torus is smooth and connected by the largest-subtorus theorem, affine
and finite type by its Laurent coordinates, and solvable because it is commutative.
Apply the solvable proper fixed-point theorem to X, retaining its possible nonreduced
structure. Obtain a k-point fixed over every k-algebra. This includes rank zero.
7. Its classified subspace U has dimension d>0, is B-stable and simple by step 1.
Equality of its points over R means equality of the corresponding subbundles, giving
exactly the asserted torus stability after scalar extension. No semisimplicity of M
is used. -/
theorem exists_torus_stable_simple_submodule
    {k : Type u} [Field k] [IsAlgClosed k]
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [GrpObj (T.asOver (Spec (.of k)))]
    (r : ℕ) (hT : Nonempty (Grp.mk (T.asOver (Spec (.of k))) ≅
      MultiplicativeType.splitTorus k r))
    (M : Type u) [AddCommGroup M] [Module k M] [FiniteDimensional k M] [Nontrivial M]
    (τ : GeneralLinearGroup.RationalHom (T.asOver (Spec (.of k)))
      (ULift.{u} (Fin (Module.finrank k M)))) [IsMonHom τ]
    (B : Subalgebra k (Module.End k M))
    (hnormalizes : ∀ (R : Type u) [CommRing R] [Algebra k R]
      (t : points (T.asOver (Spec (.of k))) R),
      (Submodule.span R (Set.range (fun b : B ↦ (b : Module.End k M).baseChange R))).map
        ((Matrix.GeneralLinearGroup.toLin'
          (((Module.finBasis k M).reindex Equiv.ulift.symm).baseChange R)
          (τ.points R t)).toLinearEquiv).conj.toLinearMap =
      Submodule.span R (Set.range (fun b : B ↦ (b : Module.End k M).baseChange R))) :
    ∃ U : Submodule k M,
      U ≠ ⊥ ∧
      (∀ (b : B) (m : M), m ∈ U → (b : Module.End k M) m ∈ U) ∧
      (∀ W : Submodule k M, W ≤ U →
        (∀ (b : B) (m : M), m ∈ W → (b : Module.End k M) m ∈ W) →
        W = ⊥ ∨ W = U) ∧
      ∀ (R : Type u) [CommRing R] [Algebra k R]
        (t : points (T.asOver (Spec (.of k))) R),
        (U.baseChange R).map ((Matrix.GeneralLinearGroup.toLin'
          (((Module.finBasis k M).reindex Equiv.ulift.symm).baseChange R)
          (τ.points R t)).toLinearEquiv).toLinearMap = U.baseChange R := by
  sorry

end AlgebraicGeometry
