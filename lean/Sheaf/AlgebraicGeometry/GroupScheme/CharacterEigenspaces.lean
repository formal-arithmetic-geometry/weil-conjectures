module

public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite

/-!+# Independence of character eigenspaces

Source: Milne, Algebraic Groups (2017), Chapter 4(g), Proposition 4.22,
Corollary 4.24 and Theorem 4.25, printed pp.92--94.
(blueprint: lem-sfb-character-eigenspaces-independent)

The representation is a homomorphism to the existing general linear group scheme,
after choosing a finite basis. Its action on A tensor V is the actual matrix action
transported along the base-changed basis. Empty bases, and thus V = 0, are included.
Eigenspaces are intersections of equalizers over all test algebras and all points.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.CharacterEigenspaces

variable {k : Type u} [Field k] {n : Type u} [Fintype n] [DecidableEq n]
variable {V : Type v} [AddCommGroup V] [Module k V]
variable {G : Over (Spec (.of k))} [GrpObj G]

/-- Action on the scalar extension, using the chosen basis and the canonical GL point
equivalence. Source: Milne, Chapter 4(g), formula (27), p.92
(blueprint: lem-sfb-character-eigenspaces-independent). -/
def action (b : Module.Basis n k V) (r : G ⟶ GeneralLinearGroup n k)
    (A : Type u) [CommRing A] [Algebra k A]
    (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G) :
    (A ⊗[k] V) →ₗ[A] (A ⊗[k] V) :=
  (b.baseChange A).equivFun.symm.toLinearMap.comp
    (((GeneralLinearGroup.homMulEquiv n k A (g ≫ r)).val.mulVecLin).comp
      (b.baseChange A).equivFun.toLinearMap)

/-- The definition of stability on all algebra-valued points; the scalar extension
of W is Mathlib's `Submodule.baseChange`. Source: Milne, Chapter 4(g), p.92
(blueprint: lem-sfb-character-eigenspaces-independent). -/
def IsStable (b : Module.Basis n k V) (r : G ⟶ GeneralLinearGroup n k)
    (W : Submodule k V) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra k A]
    (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G),
    (W.baseChange A).map (action b r A g) ≤ W.baseChange A

/-- A character is an existing bundled group-scheme homomorphism to GL_1. Its value
on an A-point is the sole matrix entry under the canonical GL point equivalence.
Source: Milne, Chapter 4(g), p.92
(blueprint: lem-sfb-character-eigenspaces-independent). -/
def characterValue
    (χ : Grp.mk G ⟶ Grp.mk (GeneralLinearGroup (LinearGroupSchemes.Index.{u} 1) k))
    (A : Type u) [CommRing A] [Algebra k A]
    (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G) : A :=
  (GeneralLinearGroup.homMulEquiv (LinearGroupSchemes.Index.{u} 1) k A
    (g ≫ χ.hom.hom)).val ⟨0⟩ ⟨0⟩

/-- The character eigenspace: exactly the vectors whose scalar extensions transform
by the character on every algebra-valued point. Equalizers and intersections give
the actual submodule, without choosing any data. Source: Milne, Proposition 4.22,
p.92 (blueprint: lem-sfb-character-eigenspaces-independent). -/
def eigenspace (b : Module.Basis n k V) (r : G ⟶ GeneralLinearGroup n k)
    (χ : Grp.mk G ⟶ Grp.mk (GeneralLinearGroup (LinearGroupSchemes.Index.{u} 1) k)) :
    Submodule k V :=
  ⨅ (A : Type u) (_ : CommRing A) (_ : Algebra k A)
    (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G),
    LinearMap.eqLocus
      (((action b r A g).restrictScalars k).comp (TensorProduct.mk k A V 1))
      (characterValue χ A g • TensorProduct.mk k A V 1)

open Classical in
/-- The character eigenspaces are independent, only finitely many are nonzero,
and their sum is an internal direct sum. Here `iSupIndep` expresses independence
of every finite sum relation; equivalently, the canonical sum map is injective,
so it identifies the external direct sum with the sum of these subspaces.

Source: Milne, Corollary 4.24 and Theorem 4.25, pp.93--94.
(blueprint: lem-sfb-character-eigenspaces-independent)

Proof: Let C = k[G]. Its given group structure induces the coordinate Hopf
algebra. A character pulls the Laurent coordinate back to a group-like element
a_chi of C, and distinct characters give distinct a_chi by affine duality.
Evaluate the representation at the universal C-point to get the k-linear map
rho(v) = r_C(id)(1 tensor v). For a vector in the chi-eigenspace this is
a_chi tensor v. A finite relation sum v_i = 0 therefore gives
sum a_chi_i tensor v_i = 0. Applying any linear form V to k in the second
factor and using independence of distinct group-like elements gives f(v_i) = 0
for every i and every f. Linear forms separate vectors, so all v_i vanish.
For any finite set of nonzero eigenspaces, choose one nonzero vector from each.
The preceding independence makes these vectors linearly independent, bounding
the set's size by dim V. Hence there are only finitely many nonzero eigenspaces.
Finally the canonical sum map has zero kernel by independence and image the sum
of the eigenspaces, giving their internal direct sum. This also handles V = 0
and empty finite sums, without smoothness, connectedness or commutativity. -/
theorem independent_and_finite [IsAlgClosed k]
    [IsAffine G.left] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [FiniteDimensional k V] (b : Module.Basis n k V)
    (r : G ⟶ GeneralLinearGroup n k) [IsMonHom r] :
    iSupIndep (eigenspace b r) ∧ Set.Finite {χ | eigenspace b r χ ≠ ⊥} ∧
      Function.Injective (DirectSum.coeLinearMap (eigenspace b r)) := by
  sorry

end AlgebraicGeometry.CharacterEigenspaces
