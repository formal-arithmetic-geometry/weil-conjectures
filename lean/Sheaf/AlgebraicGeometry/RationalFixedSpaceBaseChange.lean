module

public import Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Rational fixed spaces and arbitrary algebra base change

Source: Milne, Algebraic Groups (2017), Propositions 4.31 and 4.33, printed p.96,
and Lemma 5.15, printed p.102 (blueprint: lem-sfb-rational-fixed-space-base-change).

We use the existing natural representation interface. Its finite-dimensional dictionary
identifies it with a homomorphism to the existing general linear group scheme, including
GL of the zero vector space. Scalar extensions are A tensor V; tensor symmetry identifies
these with the V tensor A convention of the source. Fixed vectors are an intersection of
kernels over all test algebras, so no reducedness or field-valued-point assumption is made.
-/

set_option autoImplicit false

@[expose] public section

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.RationalRepresentation

variable {k : Type u} [Field k]
variable {G : Scheme.{u}} [G.Over (Spec (.of k))]
variable [GrpObj (G.asOver (Spec (.of k)))] [IsAffine G]
variable {H : Over (Spec (.of k))} [GrpObj H]
variable {V : Type u} [AddCommGroup V] [Module k V]

/-- The subspace V^H of vectors fixed by every H(B), for every commutative k-algebra B.
Each kernel imposes r_B(h)(1 tensor v) - 1 tensor v = 0. The intersection supplies its
submodule structure directly, without choosing vectors or postponing any data.
Source: Milne, Proposition 4.31, printed p.96
(blueprint: lem-sfb-rational-fixed-space-base-change). -/
noncomputable def fixedSpace (r : NaturalRepresentation (k := k) G V)
    (i : H ⟶ G.asOver (Spec (.of k))) : Submodule k V :=
  ⨅ (B : CommAlgCat.{u} k) (h : points H B),
    LinearMap.ker
      (((r.action B (h ≫ i)).toLinearMap.restrictScalars k - LinearMap.id) ∘ₗ
        TensorProduct.mk k B V 1)

/-- The fixed-space inclusion stays injective after arbitrary algebra base change, and
its image is exactly the vectors fixed by H after every further algebra extension.
If H is normal, the ambient action restricts to a rational representation on V^H on
which H acts trivially. The intertwining equation specifies the restrictions themselves.
Source: Milne, Propositions 4.31 and 4.33, printed p.96, and Lemma 5.15, printed p.102
(blueprint: lem-sfb-rational-fixed-space-base-change).

Proof: (1) The defining equations are linear. Choose a basis of V/W for W=V^H, lift
its basis vectors, and extend linearly to a section V/W to V. Subtract this section
composed with the quotient from the identity to get a retraction V to W. A finite
spanning family of V projects to one of W, so W is finite-dimensional, including W=0.
Use lem-weil-pbc-vector-space-free and def-weil-pbc-free-module.
(2) Tensor the retraction with A. It splits the tensor inclusion, proving injectivity.
Choose a possibly infinite k-basis (a_j) of A. Every tensor has a finite expression
sum v_j tensor a_j, with unique coefficients extracted by the basis coordinate maps
and the tensor universal property (def-weil-pbc-module-tensor-product).
(3) A tensor from W is fixed after every A to B, by B-linearity of r_B(h).
(4) Conversely, test a universally fixed tensor over S tensor A, for every k-algebra
S and h in H(S). Send h along S to S tensor A. Naturality gives the finite equation
sum (r_S(h)(v_j tensor 1)-v_j tensor 1) tensor a_j=0. Coefficient extraction gives
v_j in W for each j. Use lem-weil-pbc-algebra-tensor-pushout-universal-property.
(5) For normal H, h g w = g (g inverse h g) w = g w over every further algebra B.
Thus g preserves the tensor image; g inverse gives its inverse restriction. Injectivity
of the inclusion proves naturality, multiplication and identity for these restrictions.
Use def-sc-group-scheme-subgroup for normality on all test algebras.
(6) Evaluate the restrictions at the universal k[G]-point. In a finite basis of W this
is an invertible matrix over k[G], hence a morphism G to GL(W) by def-sc-general-linear-group
and def-weil-affine-spectrum. Naturality recovers every restriction from this universal
matrix. Equivalently apply the existing finite_dictionary to the natural restrictions.
(7) Check the group law on affine opens of G times G, and the identity at k. Every
H(A)-point acts identically by the definition of W and part (3). For W=0 use the unique
map to GL(0)=Spec k. These are the seven proof steps of the DAG node. -/
theorem fixedSpace_baseChange [LocallyOfFiniteType (G ↘ Spec (.of k))]
    [QuasiCompact (G ↘ Spec (.of k))] [FiniteDimensional k V]
    (r : NaturalRepresentation (k := k) G V)
    (i : H ⟶ G.asOver (Spec (.of k))) [IsClosedSubgroupScheme i] :
    (∀ (A : Type u) [CommRing A] [Algebra k A],
      Function.Injective ((fixedSpace r i).subtype.baseChange A) ∧
      ∀ w : A ⊗[k] V,
        w ∈ LinearMap.range ((fixedSpace r i).subtype.baseChange A) ↔
          ∀ (B : Type u) [CommRing B] [Algebra k B]
            (α : A →ₐ[k] B) (h : points H B),
            r.action B (h ≫ i) (α.toLinearMap.rTensor V w) =
              α.toLinearMap.rTensor V w) ∧
    (IsNormalSubgroupScheme i →
      ∃ s : NaturalRepresentation (k := k) G (fixedSpace r i),
        (∀ (A : Type u) [CommRing A] [Algebra k A]
          (g : points (G.asOver (Spec (.of k))) A) (w : A ⊗[k] fixedSpace r i),
          (fixedSpace r i).subtype.baseChange A (s.action A g w) =
            r.action A g ((fixedSpace r i).subtype.baseChange A w)) ∧
        ∀ (A : Type u) [CommRing A] [Algebra k A] (h : points H A),
          s.action A (h ≫ i) = 1) := by
  sorry

end AlgebraicGeometry.RationalRepresentation
