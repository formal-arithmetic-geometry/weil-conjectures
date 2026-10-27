module

public import Sheaf.RingTheory.FiniteEtaleSubalgebraUnion
public import Mathlib.RingTheory.TensorProduct.Maps
import Sheaf.RingTheory.IndEtaleUniverseTransport
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.RingTheory.WeaklyEtaleField
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import Sheaf.FieldTheory.FiniteSeparableClosure
import Sheaf.FieldTheory.SeparableTensorAlgebraicClosure
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.FiniteType
import WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Base change of the maximal ind-étale subalgebra

Source: Stacks Project, Tag 0CKU, lemma-change-fields-max-weakly-etale-subalgebra,
with the finite étale union description of Tag 0CKR
(blueprint: lem-sfb-maximal-ind-etale-field-base-change).

The comparison is the tensor product of the subalgebra inclusion and the identity
of the extension field. Injectivity and equality of its image with the specified
union express identification inside the ambient tensor product. The target union
uses the explicit right-factor algebra structure, so its scalars are the extension
field rather than the first tensor factor.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Algebra

/-- The inclusion of the maximal ind-étale subalgebra remains injective after
extension of the base field, and its image is precisely the maximal ind-étale
subalgebra over that extension. No finiteness or reducedness is assumed on `A`.
Source: Stacks Project, Tag 0CKU, lemma-change-fields-max-weakly-etale-subalgebra
(blueprint: lem-sfb-maximal-ind-etale-field-base-change).

Proof plan, following the node's nine steps:
1. If A is zero, its subalgebras and all tensor products in the conclusion are zero.
2. For every extension T/k, tensor the inclusion of B_k(A) with T. It is injective
by `lem-weil-pbc-module-over-field-flat` and `lem-weil-pbc-flat-tensor-exact`.
By `lem-sfb-finite-etale-subalgebra-directed-union`, the core is a directed union
of finite étale algebras, hence ind-étale by `def-weil-pbc-ind-etale-algebra`.
`lem-weil-pbc-ind-etale-stability` and `lem-weil-pbc-weak-etale-field` show that
every element of the base change lies in a finite étale T-subalgebra. This gives
the canonical injective comparison into B_T(A tensor T), compatible with towers.
3. For a finitely generated field F/k, `lem-sfb-ind-etale-core-ring-operations`
makes E = B_k(F) a separable algebraic subfield. Conversely, a separable element
lies in the finite separable field k[alpha], hence in a finite étale subalgebra by
`lem-sc-finite-etale-algebra-criterion`. Thus E is the relative separable closure
(`def-weil-pbc-relative-separable-closure` and
`def-weil-pbc-separable-algebraic-extension`). By `lem-zl-finite-separable-closure`,
E/k is finite and F/E is geometrically irreducible.
4. For algebraically closed Omega/k, use `lem-pc-separable-tensor-algebraic-closure`
to split E tensor Omega as a finite product of Omega. The coordinate embeddings
of E into Omega and tensor associativity split F tensor Omega into the products
F tensor_{E,tau} Omega. The tensor-product isomorphism sends a tensor with a tuple
to its coordinate tensors; its inverse sums the coordinate maps multiplied by
the coordinate idempotents. The included E tensor Omega becomes the scalar product.
5. By `def-pc-geometrically-irreducible`, each factor has nonempty irreducible,
hence connected spectrum. `lem-pc-scheme-connected-iff-idempotents` and
`def-weil-affine-spectrum` imply it has only trivial idempotents. The core lemma
makes its core a separable algebraic field over Omega, hence Omega itself since
Omega is algebraically closed. The finite-product clause of the core lemma now
identifies the core with the included E tensor Omega, proving surjectivity for F.
6. For reduced finite-type nonzero A, `lem-weil-pbc-finite-type-algebra-noetherian`
makes A Noetherian. `lem-weil-pbc-reduced-noetherian-total-ring-fractions` expresses
Q(A) as a finite product of finitely generated residue fraction fields. The map
A into Q(A) is injective by the nonzerodivisor definition. The field and product
cases prove the result for Q(A). The intersection clause of the core lemma gives
B(A) = A intersect B(Q(A)), also after scalar extension. Tensor the exact sequence
from this intersection to A direct-sum B(Q(A)), followed by (a,b) mapping to a-b
in Q(A); flatness and tensor exactness identify both intersections, proving the claim.
7. For finite-type A, quotient by its nilradical N. The core lemma identifies the
cores of A and A/N. Tensor exactness says that the kernel after extension to Omega
is N tensor Omega. A finite sum of nilpotent-coefficient tensors is nilpotent:
if the coefficients have exponents m_j, exponent 1 + sum_j (m_j - 1) suffices.
The reduced case lifts the image of a core element to B_k(A) tensor Omega; their
difference is nilpotent in the reduced core, hence zero. This proves surjectivity.
8. For arbitrary A, a core element over Omega lies in a finite étale subalgebra D
by the union lemma. Express a finite Omega-basis of D using finitely many tensors.
Their A-coefficients generate a finite-type subalgebra A_0 of A. Flatness embeds
A_0 tensor Omega in A tensor Omega and puts all of D in that image. Apply the
finite-type case to A_0; its finite étale subalgebras are also subalgebras of A.
9. For arbitrary L/k, take an algebraic closure Omega/L using
`lem-pc-algebraic-closure-exists-unique`. The chain B_k(A) tensor Omega into
B_L(A tensor L) tensor_L Omega into B_Omega(A tensor Omega) has surjective
composite by step 8, hence surjective first arrow. That arrow is the tensor with
Omega of the comparison for L. Tensor exactness kills its cokernel after extension.
Tensoring with Omega detects zero: extend 1 in Omega to an L-basis and project to
its 1-coordinate, giving a retraction on every L-vector space. Thus the cokernel
vanishes before extension. Together with step 2 this proves the stated image equality.
-/
theorem finiteEtaleSubalgebraUnion_field_baseChange
    (k : Type u) (A : Type v) (L : Type w)
    [Field k] [CommRing A] [Field L] [Algebra k A] [Algebra k L] :
    Function.Injective
        (TensorProduct.map (finiteEtaleSubalgebraUnion k A).val (AlgHom.id k L)) ∧
      Set.range
          (TensorProduct.map (finiteEtaleSubalgebraUnion k A).val (AlgHom.id k L)) =
        (@finiteEtaleSubalgebraUnion L (A ⊗[k] L) _ _
          TensorProduct.rightAlgebra : Set (A ⊗[k] L)) := by
  sorry

end Algebra
