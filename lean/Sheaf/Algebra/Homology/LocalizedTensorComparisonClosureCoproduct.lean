module

public import Sheaf.Algebra.Homology.LocalizedTensorComparisonProperty
public import Mathlib.RingTheory.Flat.Basic
import Sheaf.Algebra.Homology.KFlatDerivedTensorAssociator

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
namespace ModuleCat

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
  [HasDerivedCategory (ModuleCat.{u} B)]
  (Q : CochainComplex (ModuleCat.{u} A) ℤ)
  (N : CochainComplex (ModuleCat.{u} C) ℤ)
  (t : (((extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)).obj Q) ⟶ N)

/-- The localized tensor comparison predicate is closed under coproducts.
Source: Stacks Project, Tags 0DJA(1), 0BYJ and 09PB.

Proof: Fix a degree i. The universal derived counit, the canonical tensor associator
and scalar-extension adjunction identify the displayed comparison for a K-flat
representative U with a natural degree-i comparison on D(A). The counit fixes
this map, so changing the derived model conjugates it by canonical isomorphisms.
K-flat quasi-isomorphisms and their roofs give the same conjugation for a change
of representative. Extension from A to C sends A-K-flat complexes to C-K-flat
complexes: tensoring an acyclic C-complex with C tensor_A U is restriction of
that complex tensored over A with U. Thus the target is computed by derived
tensor with N even when A to C is not flat.
Choose K-flat representatives of the summands. Their direct sum is K-flat,
since tensor and direct sums commute and direct sums of exact sequences of
modules are exact. It represents their coproduct in D(A). Derived tensor over
R with B, restriction of scalars, and cohomology preserve these sums. Extension
from A tensor_R B to C preserves sums as a left adjoint, as do extension from
A to C and tensor with N. Naturality identifies the comparison on this sum
with the direct sum of the comparisons on the summands in degree i. A direct
sum of isomorphisms is an isomorphism (sum their inverses). Transport across
the unique coproduct isomorphism to S, and then across the model and
representative identifications above. This proves the assertion for every U,
every model and every i. For an empty family all objects and maps are zero.
(blueprint: lem-pc-localized-tensor-comparison-closure-coproducts). -/
theorem localizedTensorComparisonProperty_closure_coproducts
    (hC : Module.Flat (A ⊗[R] B) C)
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic) :
    ∀ {I : Type u} (G : I → DerivedCategory (ModuleCat.{u} A))
      (S : DerivedCategory (ModuleCat.{u} A)) (ι : ∀ i, G i ⟶ S),
      CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.Cofan.mk S ι) →
      (∀ i, localizedTensorComparisonProperty R A B C Q N t (G i)) →
      localizedTensorComparisonProperty R A B C Q N t S := by sorry

end ModuleCat
