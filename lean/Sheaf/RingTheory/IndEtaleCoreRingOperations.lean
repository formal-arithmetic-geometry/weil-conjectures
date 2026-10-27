module

public import Sheaf.RingTheory.FiniteEtaleSubalgebraUnion
public import Mathlib.FieldTheory.Separable
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Pi
import Sheaf.AlgebraicGeometry.EtaleComparison
import Sheaf.RingTheory.WeaklyEtaleField

/-!
# Ring operations for the maximal ind-étale subalgebra

Source: Stacks Project, Tags 0CKR and 0CKT, parts (1), (2), (4), (5), (6)
(blueprint: lem-sfb-ind-etale-core-ring-operations).
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

namespace Algebra

/-- The finite étale core is reduced, functorial, compatible with subalgebra
intersection, reduction and finite products, and is a separable algebraic field
when the ambient algebra is nonzero and has only trivial idempotents.
Source: Stacks Project, Tags 0CKR and 0CKT
(blueprint: lem-sfb-ind-etale-core-ring-operations).

Proof plan:
1. Choose a finite étale subalgebra containing a nilpotent element using
`lem-sfb-finite-etale-subalgebra-directed-union`. By
`lem-weil-pbc-etale-algebra-over-field-product` it is a product of fields,
so that element is zero, including in the empty product.
2. A homomorphism carries each finite étale stage into a finite étale image
by the image clause of the directed-union lemma. Corestrict the homomorphism.
3. For a subalgebra D of R the inclusion gives one containment. Conversely,
an element of D in a finite étale stage of R generates a finite étale algebra
by `det-pe-morphisms-etale-comparison` and `lem-weil-pbc-weak-etale-field`.
This singly generated algebra lies in D, proving the other containment.
4. The quotient-induced map is injective by reducedness of the core. Every
finite étale subalgebra of the reduction lifts into R by
`lem-sfb-etale-nil-ideal-map-lift`, applied to the nilradical (not assumed
nilpotent as an ideal). Its image lies in the core by the image clause,
so the quotient-induced map is surjective and is an algebra isomorphism.
5. Projections give one containment for products. Choose finite étale stages
for each of finitely many coordinates. Their product is étale by
`lem-weil-pbc-etale-algebra-finite-product`; coordinatewise finite spanning
sets give module finiteness, the affine criterion of
`def-weil-finite-integral-morphism`. It contains the tuple. This includes
the empty product, whose algebra and core are both zero.
6. A finite étale stage in a nonzero connected algebra has at least one field
factor. Two factors would give a nontrivial coordinate idempotent, so it is
one finite separable field. Inverses of nonzero core elements lie in their
stages, making the core a field. Minimal polynomials agree under injective
inclusions, hence every core element is separable algebraic over k, as in
`def-weil-pbc-separable-algebraic-extension`.
-/
theorem finiteEtaleSubalgebra_ring_operations (k : Type u) (R : Type v)
    [Field k] [CommRing R] [Algebra k R] :
    IsReduced (finiteEtaleSubalgebraUnion k R) ∧
    (∀ (S : Type w) [CommRing S] [Algebra k S] (f : R →ₐ[k] S),
      ∃ g : finiteEtaleSubalgebraUnion k R →ₐ[k] finiteEtaleSubalgebraUnion k S,
        (finiteEtaleSubalgebraUnion k S).val.comp g =
          f.comp (finiteEtaleSubalgebraUnion k R).val) ∧
    (∀ D : Subalgebra k R,
      (finiteEtaleSubalgebraUnion k D).map D.val = D ⊓ finiteEtaleSubalgebraUnion k R) ∧
    (∃ e : finiteEtaleSubalgebraUnion k R ≃ₐ[k]
        finiteEtaleSubalgebraUnion k (R ⧸ nilradical R),
      ∀ x : finiteEtaleSubalgebraUnion k R,
        (e x).val = Ideal.Quotient.mkₐ k (nilradical R) x.val) ∧
    (∀ (I : Type t) [Finite I] (A : I → Type w) [∀ i, CommRing (A i)]
        [∀ i, Algebra k (A i)],
      ∃ e : finiteEtaleSubalgebraUnion k (Π i, A i) ≃ₐ[k]
          (Π i, finiteEtaleSubalgebraUnion k (A i)),
        ∀ (x : finiteEtaleSubalgebraUnion k (Π i, A i)) (i : I),
          (e x i).val = x.val i) ∧
    (Nontrivial R → (∀ e : R, e ^ 2 = e → e = 0 ∨ e = 1) →
      IsField (finiteEtaleSubalgebraUnion k R) ∧
        Algebra.IsSeparable k (finiteEtaleSubalgebraUnion k R)) := by
  sorry

end Algebra
