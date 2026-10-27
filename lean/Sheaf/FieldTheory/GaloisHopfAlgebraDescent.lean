module

public import Sheaf.FieldTheory.SemilinearHopfAlgebra
public import Mathlib.RingTheory.FiniteType

import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Finite Galois descent for commutative Hopf algebras

Source: Milne, Algebraic Groups (2017), Appendix A.64--A.66, pp.580--581
(blueprint: lem-sfb-galois-hopf-algebra-descent).

The tensor and invariant identifications below specify the functors on objects and
morphisms. The normalized unit and counit are Hopf isomorphisms, so they specify the
descended Hopf operations as well as the underlying algebra equivalence.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory
open scoped TensorProduct

namespace CommHopfAlgCat

/-- Scalar extension and invariants give inverse equivalences of commutative Hopf
algebras, including the canonical action, unit, counit, morphisms, and finite type.

Source: Milne A.64, pp.580--581, Hopf-algebra consequence; A.66 for morphisms
(blueprint: lem-sfb-galois-hopf-algebra-descent).

Proof plan, following the node:
1. By lem-sfb-finite-galois-vector-space-descent, the invariant algebra A of B
   has the algebra isomorphism L tensor A → B, lambda tensor a maps to lambda a.
   Multiplicativity follows on pure tensors from
   lem-weil-pbc-algebra-tensor-pushout-universal-property. Descent for k identifies
   the invariant field with k.
2. Iterate lem-weil-pbc-base-change-tensor-distrib for two and three factors.
   The equivariant comparisons send lambda tensor (a1 tensor ... tensor an) to
   lambda a1 tensor ... tensor an. Their invariant maps identify the invariant
   tensor powers with the tensor powers of A, using the vector-space unit.
3. Restrict the antipode to invariants, the counit to the invariant field, and
   the coproduct through the two-factor comparison. Their scalar extensions
   are the operations of B, as checked on lambda tensor a.
4. Coassociativity, both counit identities, and both inverse identities from
   lem-sfb-affine-group-coordinate-hopf hold after faithful scalar extension,
   hence before it. The three-factor comparison handles coassociativity.
5. Conversely use the tensor Hopf structure on L tensor C. The action on the
   first factor commutes with all operations. The vector-space unit is the
   indicated invariant Hopf isomorphism.
6. Restrict equivariant Hopf maps to invariants. The injective two-factor
   comparison proves coproduct compatibility; counit and antipode compatibility
   follow by restriction. Conversely extend Hopf maps by scalars. The vector-space
   Hom bijection restricts to these Hopf maps, naturally.
7. The two unit/counit triangle composites are identities on pure tensors and
   on invariant elements. These exhibit the equivalence.
8. Finite generators remain generators after extension. Conversely write each
   generator of B as a finite sum of scalar multiples of invariants. The finitely
   many resulting invariant elements generate A: their subalgebra A0 spans B
   over L, so the scalar extension of the vector-space quotient A/A0 vanishes.
   Faithfulness gives A/A0 = 0. Use def-weil-module-base-change and
   def-weil-pbc-finite-type-algebra. -/
theorem finite_galois_hopf_algebra_descent
    (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L] :
    ∃ E : CommHopfAlgCat.{max u v w} k ≌ GaloisObject.{u, v, max u v w} k L,
    ∃ t : ∀ A : CommHopfAlgCat.{max u v w} k,
      (E.functor.obj A).obj ≃ₐc[L] L ⊗[k] A,
    ∃ i : ∀ B : GaloisObject.{u, v, max u v w} k L,
      E.inverse.obj B ≃ₐ[k] B.invariants,
    (∀ (A : CommHopfAlgCat.{max u v w} k) (σ : L ≃ₐ[k] L)
      (x : (E.functor.obj A).obj),
      t A ((E.functor.obj A).action.ρ σ x) =
        TensorProduct.map σ.toLinearEquiv.toLinearMap (LinearMap.id : A →ₗ[k] A)
          (t A x)) ∧
    (∀ (A C : CommHopfAlgCat.{max u v w} k) (f : A ⟶ C)
      (x : (E.functor.obj A).obj),
      t C ((E.functor.map f).hom.hom x) =
        TensorProduct.map (LinearMap.id : L →ₗ[k] L) f.hom.toLinearMap (t A x)) ∧
    (∀ (B C : GaloisObject.{u, v, max u v w} k L) (f : B ⟶ C)
      (a : E.inverse.obj B),
      (i C ((E.inverse.map f).hom a)).val = f.hom.hom (i B a).val) ∧
    (∀ (A : CommHopfAlgCat.{max u v w} k) (a : A),
      t A (i (E.functor.obj A) ((E.unitIso.app A).hom.hom a)).val = 1 ⊗ₜ[k] a) ∧
    (∀ (B : GaloisObject.{u, v, max u v w} k L) (r : L) (a : E.inverse.obj B),
      (E.counitIso.app B).hom.hom.hom ((t (E.inverse.obj B)).symm (r ⊗ₜ[k] a)) =
        r • (i B a).val) ∧
    (∀ A : CommHopfAlgCat.{max u v w} k,
      (algebraMap k A).FiniteType ↔ (algebraMap L (E.functor.obj A).obj).FiniteType) ∧
    (∀ B : GaloisObject.{u, v, max u v w} k L,
      (algebraMap L B.obj).FiniteType ↔ (algebraMap k (E.inverse.obj B)).FiniteType) := by
  sorry

end CommHopfAlgCat
