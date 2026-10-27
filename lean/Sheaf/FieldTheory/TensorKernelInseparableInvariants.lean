/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.FieldTheory.FieldTower
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import WeilConjectures.Mathlib.Algebra.CharP.Lemmas

/-!
# Purely inseparable tensor invariants and composite kernels

Source: de Jong, Families of curves and alterations (1997), Remarks 2.3(iii)--(iv),
p. 602, and Theorem 5.9(a), p. 617; the agent-expanded field calculation in the DAG
(blueprint: lem-sfb-tensor-kernel-inseparable-invariants).

The tensor product retains its canonical multiplication. `IsField` asserts that this
ring is a field. Fixed elements are specified by their defining equations, and
`ringExpChar` power membership is the criterion `isPurelyInseparable_iff_pow_mem`.
In characteristic zero the exponential characteristic is one, so these clauses
state membership itself. Since Q acts trivially on L, the N-fixed elements of L
are exactly the fixed elements for the induced action of A = N/Q.

## Main statements

* `Algebra.tensorKernelInseparableInvariants`: the tensor fixed-field equality and
  its two purely inseparable extension assertions.
* `Algebra.purelyInseparable_compositeKernel`: the final two-kernel assertion.
-/

@[expose] public section

universe u v w g g' h

open scoped TensorProduct

namespace Algebra

/-- Tensor invariants and pure inseparability, with no faithfulness assumption.
Here E is precisely M^Q, and R is a subfield of L^(N/Q). The canonical map
`L ⊗[K] E → L ⊗[K] M` identifies its source with the Q-fixed field.

Source: de Jong (1997), Remarks 2.3(iii)--(iv), p. 602, and Theorem 5.9(a), p. 617;
Stacks Tags 09HE, 09HG, 09HH for pure inseparability
(blueprint: lem-sfb-tensor-kernel-inseparable-invariants).

Proof plan, steps 1--6 of the DAG:
1. Fixed elements form a subfield. Q fixes K because it fixes L and the embeddings
   are equivariant and injective. Both factor embeddings into the tensor field
   are injective, since their source fields have no nontrivial proper ideals.
2. Choose a K-basis of L using lem-weil-pbc-vector-space-basis-through-vector.
   By def-weil-vector-space-scalar-extension, it gives E- and M-bases of the
   respective tensor products. All coordinate families have finite support.
3. The map induced by E.val preserves these coordinates, hence is injective.
   The diagonal Q-action fixes the basis vectors and acts on their coefficients.
   Unique coordinates identify its fixed elements with the map's image, using
   def-weil-pbc-module-tensor-product and def-weil-vector-space-scalar-extension.
4. Fixed elements are closed under inverses, so this image and L tensor E are fields.
5. In positive characteristic choose a common p-power for the finitely many
   E-coefficients. The Frobenius of def-weil-ring-frobenius carries the tensor sum
   into L. Use def-weil-pbc-finite-purely-inseparable-extension for this criterion.
   In characteristic zero E = K, so the image is exactly L.
6. An N-fixed tensor has a power in L by step 5. Equivariance makes that power
   N/Q-fixed, and a further power lies in R. Add the exponents, as in Stacks 09HG
   (def-weil-pbc-finite-purely-inseparable-extension). In characteristic zero both
   power assertions are equality. The embedding of R is fixed by N by hR. -/
theorem tensorKernelInseparableInvariants
    (K : Type u) (L : Type v) (M : Type w)
    [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    [FiniteDimensional K M] (hT : IsField (L ⊗[K] M))
    (N : Type g) [Group N] [Finite N]
    (σK : N →* (K ≃+* K)) (σL : N →* (L ≃+* L)) (σM : N →* (M ≃+* M))
    (hL : ∀ n : N, (σL n).toRingHom.comp (algebraMap K L) =
      (algebraMap K L).comp (σK n).toRingHom)
    (hM : ∀ n : N, (σM n).toRingHom.comp (algebraMap K M) =
      (algebraMap K M).comp (σK n).toRingHom)
    (Q : Subgroup N) [Q.Normal] (hQ : ∀ q : Q, ∀ l : L, σL q l = l)
    (E : IntermediateField K M)
    (hE : ∀ m : M, m ∈ E ↔ ∀ q : Q, σM q m = m)
    (hEpi : IsPurelyInseparable K E)
    (R : Subfield L) (hR : ∀ r : R, ∀ n : N, σL n r = r)
    (hRpi : ∀ l : L, (∀ n : N, σL n l = l) →
      ∃ a : ℕ, l ^ (ringExpChar L ^ a) ∈ R) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id K L) E.val) ∧
    (∀ x : L ⊗[K] M,
      (∀ q : Q, Algebra.TensorProduct.mapRingHom (σK q).toRingHom
        (σL q).toRingHom (σM q).toRingHom (hL q) (hM q) x = x) ↔
      x ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id K L) E.val)) ∧
    IsField (L ⊗[K] E) ∧ IsPurelyInseparable L (L ⊗[K] E) ∧
    (∀ x : L ⊗[K] M,
      (∀ n : N, Algebra.TensorProduct.mapRingHom (σK n).toRingHom
        (σL n).toRingHom (σM n).toRingHom (hL n) (hM n) x = x) →
      ∃ a : ℕ, ∃ r : R, x ^ (ringExpChar L ^ a) =
        Algebra.TensorProduct.includeLeft (R := K) (S := L) (B := M) (r : L)) := by
  sorry

/-- Pure inseparability descends through the kernels of two compatible surjections
of finite groups acting on a finite field tower. The actions need not be faithful.
The two hypotheses and the conclusion are the exact power-membership criterion
for F^(ker β)/e, e^(ker α)/k, and F^(ker (α.comp β))/k, respectively.

Source: de Jong (1997), Remarks 2.3(iii)--(iv), p. 602, and Theorem 5.9(a), p. 617;
Stacks Tags 09HE and 09HG
(blueprint: lem-sfb-tensor-kernel-inseparable-invariants).

Proof plan, step 7 of the DAG: ker β is contained in ker (α.comp β). Surjectivity
of β lifts each a in ker α to j in ker (α.comp β). Compatibility of the actions
shows that k is fixed by this composite kernel. If x is fixed by the composite
kernel, it is fixed by ker β, so a p-power is the image of y in e. Lift each
member of ker α as above; injectivity of e → F shows that y is ker α-fixed.
A further power is in k by the second hypothesis. Combining exponents proves
the conclusion, by def-weil-pbc-finite-purely-inseparable-extension and Stacks 09HG.
In characteristic zero the two hypotheses give membership without taking powers,
so the same lifting argument gives equality. No action is assumed injective. -/
theorem purelyInseparable_compositeKernel
    (k : Type u) (e : Type v) (F : Type w)
    [Field k] [Field e] [Field F] [Algebra k e] [Algebra e F] [Algebra k F]
    [IsScalarTower k e F] [FiniteDimensional k e] [FiniteDimensional e F]
    (J : Type g) (G : Type g') (H : Type h)
    [Group J] [Group G] [Group H] [Finite J] [Finite G] [Finite H]
    (β : J →* G) (α : G →* H)
    (hβ : Function.Surjective β) (hα : Function.Surjective α)
    (σk : H →* (k ≃+* k)) (σe : G →* (e ≃+* e)) (σF : J →* (F ≃+* F))
    (hke : ∀ (g : G) (a : k), σe g (algebraMap k e a) =
      algebraMap k e (σk (α g) a))
    (heF : ∀ (j : J) (a : e), σF j (algebraMap e F a) =
      algebraMap e F (σe (β j) a))
    (hFpi : ∀ x : F, (∀ j : J, β j = 1 → σF j x = x) →
      ∃ a : ℕ, x ^ (ringExpChar F ^ a) ∈ (algebraMap e F).range)
    (hepi : ∀ x : e, (∀ g : G, α g = 1 → σe g x = x) →
      ∃ a : ℕ, x ^ (ringExpChar e ^ a) ∈ (algebraMap k e).range) :
    ∀ x : F, (∀ j : J, α (β j) = 1 → σF j x = x) →
      ∃ a : ℕ, x ^ (ringExpChar F ^ a) ∈ (algebraMap k F).range := by
  sorry

end Algebra
