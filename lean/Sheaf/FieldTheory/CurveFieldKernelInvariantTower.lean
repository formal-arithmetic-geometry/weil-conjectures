/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.FieldTheory.FieldTower
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Flat.Basic

/-!
# Kernel invariant fields in towers of curve base extensions

Source: de Jong, Families of curves and alterations (1997), Remarks 2.3(iii), §2.6,
and §§3.2, 3.5, 3.11; agent-expanded field algebra in the DAG
(blueprint: lem-sfb-curve-field-kernel-invariant-tower).

The fixed-field assertions are expressed by their elementwise fixed-point conditions.
Pure inseparability of fixed fields is expressed by the exact Mathlib criterion
`isPurelyInseparable_iff_pow_mem`, with exponential characteristic `ringExpChar`.
Thus the characteristic-zero clauses literally say membership in the smaller field.
The tensor algebras retain their canonical ring structures: `IsField` asserts that
these rings are fields, without choosing replacement field structures.
-/

@[expose] public section

universe u v w g g' h

open scoped TensorProduct

namespace Algebra

/-- The canonical diagonal map on the tensor algebra for compatible semilinear actions.
Its value on `d ⊗ a` is `σD (ρ j) d ⊗ σL' j a`. No tensor-field structure is assumed.
Source: de Jong (1997), Remarks 2.3(iii), §2.6; tensor balancing as in Stacks Tag 00CX.
(blueprint: lem-sfb-curve-field-kernel-invariant-tower). -/
def curveFieldTensorDiagonal
    (L : Type u) (D : Type v) (L' : Type w)
    [Field L] [Field D] [Field L'] [Algebra L D] [Algebra L L']
    (J : Type g) (J' : Type g') [Group J] [Group J']
    (ρ : J' →* J) (σL : J →* (L ≃+* L)) (σD : J →* (D ≃+* D))
    (σL' : J' →* (L' ≃+* L'))
    (hD : ∀ j : J, (σD j).toRingHom.comp (algebraMap L D) =
      (algebraMap L D).comp (σL j).toRingHom)
    (hL' : ∀ j : J', (σL' j).toRingHom.comp (algebraMap L L') =
      (algebraMap L L').comp (σL (ρ j)).toRingHom)
    (j : J') : D ⊗[L] L' →+* D ⊗[L] L' :=
  Algebra.TensorProduct.mapRingHom (σL (ρ j)).toRingHom (σD (ρ j)).toRingHom
    (σL' j).toRingHom (hD (ρ j)) (hL' j)

/-- Finite extension of constants identifies the kernel-fixed tensor field with the
scalar extension by the kernel-fixed constants, and preserves purely inseparable
invariant-field extensions. Actions are homomorphisms to ring automorphisms and need
not be faithful. The case `ρ = MonoidHom.id J` is included.

Source: de Jong (1997), Remarks 2.3(iii), §2.6 and §§3.2, 3.5, 3.11;
agent-expanded field algebra (blueprint: lem-sfb-curve-field-kernel-invariant-tower).

Proof plan:
1. Tensor balancing defines the diagonal maps above; inverse group elements give
   inverse maps and the group law holds on pure tensors. The kernel fixes L and D.
2. Extend an L-basis of M to one of L' (lem-weil-pbc-vector-space-basis-through-vector).
   M/L is finite. Scalar-extension bases (def-weil-vector-space-scalar-extension and
   def-weil-vector-space-dimension) make both tensor algebras finite over D. The
   geometric-domain hypothesis applies to L' and M. Use
   lem-weil-pbc-finite-dimensional-domain-is-field to obtain IsField. The maps of
   the factors are the injections of lem-weil-common-extension-fields-tensor-inclusions.
3. Apply lem-sfb-tensor-kernel-inseparable-invariants with base L, left field D,
   right field L', acting group J', normal subgroup ker ρ and R = D^J. This gives
   the fixed-field equality and pure inseparability over D.
4. For β : J → H, ker (β.comp ρ) maps onto ker β, with kernel ker ρ.
5. Apply the same two-kernel lemma to this restriction with R = F. Apply it again
   with left field L and R = K, using L tensor_L L' = L'. These are precisely the
   two fixed-field power assertions below. Use isPurelyInseparable_iff_pow_mem.
6. Iteration is stated in curveFieldKernelInvariantTower below; identity ρ gives
   M = L'. In characteristic zero ringExpChar is 1, so all power clauses are equality.
-/
theorem curveFieldKernelInvariantStep
    (L : Type u) (D : Type v) (L' : Type w)
    [Field L] [Field D] [Field L'] [Algebra L D] [Algebra L L']
    [FiniteDimensional L L']
    (hgeom : ∀ (T : Type (max u v w)) [Field T] [Algebra L T], IsDomain (D ⊗[L] T))
    (J : Type g) (J' : Type g') [Group J] [Group J'] [Finite J] [Finite J']
    (ρ : J' →* J) (hρ : Function.Surjective ρ)
    (σL : J →* (L ≃+* L)) (σD : J →* (D ≃+* D))
    (σL' : J' →* (L' ≃+* L'))
    (hD : ∀ j : J, (σD j).toRingHom.comp (algebraMap L D) =
      (algebraMap L D).comp (σL j).toRingHom)
    (hL' : ∀ j : J', (σL' j).toRingHom.comp (algebraMap L L') =
      (algebraMap L L').comp (σL (ρ j)).toRingHom)
    (M : IntermediateField L L')
    (hM : ∀ a : L', a ∈ M ↔ ∀ j : J', ρ j = 1 → σL' j a = a)
    (hpi : IsPurelyInseparable L M) :
    IsField (D ⊗[L] L') ∧ IsField (D ⊗[L] M) ∧
    FiniteDimensional D (D ⊗[L] L') ∧ FiniteDimensional D (D ⊗[L] M) ∧
    IsPurelyInseparable D (D ⊗[L] M) ∧
    (∀ x : D ⊗[L] L',
      (∀ j : J', ρ j = 1 → curveFieldTensorDiagonal L D L' J J' ρ σL σD σL' hD hL' j x = x) ↔
      x ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id L D) M.val)) ∧
    (∀ (H : Type h) [Group H] [Finite H] (β : J →* H), Function.Surjective β →
      ∀ (K : Subfield L) (F : Subfield D),
      (∀ a : K, ∀ j : J, β j = 1 → σL j a = a) →
      (∀ d : F, ∀ j : J, β j = 1 → σD j d = d) →
      (∀ a : L, (∀ j : J, β j = 1 → σL j a = a) →
        ∃ n : ℕ, a ^ (ringExpChar L ^ n) ∈ K) →
      (∀ d : D, (∀ j : J, β j = 1 → σD j d = d) →
        ∃ n : ℕ, d ^ (ringExpChar D ^ n) ∈ F) →
      (∀ a : L', (∀ j : J', β (ρ j) = 1 → σL' j a = a) →
        ∃ n : ℕ, ∃ b : K, a ^ (ringExpChar L' ^ n) = algebraMap L L' b) ∧
      (∀ x : D ⊗[L] L',
        (∀ j : J', β (ρ j) = 1 →
          curveFieldTensorDiagonal L D L' J J' ρ σL σD σL' hD hL' j x = x) →
        ∃ n : ℕ, ∃ b : F, x ^ (ringExpChar D ^ n) =
          Algebra.TensorProduct.includeLeft (R := L) (S := D) (B := L') (b : D))) := by
  sorry

/-- The canonical composite embedding from stage zero to a stage in a finite field tower.
Source: de Jong (1997), §2.6, composition of alterations, and Stacks Tag 00D0.
This is finite recursion of the supplied transition maps, starting with the identity.
(blueprint: lem-sfb-curve-field-kernel-invariant-tower). -/
def curveFieldTowerMap {n : ℕ} (E : Fin (n + 1) → Type u) [∀ i, Field (E i)]
    (step : ∀ i : Fin n, E i.castSucc →+* E i.succ) :
    (i : Fin (n + 1)) → E 0 →+* E i :=
  Fin.induction (RingHom.id (E 0)) (fun i f ↦ (step i).comp f)

/-- Iteration through an arbitrary finite tower, including the zero-length tower.
The transition identifications are ring isomorphisms from the actual tensor products,
with their ordinary multiplication. The embeddings from the initial fields are the
canonical composites `curveFieldTowerMap`. Each β is the composite map to H, encoded
by its successor equation. No action is required to be faithful.

Source: de Jong (1997), Remarks 2.3(iii), §2.6 and §§3.2, 3.5, 3.11;
agent-expanded field algebra (blueprint: lem-sfb-curve-field-kernel-invariant-tower).

Proof plan (step 6 of the DAG proof): induct on the stage, starting with the two
assumed purely inseparable fixed-field extensions. At each successor use
curveFieldKernelInvariantStep with the preceding β. Its two final clauses supply the
inductive claims. Universal integrality persists: the algebra isomorphism
((d tensor a) tensor t) ↦ d tensor (a t), inverse d tensor t ↦ (d tensor 1) tensor t,
identifies the next geometric tensor with the preceding one over the same test field
(def-weil-vector-space-scalar-extension, def-pc-field-tower). The balancing relations
make these inverse multiplicative maps. The finite-stage composites are the maps
specified above. With equality at stage zero, choose exponent zero. In characteristic
zero every exponential characteristic is 1, hence the conclusions say equality.
-/
theorem curveFieldKernelInvariantTower
    (n : ℕ) (L : Fin (n + 1) → Type u) (D : Fin (n + 1) → Type v)
    [∀ i, Field (L i)] [∀ i, Field (D i)] [∀ i, Algebra (L i) (D i)]
    [∀ i : Fin n, Algebra (L i.castSucc) (L i.succ)]
    [∀ i : Fin n, FiniteDimensional (L i.castSucc) (L i.succ)]
    (e : ∀ i : Fin n, D i.castSucc ⊗[L i.castSucc] L i.succ ≃+* D i.succ)
    (he : ∀ (i : Fin n) (a : L i.succ),
      e i (1 ⊗ₜ[L i.castSucc] a) = algebraMap (L i.succ) (D i.succ) a)
    (hgeom : ∀ (T : Type (max u v)) [Field T] [Algebra (L 0) T],
      IsDomain (D 0 ⊗[L 0] T))
    (J : Fin (n + 1) → Type g) [∀ i, Group (J i)] [∀ i, Finite (J i)]
    (ρ : ∀ i : Fin n, J i.succ →* J i.castSucc)
    (hρ : ∀ i : Fin n, Function.Surjective (ρ i))
    (σL : ∀ i, J i →* (L i ≃+* L i)) (σD : ∀ i, J i →* (D i ≃+* D i))
    (hLD : ∀ (i : Fin (n + 1)) (j : J i) (a : L i),
      σD i j (algebraMap (L i) (D i) a) = algebraMap (L i) (D i) (σL i j a))
    (hL : ∀ (i : Fin n) (j : J i.succ) (a : L i.castSucc),
      σL i.succ j (algebraMap (L i.castSucc) (L i.succ) a) =
        algebraMap (L i.castSucc) (L i.succ) (σL i.castSucc (ρ i j) a))
    (hD : ∀ (i : Fin n) (j : J i.succ) (d : D i.castSucc) (a : L i.succ),
      σD i.succ j (e i (d ⊗ₜ[L i.castSucc] a)) =
        e i (σD i.castSucc (ρ i j) d ⊗ₜ[L i.castSucc] σL i.succ j a))
    (M : ∀ i : Fin n, IntermediateField (L i.castSucc) (L i.succ))
    (hM : ∀ (i : Fin n) (a : L i.succ),
      a ∈ M i ↔ ∀ j : J i.succ, ρ i j = 1 → σL i.succ j a = a)
    (hpi : ∀ i : Fin n, IsPurelyInseparable (L i.castSucc) (M i))
    (H : Type h) [Group H] [Finite H]
    (β : ∀ i, J i →* H) (hβ : ∀ i, Function.Surjective (β i))
    (hβρ : ∀ i : Fin n, β i.succ = (β i.castSucc).comp (ρ i))
    (K : Subfield (L 0)) (F : Subfield (D 0))
    (hK : ∀ a : K, ∀ j : J 0, β 0 j = 1 → σL 0 j a = a)
    (hF : ∀ d : F, ∀ j : J 0, β 0 j = 1 → σD 0 j d = d)
    (hKpi : ∀ a : L 0, (∀ j : J 0, β 0 j = 1 → σL 0 j a = a) →
      ∃ m : ℕ, a ^ (ringExpChar (L 0) ^ m) ∈ K)
    (hFpi : ∀ d : D 0, (∀ j : J 0, β 0 j = 1 → σD 0 j d = d) →
      ∃ m : ℕ, d ^ (ringExpChar (D 0) ^ m) ∈ F) :
    (∀ (i : Fin (n + 1)) (T : Type (max u v)) [Field T] [Algebra (L i) T],
      IsDomain (D i ⊗[L i] T)) ∧
    (∀ (i : Fin (n + 1)) (a : L i),
      (∀ j : J i, β i j = 1 → σL i j a = a) →
      ∃ m : ℕ, ∃ b : K, a ^ (ringExpChar (L i) ^ m) =
        curveFieldTowerMap L (fun k ↦ algebraMap (L k.castSucc) (L k.succ)) i b) ∧
    (∀ (i : Fin (n + 1)) (d : D i),
      (∀ j : J i, β i j = 1 → σD i j d = d) →
      ∃ m : ℕ, ∃ b : F, d ^ (ringExpChar (D i) ^ m) =
        curveFieldTowerMap D (fun k ↦ (e k).toRingHom.comp
          (Algebra.TensorProduct.includeLeftRingHom (R := L k.castSucc))) i b) := by
  sorry

end Algebra
