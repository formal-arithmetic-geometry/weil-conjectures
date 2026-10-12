/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.GroupTheory.PGroup
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion
import Sheaf.AlgebraicGeometry.AbelianSheavesGModules

/-!
# Primary summands of a finite generic sheaf

Source: blueprint `lem-sc-affine-generic-second`, proof paragraph 1.
(blueprint: lem-sc-generic-finite-primary-decomposition)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace AlgebraicGeometry.Scheme

/-- A finite torsion abelian sheaf on a field has finitely many primary summands, with projection
and inclusion maps whose composites sum to the identity. Only the geometric stalks are
asserted finite; no curve, extension, filtration or cohomology is involved.

Source: blueprint `lem-sc-affine-generic-second`, proof paragraph 1.

Proof: take a separable closure of K inside its algebraic closure. Apply the abelian
stalk/Galois-module equivalence to M. The resulting finite abelian group V has an
annihilating integer N, for example its cardinality. If V is zero, take r = 0; the
identity of the zero sheaf is the empty sum. Otherwise enumerate the prime divisors of N
as p_i and write N as the product of the pairwise coprime powers q_i = p_i ^ v_i(N).
The subgroup V_i killed by q_i is invariant under every group automorphism, hence under
Galois. Chinese remainder gives integers c_i with c_i = 1 modulo q_i and c_i = 0 modulo
q_j for j different from i. Multiplication by c_i is the equivariant projection onto V_i:
q_i c_i kills V, it fixes V_i, and the sum of the c_i is 1 modulo N. The inclusion and
projection therefore have sum of composites equal to identity. Each V_i is finite, and
every element has order a power of p_i. Restrict the continuous discrete action to V_i.
Transport these submodules and maps through the quasi-inverse of the equivalence, then
conjugate with its unit isomorphism at M. Additivity transports the sum identity, and
the stalk comparison transports finiteness and the p-group condition. The prime field
and all summands stay in the original coefficient universe; no field extension is chosen.
(blueprint: lem-sc-generic-finite-primary-decomposition) -/
theorem exists_finite_primary_sheaf_decomposition
    (K : Type u) [Field K]
    (M : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hM : M.IsTorsion)
    (hfinite : Finite (((pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj M)) :
    ∃ (r : ℕ) (p : Fin r → ℕ)
      (N : Fin r → Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}),
      (∀ i, (p i).Prime) ∧
      (∀ i, Finite (((pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj (N i))) ∧
      (∀ i, IsPGroup (p i) (Multiplicative (((pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj (N i)))) ∧
      ∃ (a : ∀ i, M ⟶ N i) (b : ∀ i, N i ⟶ M),
        ∑ i, a i ≫ b i = 𝟙 M := by sorry

end AlgebraicGeometry.Scheme
