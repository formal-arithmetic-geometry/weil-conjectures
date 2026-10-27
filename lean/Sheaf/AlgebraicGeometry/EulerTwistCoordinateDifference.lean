/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X8
-/
module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension

/-! # The geometric dimension drop for a coordinate difference

Source: Stacks Project, Varieties, Tag 0BEM, geometric part of the proof.
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- A coordinate difference of the Euler function is an integral linear combination of
Euler functions of coherent modules supported in one lower dimension.
Source: Stacks Project, Varieties, Tag 0BEM, proof of Lemma 33.45.1
(blueprint: lem-sc-euler-twist-coordinate-difference).

Proof: Write chi_n(M) for the specified integer-power twist of M. If the support of F
has dimension at most d, take the two modules F tensor L_j and F, with coefficients +1
and -1. Invertible tensoring preserves coherence and support, and the signed-power
identities identify chi_(n+e_j)(F) with chi_n(F tensor L_j).

Otherwise the support has dimension d+1. Remove embedded associated points, obtaining
0 → K → F → F' → 0 with K coherent and support dimension at most d. On the
scheme-theoretic support i : Z → X of F', the corresponding faithful coherent module H
has full support and no embedded associated points. Locally O_Z embeds in a finite sum
of copies of H, so Ass(O_Z) is contained in Ass(H); thus Z has no embedded points.
Choose a regular meromorphic section of i^*L_j. The denominator product with H maps
injectively to H and to H tensor i^*L_j. Write Q and Q' for these two coherent cokernels.
Their supports avoid the generic points and have dimension at most d. Choose these
modules before choosing n. Tensor both exact sequences by all the pulled-back integer
powers, which are invertible even for negative exponents. Euler additivity, associativity,
symmetry and dual evaluation give the difference chi_n(Q') - chi_n(Q).

Push Q and Q' to X. Closed-immersion cohomology and projection formula preserve all these
twisted Euler characteristics, and the closed embedding preserves support dimensions.
Subtract the Euler identities for 0 → K → F → F' → 0 at n+e_j and n. Its additional
contribution is chi_n(K tensor L_j) - chi_n(K). The four modules i_*Q', i_*Q,
K tensor L_j, K with coefficients +1,-1,+1,-1 give the result. Empty support can use the
empty sum; the construction also handles zero cokernels and zero coordinates -/
theorem eulerChar_tensorPowers_coordinate_difference
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) (d : ℕ)
    (hdim : topologicalKrullDim {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ≤
      ((d + 1 : ℕ) : WithBot ℕ∞))
    (r : ℕ) (L : Fin r → X.Modules) [∀ i : Fin r, (L i).IsInvertible]
    (j : Fin r) :
    ∃ (m : ℕ) (G : Fin m → X.Modules) (c : Fin m → ℤ),
      (∀ i, RingedSpace.IsCoherent X.toRingedSpace (G i)) ∧
      (∀ i, topologicalKrullDim {x : X | ¬ Subsingleton ((G i).presheaf.stalk x)} ≤
        (d : WithBot ℕ∞)) ∧
      ∀ n : Fin r → ℤ,
        (((List.ofFn fun i : Fin r =>
          if 0 ≤ Function.update n j (n j + 1) i then
            (L i).tensorPow (Function.update n j (n j + 1) i).toNat
          else (L i).dual.tensorPow (-Function.update n j (n j + 1) i).toNat).foldl
            (fun M N : X.Modules => M ⊗ N) F).eulerChar k) -
        (((List.ofFn fun i : Fin r =>
          if 0 ≤ n i then (L i).tensorPow (n i).toNat
          else (L i).dual.tensorPow (-n i).toNat).foldl
            (fun M N : X.Modules => M ⊗ N) F).eulerChar k) =
        ∑ a : Fin m, c a *
          (((List.ofFn fun i : Fin r =>
            if 0 ≤ n i then (L i).tensorPow (n i).toNat
            else (L i).dual.tensorPow (-n i).toNat).foldl
              (fun M N : X.Modules => M ⊗ N) (G a)).eulerChar k) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
