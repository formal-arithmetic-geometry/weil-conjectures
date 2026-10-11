/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Descent of etaleness at a prime under field extension

Source: Stacks Project, Tags 0C4Y, 02L2, 02KY and 02VM, packaged in primewise affine form
(blueprint: lem-sc-etale-local-ring-faithfully-flat-descent).
-/

@[expose] public section

universe u v w z

open TensorProduct

namespace Algebra

/-- Etaleness at a prime descends under extension of the ground field.
Source: Stacks Project, Tags 0C4Y, 02L2, 02KY and 02VM
(blueprint: lem-sc-etale-local-ring-faithfully-flat-descent).

The algebra structure on `B ⊗[k] K` over `A ⊗[k] K` is induced by the tensor product of
`A → B` with the identity of `K`. The primes `p` and `p_K` in the node are the contractions
of `q` and `qK` along these algebra maps; they are auxiliary notation, not extra hypotheses.

Proof, following the four steps of the node:
1. The map `B_q → (B ⊗[k] K)_{qK}` is faithfully flat by
   [lem-sc-etale-local-ring-stalk-faithfully-flat].
2. Apply the same lemma to `A` to obtain faithful flatness over `A_p`. Finite presentation
   survives base change. The criterion [lem-sc-etale-at-prime-flat-unramified-criterion]
   makes the upper local ring flat over the upper base local ring. Compose flat maps and
   use [lem-weil-pbc-flat-permanence] to descend flatness to `A_p → B_q`.
3. By [lem-weil-pbc-kahler-differentials-base-change], the localized differentials upstairs
   are the faithfully flat scalar extension of those downstairs. They vanish upstairs by
   the same etale criterion, hence downstairs by [lem-sc-faithfully-flat-tensor-zero].
4. Apply [lem-sc-etale-at-prime-flat-unramified-criterion] to the finitely presented
   `A`-algebra `B`: flatness at `q` and vanishing differentials imply etaleness at `q`. -/
theorem IsEtaleAt.of_fieldExtension
    (k : Type u) (K : Type v) (A : Type w) (B : Type z)
    [Field k] [Field K] [Algebra k K] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    [FinitePresentation A B]
    (q : Ideal B) [q.IsPrime] (qK : Ideal (B ⊗[k] K)) [qK.IsPrime]
    (hq : Ideal.comap (Algebra.TensorProduct.includeLeftRingHom (R := k) (B := K)) qK = q) :
    letI : Algebra (A ⊗[k] K) (B ⊗[k] K) :=
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A B) (AlgHom.id k K)).toRingHom.toAlgebra
    IsEtaleAt (A ⊗[k] K) qK → IsEtaleAt A q := by
  sorry

end Algebra
