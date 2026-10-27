/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Localization comparisons in a field tower

Source: Stacks Project, varieties.tex, Tag 0C4Y (lemma-change-fields-flat), proof of (3),
and algebra.tex, Tags 00D2, 00CX, 00DK, 00CP.
(blueprint: lem-trf-field-localization-tensor-comparison)

Tensor factors are written with the field first, using the canonical commutativity
isomorphism to the order in the node. This uses the standard left algebra actions.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open scoped TensorProduct

namespace Algebra

/-- The map `L ⊗[k] R → H ⊗[k] R` induced by the field tower.
Source: Stacks Project, varieties.tex, Tag 0C4Y, proof of (3).
(blueprint: lem-trf-field-localization-tensor-comparison) -/
abbrev fieldTowerTensorMap
    (k : Type u) (L : Type v) (H : Type w) (R : Type z)
    [Field k] [Field L] [Field H] [CommRing R]
    [Algebra k L] [Algebra L H] [Algebra k H] [IsScalarTower k L H] [Algebra k R] :
    L ⊗[k] R →ₐ[k] H ⊗[k] R :=
  TensorProduct.map (IsScalarTower.toAlgHom k L H) (AlgHom.id k R)

/-- Scalar extension of the two prime localizations gives compatible localizations
of `H ⊗[k] R`, and localization at an upstairs prime is a further localization.

Source: Stacks Project, varieties.tex, Tag 0C4Y (lemma-change-fields-flat), proof of (3).
(blueprint: lem-trf-field-localization-tensor-comparison)

Proof:
1. Use `lem-weil-pbc-module-base-change-transitive` to identify
   `H ⊗[L] (L ⊗[k] R)` with `H ⊗[k] R`. The pure-tensor multiplication formula of
   `lem-weil-pbc-algebra-tensor-pushout-universal-property` makes this a ring isomorphism.
2. Apply `lem-weil-pbc-localization-tensor-over-base` over k at R minus p. On fractions
   the resulting identification sends h tensor (r/v) to (h tensor r)/(1 tensor v).
   This preserves products and one, hence is a ring identification.
3. Apply the same localization-tensor result over L at S minus q and compose with
   step 1. It sends h tensor (s/u) to (h tensor 1)j(s)/j(u).
4. The contraction equality implies that the first denominator set lies in the second.
   `lem-weil-pbc-ring-localization-universal-property` supplies the induced map, and
   clause (2) of `lem-weil-pbc-localization-of-localization` gives its localization property.
5. For Q over q the second denominator set lies in T minus Q. The same universal
   property and localization-of-localization result give the final map and its property.
6. The formulas agree on T. Tensor-product extensionality and localization uniqueness
   show compatibility of all arrows and of the structural maps from R, L, and H. -/
theorem field_localization_tensor_comparison
    (k : Type u) (L : Type v) (H : Type w) (R : Type z)
    [Field k] [Field L] [Field H] [CommRing R]
    [Algebra k L] [Algebra L H] [Algebra k H] [IsScalarTower k L H] [Algebra k R]
    (q : Ideal (L ⊗[k] R)) [q.IsPrime]
    (p : Ideal R) [p.IsPrime]
    (hp : p = q.comap (TensorProduct.includeRight (R := k) (A := L)).toRingHom) :
    ∃ (eA : H ⊗[k] Localization.AtPrime p ≃+*
          Localization (p.primeCompl.map
            (TensorProduct.includeRight (R := k) (A := H)).toRingHom))
      (eB : H ⊗[L] Localization.AtPrime q ≃+*
          Localization (q.primeCompl.map (fieldTowerTensorMap k L H R).toRingHom))
      (f : H ⊗[k] Localization.AtPrime p →+* H ⊗[L] Localization.AtPrime q),
      (∀ (h : H) (r : R) (v : p.primeCompl),
        eA (h ⊗ₜ[k] Localization.mk r v) =
          Localization.mk (S := p.primeCompl.map
            (TensorProduct.includeRight (R := k) (A := H)).toRingHom) (h ⊗ₜ[k] r)
            ⟨1 ⊗ₜ[k] (v : R), ⟨v, v.property, rfl⟩⟩) ∧
      (∀ (h : H) (s : L ⊗[k] R) (u : q.primeCompl),
        eB (h ⊗ₜ[L] Localization.mk s u) =
          Localization.mk
            (S := q.primeCompl.map (fieldTowerTensorMap k L H R).toRingHom)
            ((h ⊗ₜ[k] (1 : R)) * fieldTowerTensorMap k L H R s)
            ⟨fieldTowerTensorMap k L H R u, ⟨u, u.property, rfl⟩⟩) ∧
      (∀ t : H ⊗[k] R,
        f (eA.symm (algebraMap _ _ t)) = eB.symm (algebraMap _ _ t)) ∧
      @IsLocalization _ _
        ((q.primeCompl.map (fieldTowerTensorMap k L H R).toRingHom).map
          (eA.symm.toRingHom.comp (algebraMap _ _))) _ _ f.toAlgebra ∧
      ∀ (Q : Ideal (H ⊗[k] R)) [Q.IsPrime],
        Q.comap (fieldTowerTensorMap k L H R).toRingHom = q →
        ∃ g : H ⊗[L] Localization.AtPrime q →+* Localization.AtPrime Q,
          (∀ t : H ⊗[k] R,
            g (eB.symm (algebraMap _ _ t)) = algebraMap _ _ t) ∧
          @IsLocalization _ _
            (Q.primeCompl.map (eB.symm.toRingHom.comp (algebraMap _ _))) _ _ g.toAlgebra ∧
          ∀ (t : H ⊗[k] R) (u : q.primeCompl)
            (d : Q.primeCompl), (d : H ⊗[k] R) = fieldTowerTensorMap k L H R u →
            g (eB.symm (Localization.mk t
              ⟨fieldTowerTensorMap k L H R u, ⟨u, u.property, rfl⟩⟩)) =
                Localization.mk t d := by
  sorry

end Algebra
