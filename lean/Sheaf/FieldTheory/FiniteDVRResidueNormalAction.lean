/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Normal residue extensions and decomposition actions

Source: Stacks Project, More on Algebra, Tag 09ED (`lemma-galois-galois`),
assertions (1)--(2), in `literature/stacks-project/more-algebra.tex`.
(blueprint: lem-exc-dvr-residue-normal-action)

## Main declarations

* `IsDiscreteValuationRing.residueNormalActionHom`: the canonical residue action.
* `IsDiscreteValuationRing.residue_normal_action`: normality and surjectivity.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped Pointwise

namespace IsDiscreteValuationRing

/-- The canonical maximal-ideal-over-residue-field instance.

Source: Stacks Project, More on Algebra, Tag 09ED (`lemma-galois-galois`).
This uses maximal contraction for an integral extension and uniqueness of the
maximal ideal of a local ring, through the existing Mathlib declarations.
(blueprint: lem-exc-dvr-residue-normal-action)
-/
instance residueNormalLiesOverInstance
    (A : Type u) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field L] [Algebra A L]
    (n : Ideal (integralClosure A L)) [n.IsMaximal] :
    n.LiesOver (IsLocalRing.maximalIdeal A) :=
  Ideal.LiesOver.mk (IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n)).symm

/-- The residue field of the DVR as a quotient field.

Source: Stacks Project, More on Algebra, Tag 09ED (`lemma-galois-galois`).
(blueprint: lem-exc-dvr-residue-normal-action)
-/
@[instance_reducible]
noncomputable instance residueNormalBaseField
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    Field (A ⧸ IsLocalRing.maximalIdeal A) :=
  Ideal.Quotient.field _

/-- The residue quotient of a maximal integral-closure ideal as a field.

Source: Stacks Project, More on Algebra, Tag 09ED (`lemma-galois-galois`).
(blueprint: lem-exc-dvr-residue-normal-action)
-/
@[instance_reducible]
noncomputable instance residueNormalQuotientField
    (A : Type u) (L : Type w) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field L] [Algebra A L] (n : Ideal (integralClosure A L)) [n.IsMaximal] :
    Field (integralClosure A L ⧸ n) :=
  Ideal.Quotient.field _

/-- The canonical residue-action homomorphism from the decomposition group.

Source: Stacks Project, More on Algebra, Tag 09ED (`lemma-galois-galois`),
assertions (1)--(2).
(blueprint: lem-exc-dvr-residue-normal-action)
-/
noncomputable def residueNormalActionHom
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : Ideal (integralClosure A L)) [n.IsMaximal] :
    MulAction.stabilizer (Gal(L / K)) n →*
      (integralClosure A L ⧸ n) ≃ₐ[A ⧸ IsLocalRing.maximalIdeal A]
        (integralClosure A L ⧸ n) :=
  Ideal.Quotient.stabilizerHom n (IsLocalRing.maximalIdeal A) (Gal(L / K))

/-- For a finite normal separable extension of the fraction field of a DVR, the
residue extension at a maximal ideal of the integral closure is normal, and every
residue-field automorphism lifts to its decomposition group.

Source: Stacks Project, More on Algebra, Tag 09ED (`lemma-galois-galois`),
assertions (1)--(2); the proof uses `A = B^G` and Tag 0BRJ
(`lemma-one-orbit-geometric`).
(blueprint: lem-exc-dvr-residue-normal-action)

Proof:
1. A DVR is a PID and hence integrally closed in its fraction field. The finite
   normal separable extension has a finite Galois automorphism group with fixed
   field K, by `lem-weil-pbc-pid-noetherian-normal` and
   `lem-weil-pbc-finite-galois-fixed-field`.
2. The canonical integral closure is stable under this action: applying an
   automorphism and its inverse to a monic equation preserves integrality.
3. The fixed subring is A, using the fixed-field and integral-closedness clauses.
4. The contraction of a maximal ideal of the integral closure is maximal by
   `lem-weil-pbc-integral-algebra-ideal-in-radical`; locality of A identifies it
   with its maximal ideal.
5. Apply `lem-exc-finite-invariant-quotient-normal-action`, the invariant-ring
   quotient normality and stabilizer-surjectivity results (Tag 0BRJ), with
   R=A, S=integralClosure A L, H=Gal(L/K),
   p=maximalIdeal A and q=n. These give `Normal` of the residue extension and
   surjectivity of the displayed residue-action homomorphism. No separability
   assumption on the residue extension is used.
-/
theorem residue_normal_action
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L] [IsGalois K L]
    (n : Ideal (integralClosure A L)) [n.IsMaximal] :
    Normal (A ⧸ IsLocalRing.maximalIdeal A)
        (integralClosure A L ⧸ n) ∧
      Function.Surjective (residueNormalActionHom A K L n) := by
  have : Algebra.IsInvariant A (integralClosure A L) (Gal(L / K)) := by
    constructor
    intro b hb
    have hf : ∀ σ : Gal(L / K), σ (b : L) = (b : L) := fun σ ↦
      congrArg (fun x : integralClosure A L ↦ (x : L)) (hb σ)
    obtain ⟨k, hk⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (b : L)).mpr hf
    have hi : IsIntegral A k := by
      apply (isIntegral_algebraMap_iff (algebraMap K L).injective).mp
      rw [hk]
      exact b.property
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
    refine ⟨a, Subtype.ext ?_⟩
    change algebraMap A L a = (b : L)
    rw [IsScalarTower.algebraMap_apply A K L a, ha, hk]
  exact ⟨Ideal.Quotient.normal (Gal(L / K)) (IsLocalRing.maximalIdeal A) n,
    Ideal.Quotient.stabilizerHom_surjective (Gal(L / K)) (IsLocalRing.maximalIdeal A) n⟩

end IsDiscreteValuationRing
