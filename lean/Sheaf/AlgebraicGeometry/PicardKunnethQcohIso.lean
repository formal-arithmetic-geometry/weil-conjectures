/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.DirectSum.Module
import Sheaf.Algebra.Homology.TensorKunnethNat
import Sheaf.AlgebraicGeometry.PicardKunnethCechModels

/-! # The isomorphism clause of the quasi-coherent Kunneth theorem

(blueprint: lem-sc-picard-kunneth-qcoh-iso-exists).
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct DirectSum

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option autoImplicit false

/-- The isomorphism clause of the quasi-coherent Kunneth theorem.
Source: Stacks Project, Varieties, Tag 0BED, Lemma varieties-lemma-kunneth.
(blueprint: lem-sc-picard-kunneth-qcoh-iso-exists).

Proof:
1. Obtain nonnegative Cech models A and B, their factor homology comparisons, and the
geometric tensor-total comparison from picard_kunneth_cech_models. This comparison
contains the affine-cover, dimension-shifting and Leray part of the source argument.
2. Apply tensor_kunneth_nat, which reindexes the integer-degree tensor_kunneth using
vanishing of every negative-degree tensor summand. Transport the direct sum by the
tensor products of the factor comparisons and compose with the geometric comparison.
3. Represent arbitrary factor cohomology classes by cycles using surjectivity of
homologyπ. The algebraic tensor formula supplies a total cycle representing their
tensor. The geometric comparison computes its class as externalCup; the inverse
factor comparisons cancel. This gives the required formula for all pure tensors,
including its degree cast. No finite-dimensionality or nonempty-scheme assumption
is used. -/
theorem picard_kunneth_iso_exists (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (Limits.pullback.diagonal f)] [IsAffineHom (Limits.pullback.diagonal g)]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    ∀ n : ℕ, ∃ e :
      (⨁ i : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
        scalarCohomology f F i.val.1 ⊗[k] scalarCohomology g G i.val.2) ≃ₗ[k]
          scalarCohomology (Limits.pullback.fst f g ≫ f) (externalCupCoefficients f g F G) n,
      ∀ (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
        (a : scalarCohomology f F i.val.1) (b : scalarCohomology g G i.val.2),
        e (DirectSum.lof k _
          (fun j : {pq : ℕ × ℕ // pq.1 + pq.2 = n} ↦
            scalarCohomology f F j.val.1 ⊗[k] scalarCohomology g G j.val.2) i
          (a ⊗ₜ[k] b)) =
          cast (congrArg (fun d ↦ ↥(scalarCohomology (Limits.pullback.fst f g ≫ f)
            (externalCupCoefficients f g F G) d)) i.property)
              (externalCup f g F G i.val.1 i.val.2 a b) := by
  classical
  obtain ⟨A, B, hA, hB, alpha, beta, gamma, hgamma⟩ :=
    picard_kunneth_cech_models k X Y f g F G
  intro n
  obtain ⟨e, he⟩ := HomologicalComplex.tensor_kunneth_nat A B hA hB n
  let d := DirectSum.congrLinearEquiv
    (fun i : {pq : ℕ × ℕ // pq.1 + pq.2 = n} ↦
      TensorProduct.congr (alpha i.val.1) (beta i.val.2))
  refine ⟨(d.trans e).trans (gamma n), ?_⟩
  intro i a b
  obtain ⟨a', ha'⟩ := (ModuleCat.epi_iff_surjective
    (A.homologyπ (i.val.1 : ℤ))).mp inferInstance (alpha i.val.1 a)
  obtain ⟨b', hb'⟩ := (ModuleCat.epi_iff_surjective
    (B.homologyπ (i.val.2 : ℤ))).mp inferInstance (beta i.val.2 b)
  obtain ⟨z, hz, hez⟩ := he i a' b'
  have hd : d (DirectSum.lof k _ _ i (a ⊗ₜ[k] b)) =
      DirectSum.lof k _ _ i ((alpha i.val.1 a) ⊗ₜ[k] (beta i.val.2 b)) := by
    simp [d, DirectSum.coe_congrLinearEquiv]
  change gamma n (e (d (DirectSum.lof k _ _ i (a ⊗ₜ[k] b)))) = _
  rw [hd, ← ha', ← hb', hez, hgamma n i a' b' z hz]
  simp only [ha', hb', LinearEquiv.symm_apply_apply]
end
end AlgebraicGeometry.Scheme.Modules
