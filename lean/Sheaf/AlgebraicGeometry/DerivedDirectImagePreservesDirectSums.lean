/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

/-! # Derived direct image preserves direct sums

Source: literature/stacks-project/perfect.tex,
Lemma perfect-lemma-quasi-coherence-pushforward-direct-sums
(blueprint: lem-pc-derived-direct-image-preserves-direct-sums).
-/

@[expose] public section

universe u₁ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For a quasi-compact and quasi-separated morphism of schemes, derived direct image
preserves every set-indexed coproduct of objects with quasi-coherent cohomology.
Source: literature/stacks-project/perfect.tex,
Lemma perfect-lemma-quasi-coherence-pushforward-direct-sums
(blueprint: lem-pc-derived-direct-image-preserves-direct-sums).

Proof (the three steps of the node):
1. Check the comparison on affine opens of the target. On each such open, use
   `lem-pc-derived-direct-image-uniform-truncation-bound` to choose one positive N
   for the entire family. The truncation triangle for T = τ≤(-N-1)E gives
   H⁰(Rf_*T) = H¹(Rf_*T) = 0, since T[-N-1] has no positive cohomology.
   Thus H⁰(Rf_*E) = H⁰(Rf_*τ≥(-N)E). Truncation commutes with direct sums,
   reducing all objects and their sum to the common lower bound -N.
2. Apply `thm-sp-truncation-e2`: its natural E₂ page is Rᵖf_*Hᑫ(E). On each
   affine V in the target, f⁻¹V is qcqs. Use
   `lem-weil-pbc-qcqs-cohomology-direct-sum` there, then
   `lem-weil-pbc-higher-direct-image-presheaf` and
   `lem-weil-pbc-module-sheaves-colimits-forgetful` to sheafify the comparison
   and obtain commutation of Rᵖf_* with the sum of the quasi-coherent Hᑫ(Eᵢ).
   Cohomology commutes with sums, so the E₂ pages agree. In total degree zero
   only 0 ≤ p ≤ N occurs; induction on the finite filtrations gives the H⁰
   comparison isomorphism.
3. Repeat with Eᵢ[k] for each integer k. Shifts commute with sums and Rf_*,
   so the comparison is an isomorphism on every cohomology sheaf, hence an
   isomorphism in the derived category. By
   `lem-pc-derived-direct-image-preserves-qcoh`, its image lies in the full
   quasi-coherent subcategory of the target, where the same coproduct applies. -/
theorem derivedDirectImagePreservesDirectSums {X Y : Scheme.{u₁}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace))] :
    ∀ (I : Type u₁) (E : I → schemeDerivedQCohCategory X),
      PreservesColimit (Discrete.functor (fun i => (E i).obj))
        (schemeDerivedDirectImage f) := by
  sorry

end AlgebraicGeometry
