/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Data.List.TFAE
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import Sheaf.AlgebraicGeometry.EtaleStratificationLocalGluingCore
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Affine locality of constructible etale module sheaves on qcqs schemes

Source: Stacks Project, Tags 095E and 03RW(3)
(blueprint: lem-weil-pbc-constructible-qcqs-affine-local).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- For finite module coefficients, affine-local constructibility, its validity on an
open cover, and a global constructible immersed partition are equivalent.
Reduced immersed representatives encode the reduced induced structure on local strata.
Source: Stacks Project, Tags 095E and 03RW(3)
(blueprint: lem-weil-pbc-constructible-qcqs-affine-local).

Proof plan:
1. Condition (1) implies (2) using the one-member open cover.
2. Finite locally constant module sheaves are preserved by pullback: pull back a
   trivializing etale cover (etale-covering-base-change), use upperStarConstantSheafIso
   with the same finite module values, and use the etale inverse-image/restriction
   comparison. Scalar naturality makes this a comparison of module sheaves. Composition
   of adjunctions and the conjugate unit equation identify composite inverse images.
   Immersion independence permits reduced representatives; finite-local-constant module
   values agree with the stalk formulation by finite_locally_constant_module_values_iff.
3. Under (2), choose affine neighbourhoods inside the cover and use compactness to
   extract finitely many, with the empty cover allowed on the empty scheme.
4. Apply exists_global_stratification_factoring_local to their partitions. Its actual
   factorization maps let step 2 pull the finite local systems to the global strata,
   proving (3) without assuming that image containment implies factorization.
5. Under (3), pull the partition back to any affine open. The constructible-preimage
   lemma gives constructibility of the traces in that open. Step 2 gives finite local
   constancy and transfers it to reduced representatives, proving (1). Empty traces
   are harmless; intersections of affine opens need not be affine.
6. These cyclic implications prove the three-way equivalence. -/
theorem constructible_etale_module_qcqs_affine_local
    {T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    List.TFAE [
      (∀ U : T.Opens, IsAffineOpen U →
        ∃ S : LocallyClosedStratification U.toScheme,
          (∀ k : Fin S.n, Topology.IsConstructible (S.stratum k)) ∧
          (∀ k : Fin S.n, IsReduced (S.domain k)) ∧
          ∀ k : Fin S.n,
            IsFiniteLocallyConstantSheaf
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion k ≫ U.ι)).obj F)),
      (∃ 𝒱 : Set T.Opens,
        (∀ x : T, ∃ V ∈ 𝒱, x ∈ V) ∧
        ∀ V ∈ 𝒱, ∀ U : V.toScheme.Opens, IsAffineOpen U →
          ∃ S : LocallyClosedStratification U.toScheme,
            (∀ k : Fin S.n, Topology.IsConstructible (S.stratum k)) ∧
            (∀ k : Fin S.n, IsReduced (S.domain k)) ∧
            ∀ k : Fin S.n,
              IsFiniteLocallyConstantSheaf
                ((Etale.upperStar (ModuleCat.{u + 1} Λ)
                  (S.immersion k ≫ U.ι ≫ V.ι)).obj F)),
      IsConstructibleEtaleModuleSheaf F] := by
  sorry

end AlgebraicGeometry.Scheme
