/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.HilbertEmbeddedPointsGluing
import Sheaf.RingTheory.LocalizationEmbeddedPoints
import Sheaf.RingTheory.RemoveEmbeddedPrimes

/-! # Removing embedded associated points of a coherent module

Source: Stacks Project, Divisors, Tag 02OL (blueprint: lem-sc-hilbert-embedded-points).
The dimension clause is the additional support-dimension argument recorded in the DAG.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- A coherent module on a locally Noetherian scheme has a maximal coherent subobject
whose support is nowhere dense in the original support. Its quotient has the same support,
no embedded associated points, and agrees with the original module on a dense open which
also meets the support densely. The kernel support has strictly smaller dimension when the
original support has finite positive dimension.

Support means nonzero stalks. Nowhere density and density in the support use the subspace
topology. No embedded associated points is expressed on every affine open by minimality
of every associated prime of the section module, as in `lem-sc-hilbert-difference`.
Mathlib defines associated primes using radicals of annihilators; on the Noetherian
coordinate rings here, `isAssociatedPrime_iff` identifies this with the source's
annihilator definition. The affine correspondence in Divisors, Tag 02OK, and
`definition-embedded` in that chapter justify the affine formulation.
The quotient is the categorical cokernel of the subobject inclusion.
Source: Stacks Project, Divisors, Tag 02OL (blueprint: lem-sc-hilbert-embedded-points).

Proof:
1. On an affine open write F as the sheaf associated to a finite module M over a
   Noetherian ring A. Apply `lem-sc-hilbert-embedded-points-affine-removal` (Tag 02M6)
   to obtain the maximal submodule N with nowhere dense support. The quotient has the
   same support and no embedded primes, and agrees with M after localization away
   from the embedded primes.
2. `lem-sc-hilbert-embedded-points-affine-localization` (Tag 02M7) identifies these
   submodules on principal affine overlaps. Apply
   `lem-sc-hilbert-embedded-points-gluing` to glue them to a coherent submodule K.
3. The affine conclusions give maximality, equality of supports and the associated-point
   assertion globally. Take U to be the complement of the closure of the embedded
   associated points of F. It is dense in X and meets Supp(F) densely, and K vanishes
   there, giving the restriction isomorphism (Tag 02OL).
4. If d = dim Supp(F) is finite and positive, each irreducible component Z of Supp(K)
   is properly contained in an irreducible component W of Supp(F): components are locally
   finite on a locally Noetherian scheme (Tag 0052), and nowhere density excludes Z = W.
   Any chain in Z extends by W, so dim Z + 1 ≤ dim W ≤ d. Taking suprema gives
   dim Supp(K) ≤ d - 1 < d. For K = 0 its empty support has dimension bottom.
-/
theorem exists_maximal_nowhereDense_support_cokernel
    (X : Scheme.{u}) [IsLocallyNoetherian X] (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) :
    ∃ K : Subobject F,
      Maximal (fun L : Subobject F ↦
        RingedSpace.IsCoherent X.toRingedSpace (L : X.Modules) ∧
          IsNowhereDense {x : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} |
            ¬ Subsingleton ((L : X.Modules).presheaf.stalk x.val)}) K ∧
      {x : X | ¬ Subsingleton ((cokernel K.arrow : X.Modules).presheaf.stalk x)} =
        {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ∧
      (∀ (V : X.Opens) (_ : IsAffineOpen V) (p : Ideal Γ(X, V)),
        p ∈ associatedPrimes Γ(X, V) Γ((cokernel K.arrow : X.Modules), V) →
          Minimal (fun q : Ideal Γ(X, V) ↦
            q ∈ associatedPrimes Γ(X, V) Γ((cokernel K.arrow : X.Modules), V)) p) ∧
      (∃ U : X.Opens, Dense (U : Set X) ∧
        Dense {x : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} | x.val ∈ U} ∧
        Nonempty ((cokernel K.arrow : X.Modules).over U ≅ F.over U)) ∧
      (∀ d : ℕ, 0 < d →
        topologicalKrullDim {x : X | ¬ Subsingleton (F.presheaf.stalk x)} =
          (d : WithBot ℕ∞) →
        topologicalKrullDim {x : X | ¬ Subsingleton ((K : X.Modules).presheaf.stalk x)} <
          topologicalKrullDim {x : X | ¬ Subsingleton (F.presheaf.stalk x)}) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
