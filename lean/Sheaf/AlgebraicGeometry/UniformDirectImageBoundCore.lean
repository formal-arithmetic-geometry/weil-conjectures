/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Uniform upper cohomological bound for quasi-coherent derived direct image

Source: Stacks Project, Tag 08D5, part (2)
(blueprint: lem-pc-uniform-direct-image-bound-core).
-/

@[expose] public section

universe u wX wS

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Uniform vanishing for nonpositive quasi-coherent derived objects.
Source: Stacks Project, Tag 08D5, part (2)
(blueprint: lem-pc-uniform-direct-image-bound-core).

Proof:
1. Choose the uniform higher-direct-image bound n₀ from Tag 01XJ, valid after
arbitrary base change, and enlarge it to N = max(1,n₀). For each affine open
U of S, the restricted morphism f_U has the same bound on quasi-coherent modules.
2. The higher direct images are quasi-coherent. Affine vanishing kills their
higher cohomology on U, so the Leray edge identifies H^p(f⁻¹U,M) with the
sections of R^p(f_U)_*M. These sections vanish for p ≥ N. The groups are the
right derived functors of global sections, by pqf-def-cohomology. Sections
commute with countable products: maps from the structure sheaf into a product
are precisely families of maps into its factors.
3. Restrict E to f⁻¹U; its cohomology stays quasi-coherent and has no positive
terms. Apply the unbounded derived-functor cohomological-bound theorem to
sections on f⁻¹U with b = 0. It gives vanishing in degrees m ≥ N. Derived
sections of pushforward agree with these derived sections. K-injective
restriction to opens justifies the restriction computation.
4. A K-injective representative I of Rf_*E computes derived sections on every
affine U. The sheaf H^m(I) is the sheafification of the presheaf
U ↦ H^m(Γ(U,I)); this presheaf vanishes on the affine basis by step 3.
Therefore its sheafification, and hence H^m(Rf_*E), is zero. This holds
uniformly for all E under consideration and all m ≥ N. -/
theorem uniform_bound_core
    {X S : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] [CompactSpace S] :
    ∃ N : ℤ, 0 < N ∧
      ∀ E : schemeDerivedQCohCategory X,
        (∀ m : ℤ, 0 < m → IsZero
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) m).obj E.obj)) →
        ∀ m : ℤ, N ≤ m → IsZero ((schemeHigherDirectImage f m).obj E.obj) := by
  sorry

end AlgebraicGeometry
