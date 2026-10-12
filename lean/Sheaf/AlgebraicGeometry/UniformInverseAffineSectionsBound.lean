/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Sheaf.Topology.OpenModuleCohomology
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.LerayDegenerateSections
import Sheaf.Topology.RestrictInjectiveResolution
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech

/-! # Uniform cohomological dimension of inverse images of affine opens

Source: Stacks Project, Tags 01XJ and 01XK; Tag 08D5, proof of (2).
(blueprint: lem-pc-uniform-inverse-affine-sections-bound).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A single positive bound works for ordinary module cohomology on the inverse image
of every affine open of the target.
Source: Stacks Project, Tags 01XJ and 01XK; Tag 08D5, proof of (2).
(blueprint: lem-pc-uniform-inverse-affine-sections-bound).

Proof:
1. Choose the base-change-stable bound n from Tag 01XJ for f and replace it by
max(1,n). For an affine open U, its inverse image V maps to U by the base change
of f. Restriction of a quasi-coherent module M on X to V is quasi-coherent.
2. Tag 01XJ gives quasi-coherence of every higher direct image of this restriction
and its vanishing in degrees p >= max(1,n). Affine vanishing makes all positive
cohomology of those higher direct images zero. The Leray edge therefore identifies
H^p(V,M|V) with sections of the p-th higher direct image on U (Tag 01XK).
3. Those sections are zero in the specified range. Restriction of an injective
module resolution to V remains injective; its sections on V are exactly the
openModuleSections functor applied to the resolution on X. Thus the same vanishing
holds for the right derived functors in the conclusion. The bound is independent
of U and M. Empty opens and zero modules give zero groups without exceptions. -/
theorem exists_uniform_inverse_affine_sections_bound
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace S] :
    ∃ N : ℕ, 0 < N ∧ ∀ (U : S.Opens), IsAffineOpen U →
      ∀ (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)), M.IsQuasicoherent →
        ∀ p : ℕ, N ≤ p → IsZero
          (((RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ U)).rightDerived p).obj M) :=
  by sorry

end AlgebraicGeometry
