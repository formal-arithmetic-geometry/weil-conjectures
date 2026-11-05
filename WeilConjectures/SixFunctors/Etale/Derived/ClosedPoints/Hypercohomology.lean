/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.MinimalCohomology

/-!
# Cohomology of complexes with acyclic cohomology objects

Let `F : C ⥤ D` be a left exact functor, `C` with enough injectives and K-injective
resolutions, and `K ∈ D^{≥ m}(C)` all of whose homology objects `H^q(K)` are `F`-acyclic
(`R^p F(H^q K) = 0` for `p > 0`). Then `H^n(RF(K)) ≅ F(H^n K)` for all `n`: by induction on the
length, a bounded complex `L ∈ D^{≤ a}` with `F`-acyclic homology has `H^j(RF(L)) = 0` for
`j > a`, and the truncation triangles then identify `H^n(RF(K))` with
`H^n(RF(H^n(K)[-n])) = F(H^n K)`.

## Main statements

- `CategoryTheory.Functor.nonempty_homology_rightDerivedFunctor_obj_iso_of_acyclic`.
- `AlgebraicGeometry.Etale.nonempty_homology_rightDerivedGlobalSections_obj_iso_of_acyclic`
  (`lem-kun-0bkz`, bounded below case).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]

variable {F}

variable (F)

variable [PreservesFiniteLimits F]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

end AlgebraicGeometry.Etale
