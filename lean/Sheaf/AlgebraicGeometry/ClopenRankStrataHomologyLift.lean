/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.LocallyRankedExteriorComplex

/-! # Lifting a map from one clopen rank stratum

Source: rank-idempotent splitting and single-degree truncation in steps 1--2
of clopen rank-stratum formality (the expansion of the reconstruction argument
motivated by Stacks Tag 0BQZ). Supporting sources: Stacks Tags 00EE
(clopen idempotents), 0118 (canonical truncation), and 0AVW (algebra setup).
-/

@[expose] public section

universe u wA

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry

/-- A module in degree n supported on its clopen rank stratum maps into a
complex through its degree-n homology, provided all other homology degrees
are supported on their respective different rank strata. The degree-n
homology need not be prescribed, and the map need not be an isomorphism.
No finite-image assumption on the rank function is needed for this one-stratum
lifting statement.

Source: rank-idempotent splitting and single-degree truncation, steps 1--2
of `lem-sc-clopen-rank-strata-formality` (expanding the reconstruction argument
motivated by Tag 0BQZ); Stacks Tags 00EE (clopen idempotents), 0118
(canonical truncation), and 0AVW (direct-image algebra setup).
The rank-stratum expansion is written by the agent, not stated verbatim in 0BQZ.
(blueprint: lem-sc-clopen-rank-strata-homology-lift)

Proof: If n is negative then T n is zero, so its single complex is zero
and the unique zero map is a lift. Otherwise put q = n.toNat and U = {r = q}.
Glue 1 on U and 0 on its open complement to get the characteristic idempotent
of O_Z, hence of i_*O_Z. Multiplication by this central idempotent splits
any representative complex of K into its image and complementary image,
with chain inclusions and projections. This splitting is exact on module
sheaves, so the homology of the image complex is the image of multiplication
by the same idempotent on H^m(K). For m different from n, the given isomorphism
identifies H^m(K) with the direct image of T m. This module is zero when m
is negative and is supported on the disjoint rank-m stratum otherwise.
The idempotent therefore acts by zero on these homology sheaves. The image
complex has homology only in degree n; the two canonical truncations give
its derived isomorphism to its degree-n homology in degree n. The idempotent
acts as the identity on the source module g_*T n. Every module-linear map a
therefore lands in the idempotent image of H^n(K). Apply the single functor
to this factored map, compose with the inverse of the truncation isomorphism
and with the image-complex inclusion into K. The natural homology
identification of a single complex shows that this composite induces a.
The construction also covers an empty stratum: the source module and its
single complex are zero. Neither U nor its image has to be open in Y. -/
theorem clopenRankStrata_homology_lift
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{wA} (SheafOfModules.{u}
      (moduleRings (directImageAlgebraSpace i)))]
    (r : LocallyConstant Z ℕ)
    (E : ∀ n : ℕ, (Scheme.Modules.exteriorRankOpen r n).toScheme.Modules)
    (T : ℤ → Z.Modules)
    (hT : ∀ n : ℤ, T n = if 0 ≤ n then
      (Scheme.Modules.pushforward (Scheme.Modules.exteriorRankOpen r n.toNat).ι).obj
        (E n.toNat) else 0)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))))
    (n : ℤ)
    (hother : ∀ m : ℤ, m ≠ n → Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) m).obj K ≅
        (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).obj (T m)))
    (a : (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).obj (T n) ⟶
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).obj K) :
    ∃ f : (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).obj
          ((RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).obj (T n)) ⟶ K,
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).inv.app
          ((RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).obj (T n)) ≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).map f = a := by sorry

end AlgebraicGeometry
