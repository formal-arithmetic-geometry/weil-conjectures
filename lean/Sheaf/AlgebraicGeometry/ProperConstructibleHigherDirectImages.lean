/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImages
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
import Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleQcqsAffineLocal
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import Sheaf.AlgebraicGeometry.ReductionUniversalHomeomorphism
import Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.AlgebraicGeometry.ConstructibleModificationTransfer
import Sheaf.AlgebraicGeometry.DerivedOpenRestriction
import Sheaf.AlgebraicGeometry.NoetherianChowModification
import Sheaf.AlgebraicGeometry.ProjectiveConstructibleHigherDirectImages

/-!
# Proper direct-image constructibility

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
`thm-fin-proper-constructibility-complete.md`, statement and proof
(blueprint: thm-fin-proper-constructibility-complete).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Every proper morphism between finite-type schemes over a field satisfies `C(f)`:
each nonnegative higher direct image of a constructible finite-coefficient module sheaf
is constructible, with no uniform vanishing assertion.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/`,
`thm-fin-proper-constructibility-complete.md`, statement and proof
(blueprint: thm-fin-proper-constructibility-complete).

Proof plan:
1. A field is Noetherian. Finite type over a Noetherian scheme makes `X` and `S`
   Noetherian (`lem-weil-pbc-finite-type-over-noetherian`), hence quasi-compact and
   quasi-separated (`lem-weil-pbc-locally-noetherian-quasi-separated`). Work degree by
   degree with the coefficients of `def-finrepair-property-c`.
2. Reduce to affine targets: restrict to an affine open and base change the proper map
   (`lem-weil-pbc-proper-base-change`). Noetherian opens are quasi-compact, hence still
   finite type over the field. Restrict the constructible partition
   (`def-weil-pbc-constructible-complexes`). Derived open restriction
   (`lem-weil-pbc-derived-open-restriction`) and exact module inverse image
   (`prop-weil-pbc-inverse-image-modules-exact`) identify the restricted higher direct
   images. Glue by `lem-weil-pbc-constructible-qcqs-affine-local`.
3. For each closed subset of `X` take its reduced induced subscheme and its proper
   composite to `S` (`lem-weil-pbc-closed-immersion-proper`). These schemes remain finite
   type. The empty subset has zero direct images, which are constructible. If any subset
   fails `C`, choose a minimal nonempty failing subset `Z` using
   `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`.
4. Apply `lem-fin-noetherian-chow-modification` to `Z` over the affine Noetherian target:
   obtain a proper modification `Y → Z`, an isomorphism over a dense open `U`, with
   projective composite to `S`. Projective-space charts and the closed embedding
   (`def-pc-projective-morphism`) make `Y` finite type over the field. Apply
   `thm-fin-projective-constructibility-complete` to obtain `C` for that composite.
5. The reduced closed complement of `U` is a proper closed subset of `Z`, so minimality
   gives `C` for its map to `S`. Apply `lem-finrepair-modification-c` to obtain `C` for
   `Z`, a contradiction. In particular `C` holds for the reduction of `X`.
6. The reduction immersion is a universal homeomorphism
   (`lem-weil-pbc-reduction-universal-homeomorphism`). Topological invariance
   (`thm-weil-pbc-universal-homeomorphism-invariance`) gives quasi-inverse exact functors,
   also for constant-coefficient modules, by transporting the scalar action. Inverse
   image preserves the finite constructible partition. Choose an injective resolution
   on the reduction (`lem-weil-pbc-module-sheaves-enough-injectives`); its direct image
   under the exact equivalence remains an injective resolution. The sectionwise formula
   (`def-weil-pbc-direct-image`) identifies the composite direct image with that for the
   reduction-to-`S` map, so their higher direct images agree. Their constructibility gives
   the affine-target assertion, and step 2 proves the global assertion. -/
theorem hasConstructibleHigherDirectImages_of_proper
    (k : Type u) [Field k] (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X S : Scheme.{u}} [X.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (hX : IsSmoothBaseChangeCoefficients N Λ X)
    (hS : IsSmoothBaseChangeCoefficients N Λ S) (f : X ⟶ S) [IsProper f] :
    HasConstructibleHigherDirectImages k N Λ hX hS f := by
  sorry

end AlgebraicGeometry.Etale
