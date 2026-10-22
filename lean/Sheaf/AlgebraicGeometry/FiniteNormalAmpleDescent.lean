/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.AmpleRestrictClosedImmersion
import Sheaf.AlgebraicGeometry.AmpleFinitePrincipalAffine
import WeilConjectures.AlgebraicGeometry.AffineCapSectionOpen

/-! # Existence of ample invertible modules descends to a normal integral scheme

Source: Stacks Project, Divisors, Tag 0BD4, proposition-push-down-ample, case (2),
using Tag 0BD0, lemma-norm-ample
(blueprint: lem-sfb-finite-normal-ample-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite surjective cover admitting an ample invertible module gives an ample invertible
module on its normal integral target.
Source: Stacks Project, Divisors, Tag 0BD4, proposition-push-down-ample, case (2),
and Tag 0BD0, lemma-norm-ample
(blueprint: lem-sfb-finite-normal-ample-descent).

Proof:
1. Choose a point over the generic point of `Z`, using `lem-weil-pbc-scheme-sober`
   and surjectivity. Its closure with the reduced induced structure from
   `lem-weil-pbc-reduced-induced-closed-subscheme` is an integral closed subscheme `Y` of `X`.
2. The composite `p : Y ⟶ Z` is finite by `lem-weil-pbc-closed-immersion-finite` and
   `lem-weil-pbc-finite-composition`. By `lem-weil-pbc-finite-closed-map-finite-fibres`,
   its image is closed and contains the generic point, hence it is surjective.
   Restrict an ample invertible module on `X` to `Y`, obtaining an ample module `M`
   by `lem-trf-ample-restrict-closed-immersion`.
3. Apply `lem-sfb-normal-integral-finite-sheaf-norm` to `p` and then
   `lem-sfb-finite-norm-invertible-sections` to `M`. Fix the resulting invertible module `N`
   on `Z`; this single choice works for all positive powers and sections.
4. The ample definition `def-weil-pbc-ample-invertible-module` makes `Y` quasi-compact.
   Pull back an open cover of `Z` to `Y`, take a finite subcover, and use surjectivity
   of `p` to see that the same finitely many opens cover `Z`.
5. Given `z` in `Z` and an affine open neighbourhood `V`, the fibre over `z` is finite
   by `lem-weil-pbc-finite-closed-map-finite-fibres`. Apply
   `lem-sc-ample-finite-principal-affine` to obtain a positive-power section `s` of `M`
   whose affine nonvanishing locus contains that fibre and lies over `V`.
6. By `lem-sfb-finite-norm-invertible-sections`, its norm is a section `t` of the same
   power of `N` whose nonvanishing locus consists exactly of points whose entire fibre
   lies in the nonvanishing locus of `s`. It contains `z` and, by surjectivity, lies in `V`.
   Thus `lem-sc-affine-cap-section-open` makes this nonvanishing locus affine.
7. For each `z` there is therefore a positive-power section of `N` with affine
   nonvanishing neighbourhood of `z`. Together with step 4, these are precisely the
   two clauses of `def-weil-pbc-ample-invertible-module`, proving that `N` is ample.
-/
theorem exists_isAmple_of_finite_surjective_normal
    {X Z : Scheme.{u}} (f : X ⟶ Z) [IsFinite f] [Surjective f] [IsIntegral Z]
    (hZ : ∀ z : Z, IsDomain (Z.presheaf.stalk z) ∧
      IsIntegrallyClosed (Z.presheaf.stalk z))
    (hX : ∃ L : X.Modules, ∃ hL : L.IsInvertible, @IsAmple X L hL) :
    ∃ N : Z.Modules, ∃ hN : N.IsInvertible, @IsAmple Z N hN := by
  sorry

end AlgebraicGeometry.Scheme.Modules
