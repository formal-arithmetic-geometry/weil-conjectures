/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
# Restriction to an open preserves K-injective complexes

Source: literature/stacks-project/cohomology.tex, Lemma 08BS
(blueprint: lem-sc-derived-k-injective-restrict-open).
-/

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Restriction of a K-injective complex of modules on a ringed space to an open
subspace is K-injective.

Source: literature/stacks-project/cohomology.tex, Lemma 08BS.
Proof: (1) Restriction is exact and right adjoint to the exact extension-by-zero
functor by `AlgebraicGeometry.open_restriction_adjunction_exact`
(lem-sc-derived-open-restriction-adjunction-exact), so the exact-left-adjoint
hypothesis holds for the module categories on `U` and `X`.
(2) Apply `CategoryTheory.Adjunction.preservesKInjectiveComplexes`
(lem-weil-pbc-right-adjoint-preserves-kinjective) to this adjunction and the given
K-injective `I`. Its termwise restriction is therefore K-injective on `U`.
(blueprint: lem-sc-derived-k-injective-restrict-open). -/
theorem kInjective_of_restrict_open (X : RingedSpace.{u}) (U : Opens X)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ)
    [I.IsKInjective] :
    @CochainComplex.IsKInjective
      (SheafOfModules.{u} ((moduleRings X).over U)) _ _
      (((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  sorry

end AlgebraicGeometry
