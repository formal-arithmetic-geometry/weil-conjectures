/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullbackAcrossUniverses
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure

/-! # Monoidal comparison with the standard derived localization

Source: Stacks Project, Tags 079U and 05RU.
(blueprint: lem-sc-standard-derived-equivalence-monoidal).
-/

@[expose] public section
set_option autoImplicit false
universe u wX
open CategoryTheory
namespace AlgebraicGeometry
/-- The specified equivalence to the standard localization preserves the fixed
K-flat derived tensor and its unit. Source: Stacks Project, Tags 079U and 05RU,
with the identity morphism in 079U and the localization universal property.
(blueprint: lem-sc-standard-derived-equivalence-monoidal).

Proof: write E for schemeDerivedStandardEquivalence X. Its canonical comparison
Qh ⋙ E.functor ≅ Qh_standard identifies localized representatives. For K-flat
complexes P and N, identify their derived tensor with the localization of their
ordinary total tensor complex in both localizations. Conjugating these two
comparison isomorphisms by the factorization of E yields an invertible map
E(P) tensor E(N) -> E(P tensor N). The unit is the localization of the structure
sheaf in degree zero in both categories, so the same factorization gives its
invertible comparison. Extend the tensor maps to arbitrary objects through K-flat
resolutions. Naturality of the localization factorization and tensor comparisons
shows independence of the resolutions and naturality in both arguments.
Resolve three arguments simultaneously: associativity is the image of the
associativity of the total tensor complex; the comparison maps cancel. Resolving
one argument and using the structure sheaf as the other gives both unit laws.
The localization universal property descends these equalities to all objects.
Package the maps and these laws as CoreMonoidal. No condition on X or on the
chosen localization universe is required; zero complexes and empty schemes use
the same construction. -/
theorem exists_schemeDerivedStandardEquivalence_monoidal
    (X : Scheme.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    Nonempty ((schemeDerivedStandardEquivalence X).functor.CoreMonoidal) := by sorry
end AlgebraicGeometry
