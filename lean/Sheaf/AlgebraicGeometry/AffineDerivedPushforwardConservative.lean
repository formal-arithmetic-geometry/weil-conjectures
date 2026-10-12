/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.FiniteAffineDerivedEquivalence

/-!
# Affine derived direct image reflects isomorphisms

Source: Stacks Project, Derived Categories of Schemes, Tag 08I8,
Lemma 36.5.2 (blueprint: lem-sc-affine-derived-pushforward-conservative).
-/

@[expose] public section

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

/-- For an affine morphism of schemes, derived direct image reflects isomorphisms
between objects with quasi-coherent cohomology.
Source: Stacks Project, Tag 08I8, Lemma 36.5.2
(blueprint: lem-sc-affine-derived-pushforward-conservative).

Proof:
1. By `lem-sc-finite-affine-derived-equivalence` (Stacks, Tag 0AVW), affine direct
   image gives an equivalence from `D_QCoh(𝒪_X)` to `D_QCoh(f_*𝒪_X)` whose composite
   with restriction of scalars is `Rf_*`. Restriction of scalars reflects isomorphisms:
   the cone of a morphism of `f_*𝒪_X`-complexes is acyclic exactly when its underlying
   `𝒪_Y`-complex is acyclic, since restriction does not change cohomology groups.
   Thus invertibility of `Rf_*u` implies invertibility of the image of `u` under
   this equivalence.
2. An equivalence reflects isomorphisms: apply its quasi-inverse to the inverse
   obtained in step 1 and use the unit and counit isomorphisms to obtain an inverse
   to `u`. Consequently `u` is an isomorphism. -/
theorem schemeDerivedDirectImage_isIso_of_affine
    {X Y : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [IsAffineHom f]
    {E F : schemeDerivedCategory X}
    (hE : schemeDerivedQCohProperty X E) (hF : schemeDerivedQCohProperty X F)
    (u : E ⟶ F) [IsIso ((schemeDerivedDirectImage f).map u)] : IsIso u := by
  sorry

end AlgebraicGeometry
