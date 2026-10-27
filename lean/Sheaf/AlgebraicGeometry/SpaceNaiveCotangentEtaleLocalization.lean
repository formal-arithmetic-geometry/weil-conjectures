/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.AlgebraicGeometry.SpaceNaiveCotangentComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems

/-! # Étale localization of the naive cotangent complex of algebraic spaces

Source: Stacks Project, More on Morphisms of Spaces, Tag 0D0W,
lemma-NL-etale-localization
(blueprint: lem-sfb-space-naive-cotangent-etale-localization).

The derived restriction and the naive cotangent complexes use the existing small affine
étale ringed models, with their original regular functions and module section universes.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Simultaneous étale localization of source and target preserves the naive cotangent
complex as an object of the unbounded derived module category. The comparison is induced
by the canonical identifications of inverse-image structure sheaves and ring maps.
The square is only required to commute.

Source: Stacks Project, More on Morphisms of Spaces, Tag 0D0W,
lemma-NL-etale-localization
(blueprint: lem-sfb-space-naive-cotangent-etale-localization).

Proof:
1. Use lem-trf-space-enlarged-etale-ringed-site-model to identify p⁻¹ O_X with O_U
   and q⁻¹ O_Y with O_V. Compatibility with composition and the commuting square
   identify the pulled-back ring map p⁻¹ f⁻¹ O_Y → p⁻¹ O_X with g⁻¹ O_V → O_U:
   both structure maps pull regular functions back along U → Y. Restriction is exact
   by lem-pur-site-restriction-module-adjunction-exact, hence is represented termwise
   by the existing spaceEtaleDerivedRestriction.
2. Apply lem-sfb-topos-naive-cotangent-pullback to A = f⁻¹ O_Y and B = O_X and
   the geometric inverse image p⁻¹. It identifies the restriction of NL_{X/Y} with
   NL_{p⁻¹ B / p⁻¹ A} in the derived category, including its differential.
3. Substitute the ring-map identification from step 1. Renaming coefficients and
   polynomial variables preserves evaluation, its kernel and its square, Kähler
   differentials and tensor products. It sends [h] ↦ dh ⊗ 1 to the differential
   defining NL_{U/V}. Compose the comparisons. No cartesian hypothesis is used. -/
theorem naiveCotangent_etaleLocalization
    {S : Scheme.{u}} {X Y U V : AlgebraicSpace S}
    (f : X ⟶ Y) (g : U ⟶ V) (p : U ⟶ X) (q : V ⟶ Y)
    (hp : IsEtale p.hom.hom) (hq : IsEtale q.hom.hom)
    (sq : p ≫ f = g ≫ q)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} U.SmallModules] :
    Nonempty ((spaceEtaleDerivedRestriction p hp).obj (naiveCotangent f) ≅
      naiveCotangent g) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
