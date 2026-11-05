/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.Defs.Filter
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeFibreDimensionBound
import WeilConjectures.AlgebraicGeometry.SmoothPurity.DimensionExtension
import WeilConjectures.AlgebraicGeometry.SmoothPurity.SeparablyClosedTorsionCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeTorsionCohomologicalDimension

/-!
# Uniform torsion cohomology bound for proper geometric fibres

Source: Stacks Project, Tags 0A3V (lemma-morphism-finite-type-bounded-dimension),
00P3 (lemma-dimension-preserved-field-extension), and 0F0V (proposition-cd-affine),
with the blueprint finite-type torsion cohomological-dimension bound, applied in
sec-six-functors-basics/sk-thm-sfb-proper-base-change,
sk-thm-sfb-proper-base-change-finite.proof.md, paragraph (1).
(blueprint: lem-sfb-proper-geometric-fibre-torsion-bound)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

end AlgebraicGeometry
