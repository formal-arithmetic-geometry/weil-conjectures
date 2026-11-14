/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjOrderedRelativeComparison
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjOrderedTwistGluing
import WeilConjectures.AlgebraicGeometry.RelativeProjectiveSpace.FreeProjectiveBundleBaseChangeSpace

/-!
# Ordered free comparisons for the normalized symmetric Proj quotient

Source: Stacks Project, Constructions, Tags 01OE, 01OB and 01MS.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomogeneousLocalization
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.SymmetricProjTautologicalCharts

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  Scheme.Modules.tensorPullbackSectionComp Scheme.Modules.tensorPullbackSectionAdjunction
  Scheme.Modules.boundaryPullbackComparison

/-- Ordered free comparisons for the normalized symmetric Proj quotient.

Source: Stacks Project, Constructions, Tags 01OE, 01OB and 01MS. -/
theorem free_compatibility_of_normalized_quotient (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E) :
    ProjectiveBundleQuotientGeometry.HasFreeCompatibility D := by
  intro r b
  let eRel := orderedRelativeComparison b
  have hRel := orderedRelativeComparison_hom_π b
  have hAffine := orderedRelativeComparison_affineFreeComparison b
  obtain ⟨θ, hθ, _⟩ :=
    RelativeProjectiveSpace.existsUnique_freeProjectiveBundleBaseChangeSpace S r
  obtain ⟨t, ht⟩ := exists_ordered_twist_comparison S E D r b eRel hRel hAffine θ
    hθ.1 hθ.2.1
  refine ⟨eRel, eRel ≪≫ θ, t, hRel, ?_, ht, hAffine⟩
  change (eRel.hom ≫ θ.hom) ≫ _ = _
  rw [Category.assoc, hθ.1, hRel]

end AlgebraicGeometry.SymmetricProjTautologicalCharts
