/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.SymmetricProjAffineComparisonExistence

/-! # Degree-one section compatibility for affine symmetric Proj comparisons

Source: Stacks Project, Constructions, Tags 01NR, 01OB and 01N2.
(blueprint: lem-trf-symmetric-proj-normalized-descent).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomogeneousLocalization
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.SymmetricProjTautologicalCharts

/-- The affine comparison carries every normalized degree-one section to its
restriction.  Source: Stacks, Tags 01NR, 01OB and 01N2.
(blueprint: lem-trf-symmetric-proj-normalized-descent).

Proof: on a standard open, both sides are the section represented by the same
degree-one fraction.  The affine localization formula sends `a/1` to `res(a)/1`;
the boundary pullback comparison is exactly the canonical identification of the
pulled-back unit section.  Equality on standard opens and the affine tilde
equivalence give the displayed sheaf morphism equality. -/
theorem section_compatibility_of_affine_comparison
    {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
    (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (U V : S.affineOpens) (h : U ≤ V)
    (c : AffineComparison E D U V h) :
    ∀ (a : (SymmetricAlgebraSheaf.gradedAlgebraData E).obj V)
      (ha : a ∈ (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V 1),
      (Scheme.Modules.tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map (homOfLE h))).map
          (Proj.unitToTwist ha) ≫ c.comparison.hom =
        ((Scheme.Modules.boundaryPullbackComparison
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map
              (homOfLE h))).app (Scheme.Modules.unit _) ≪≫
          Scheme.Modules.pullbackObjUnitIso
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map
              (homOfLE h))).hom ≫
        Proj.unitToTwist
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).res h |>.map_mem ha) := by
  sorry

end AlgebraicGeometry.SymmetricProjTautologicalCharts
