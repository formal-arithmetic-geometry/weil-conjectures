/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCoverDescentDatum
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.FppfAffineRefinement
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.FpqcCanonicalPullbackDatum
import WeilConjectures.AlgebraicGeometry.FpqcRefinementReflectsEffectivity
import WeilConjectures.AlgebraicGeometry.FpqcEffectivityOpenLocal
import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum

/-!
# Reduction of effective fppf descent to affine singleton covers

Source: Stacks Project, Descent, Tag 02W3, `lemma-descending-types-morphisms`,
specialized to fppf coverings (blueprint: lem-trf-fppf-family-affine-effectivity-reduction).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Effective descent for a base-change-stable morphism property reduces to affine singleton
covers. Source: Stacks Project, Descent, Tag 02W3, invoked in Tag 02W8
(blueprint: lem-trf-fppf-family-affine-effectivity-reduction).

Proof: Form the coproducts of the covering schemes and local schemes. Their open disjoint
components decompose all double and triple fibre products; glue the family transitions on
these components to obtain a singleton datum, as in Tag 023X. The coproduct cover is fpqc:
affine refinement supplies, over each affine open of the base, finitely many affine opens
whose images cover that open. Restrict the singleton datum to such an affine open. Its
finite affine refinement has affine coproduct, and its map to the affine base is flat,
surjective and locally of finite presentation. It is quasi-compact and quasi-separated
because a morphism between affine schemes is affine. Base-change stability gives the
property on each refined local scheme. Finite-coproduct stability, including the empty
case, gives the property on their coproduct. The affine singleton hypothesis makes the
canonical pulled-back datum effective. The fpqc refinement-reflects-effectivity lemma
then makes the restricted singleton datum effective. The affine-open-local effectivity
lemma glues these models over the original base. Restrict the resulting compatible
isomorphism to each open coproduct component to recover the required family realization.
No property of the infinite coproduct map, or of the final descended map, is asserted. -/
theorem fppf_family_isEffective_of_affine_singletons
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] [P.IsStableUnderBaseChange]
    (hfinite : ∀ (n : ℕ) (Y B : Fin n → Scheme.{u}) (h : ∀ j, Y j ⟶ B j),
      (∀ j, P (h j)) → P (CategoryTheory.Limits.Sigma.map h))
    (haffine : ∀ (A B : Scheme.{u}) [IsAffine A] [IsAffine B] (p : A ⟶ B),
      Flat p → Surjective p → LocallyOfFinitePresentation p → QuasiCompact p →
        QuasiSeparated p → ∀ (V : Over A) (D : Over.DescentDatum p V),
          P V.hom → D.IsEffective)
    {I : Type (u + 1)} (T : Scheme.{u}) (U : I → Scheme.{u}) (f : ∀ i, U i ⟶ T)
    (hcov : Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage T)
    (D : SchemeCoverDescentDatum f) (hP : ∀ i, P (D.localScheme i).hom) :
    D.IsEffective := by
  sorry

end AlgebraicGeometry
