/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit
import Sheaf.Paper.FiniteHypercoverDescent
import Sheaf.Paper.FiniteSplitHypercoverRefinement
import Sheaf.Paper.HypercoverCohomology
import WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity

/-!
# Descent of an etale cohomology class to a finite stage

Source: the first proof step of blueprint lemma-weil-pbc-etale-cohomology-continuity;
Stacks Project, Tags 03Q6 and 09YQ.
(blueprint: lem-weil-pbc-etale-cohomology-class-descent)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Every class on the limit is the pullback of a class at a stage mapping to `i`.
This is only the class-descent part of continuity; it asserts no eventual vanishing.

Source: blueprint lemma-weil-pbc-etale-cohomology-continuity, proof step 1 and
blueprint_sketch proof paragraph beginning "Let alpha"; Stacks Tags 03Q6 and 09YQ.
(blueprint: lem-weil-pbc-etale-cohomology-class-descent)

Proof:
1. Restrict the system to `Over i`. Its forgetful functor is initial, so the
   restricted cone is still a limit. The new stage sheaves are the pullbacks of F.
   The limit is qcqs since the projections of an affine-transition limit are affine.
2. By thm-weil-pbc-hypercover-cohomology, choose a finite split hypercover and a
   degree-q cocycle representing the given class. Compare the derived-global-sections
   encoding there with Sheaf.H using lem-weil-pbc-ext-via-injective-resolution: global
   sections are Hom from the constant integer sheaf, and their resolution complexes
   therefore agree. The pullback identification is the resolution comparison of
   lem-weil-pbc-cohomology-pullback-derived-unit.
3. Descend the skeleton through degree q+1 by lemma-weil-pbc-finite-hypercover-descent.
   Only finitely many components, structure maps, identities and matching covers occur.
   The descended skeleton extends to a split hypercover by successively choosing finite
   etale covers of the matching objects, as in lem-weil-pbc-hypercover-refinement.
4. On the finite degree-q components, lem-weil-pbc-etale-section-continuity descends
   the cocycle sections, after a finite refinement if needed. Cofilteredness supplies
   one stage for all components. Apply the equality part of section continuity to the
   finitely many equations saying that the alternating differential is zero. Move to
   one later stage where they all hold.
5. The descended cocycle defines a stage cohomology class by the same hypercover
   comparison. Its pullback is the original cocycle, hence the original class. The
   comparison is natural for pullback, so the resulting equality is precisely the
   displayed cohomologyMap followed by upperStarComp inverse. For q=0 the same argument
   is descent of a section and its degree-one compatibility equations; there is no
   negative-degree cochain. Zero sheaves and empty schemes give the zero class. -/
theorem exists_cohomology_class_of_isLimit
    {J : Type u} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{u})
    [∀ j : J, CompactSpace (D.obj j)] [∀ j : J, QuasiSeparatedSpace (D.obj j)]
    [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i : J)
    (F : Sheaf (D.obj i).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsTorsion) (q : ℕ) :
    (∀ x : Sheaf.H (((c.π.app i)^*[AddCommGrpCat.{u + 1}]).obj F) q,
      ∃ (j : J) (f : j ⟶ i)
        (y : Sheaf.H (((D.map f)^*[AddCommGrpCat.{u + 1}]).obj F) q),
        Sheaf.H.map
          ((upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
            (c.π.app i) (c.w f).symm).inv.app F) q
          (cohomologyMap (c.π.app j) _ q y) = x) := by sorry

end AlgebraicGeometry.Etale
