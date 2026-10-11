/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Continuity of etale cohomology at inverse limits

Source: blueprint `sec-curve-estimates/sk-prop-h2`, lemma Etale cohomology continuity
(blueprint: lemma-weil-pbc-etale-cohomology-continuity); Stacks Project, Tag 03Q6.

The canonical filtered-colimit isomorphism is stated by its elementwise criterion:
every limit class descends, and every stage class in the kernel eventually vanishes.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Etale cohomology of a torsion sheaf descending to a stage of a cofiltered qcqs
system with affine transition morphisms is the filtered colimit of stage cohomology.
The two conjuncts express surjectivity and injectivity of the canonical comparison,
with the indexing category of later stages given by arrows `f : j ⟶ i`.
The composition isomorphism identifies iterated inverse images with direct inverse images.

Source: blueprint `sec-curve-estimates/sk-prop-h2`, Etale cohomology continuity;
Stacks Project, Tag 03Q6 (the base-change case of the continuity theorem).
(blueprint: lemma-weil-pbc-etale-cohomology-continuity).

Proof:
1. By `thm-weil-pbc-hypercover-cohomology`, represent a limit class by a cocycle on a
   hypercover finite in each degree. Descend its truncation through degree `q+1` by
   `lemma-weil-pbc-finite-hypercover-descent`. Descend the cocycle sections and the
   equation that their differential is zero by `lem-weil-pbc-etale-section-continuity`.
   The descended cocycle represents a stage class, proving surjectivity.
2. Represent a stage class by a hypercover cocycle using the same cohomology theorem.
   If it vanishes on the limit, that theorem and `lem-weil-pbc-hypercover-refinement`
   provide a refinement where it is a boundary. Descend the truncated refinement, its
   map to the original hypercover, a primitive, and the boundary equation by the same
   descent and section-continuity lemmas. The class vanishes at that later stage.
   For degree zero descend the equation that the section is zero directly.
   These maps are pullbacks, so the comparison is the canonical map, natural in the
   sheaf and the inverse system. -/
theorem cohomology_continuity_of_isLimit
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
          (cohomologyMap (c.π.app j) _ q y) = x) ∧
    (∀ (j : J) (f : j ⟶ i)
      (y : Sheaf.H (((D.map f)^*[AddCommGrpCat.{u + 1}]).obj F) q),
      Sheaf.H.map
        ((upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
          (c.π.app i) (c.w f).symm).inv.app F) q
        (cohomologyMap (c.π.app j) _ q y) = 0 →
      ∃ (k : J) (g : k ⟶ j),
        Sheaf.H.map
          ((upperStarComp AddCommGrpCat.{u + 1} (D.map g) (D.map f)
            (D.map (g ≫ f)) (D.map_comp g f)).inv.app F) q
          (cohomologyMap (D.map g) _ q y) = 0) := by
  sorry

end AlgebraicGeometry.Etale
