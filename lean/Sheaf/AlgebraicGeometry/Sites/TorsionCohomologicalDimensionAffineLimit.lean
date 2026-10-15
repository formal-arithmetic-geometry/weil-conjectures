/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.IsLimit
import Sheaf.Paper.EtaleFiniteDataDescent
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings
import Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import Sheaf.AlgebraicGeometry.TorsionFilteredUnion

/-!
# Torsion cohomological dimension at an affine inverse limit

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
lem-sc-cd-affine-limit.md (blueprint: lem-sc-cd-affine-limit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A uniform torsion étale cohomological dimension bound passes to a cofiltered
limit of quasi-compact quasi-separated schemes with affine transition morphisms.

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc, lemma lem-sc-cd-affine-limit,
statement and proof (blueprint: lem-sc-cd-affine-limit).

Proof:
1. The projections are affine by lem-weil-pbc-limit-cone-affine-projections-opens.
   Pull back a finite affine cover of a stage, and finite affine covers of its
   intersections. The criterion lem-weil-pbc-quasi-separated-affine-cover-criterion
   shows that the limit is quasi-compact and quasi-separated. For a sheaf F killed
   by n > 0, put F_i = p_{i*} F using def-weil-pbc-direct-image. The adjunction of
   def-weil-pbc-inverse-image supplies compatible transitions and a cocone to F.
   The canonical colimit of p_i^* F_i is F: affine étale basis objects are of finite
   presentation by lem-weil-pbc-qcqs-morphism-permanence; finite affine refinements
   exist by lem-weil-pbc-etale-qcqs-cofinal-finite-coverings. Descend these objects,
   their maps and finite covering relations by lem-weil-pbc-etale-finite-data-descent.
   Sections are sections of F_i by the definition of direct image, giving local
   surjectivity. A representative mapping to zero becomes zero on a finite cover
   at a later stage, giving injectivity after sheafification.
2. Each F_i and its inverse images are killed by n. Apply
   lemma-weil-pbc-etale-cohomology-continuity to F_i: the higher cohomology of
   p_i^* F_i is the filtered colimit of stage cohomology, which vanishes above c
   by the uniform hypothesis.
3. Apply lem-weil-pbc-cohomology-filtered-colimit to the colimit in Step 1 to get
   the bound for F killed by n. For arbitrary torsion F, use
   lemma-weil-pbc-torsion-filtered-union to write F as the filtered colimit of F[n],
   and apply the same commutation of cohomology with filtered colimits again. -/
theorem hasTorsionEtaleCohomologicalDimensionLE_of_isLimit
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (s : Cone D) (hs : IsLimit s) (c : ℕ)
    (h : ∀ i : I, HasTorsionEtaleCohomologicalDimensionLE (D.obj i) c) :
    HasTorsionEtaleCohomologicalDimensionLE s.pt c := by
  sorry

end AlgebraicGeometry.Scheme
