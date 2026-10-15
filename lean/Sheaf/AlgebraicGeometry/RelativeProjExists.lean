/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.RelativeProjData
import Mathlib.AlgebraicGeometry.Gluing
import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic

/-! # Existence and affine compatibility of relative Proj

Source: blueprint, Nagata compactification, sketch data, order 13;
Stacks Project, Constructions, Tags 01LH, 01NO, 01NP, 01NQ
(blueprint: lemma-nagata-relative-proj-exists).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Relative Proj exists with all its affine restriction identifications, and is unique
up to the unique isomorphism respecting those identifications and the structural maps.
The fields of `RelativeProjData` give the restriction isomorphisms, their compatibility
with the canonical section-restriction maps, and their compatibility over the base.
The comparison ranges over any scheme with such compatible affine identifications,
including a realization obtained by gluing a different affine cover.

Source: blueprint, Nagata compactification, sketch data, order 13; Stacks Project,
Constructions, Tags 01LH and 01NQ (blueprint: lemma-nagata-relative-proj-exists).

Proof: (1) For every affine open U use Proj of the graded section ring. The canonical
restriction morphisms identify the model on V with the inverse image of V in the
model on U, by `lem-nagata-proj-affine-restriction` (Tags 01NO and 01NP).
(2) Its identity and composition laws give an equifibered diagram on all affine opens.
Apply `lem-weil-pbc-relative-glueing-affine-opens` to obtain the scheme and structural
map, with all affine restriction isomorphisms and their compatibility equations.
(3) The transition composition law gives iterated affine restriction compatibility.
For arbitrary open restrictions, check equality on affine refinements using
`lem-weil-pbc-affine-opens-basis` and `lem-weil-pbc-scheme-morphism-gluing`.
(4) Given another realization P, on each affine inverse image compare the two charts
via the common local Proj model. On an overlap these comparisons agree on all affine
refinements, by the transition equations. The affine basis and morphism gluing yield
a unique global comparison over X. Reverse the local comparisons to construct its
inverse; both composites are identities by the uniqueness part of morphism gluing.
Any chart-preserving comparison has the same local maps and hence is this one.
(5) A realization from any chosen affine cover has the same identifications after
passing to common affine refinements. Glue the comparisons there as in (4).
Comparisons for three covers agree on common affine refinements, hence globally;
restricting gives compatibility with further restriction. No overlap is assumed affine. -/
theorem exists_relativeProjData {X : Scheme.{u}} (A : RelativeProjAlgebra X) :
    ∃ D : RelativeProjData A,
      ∀ (P : Scheme.{u}) (π : P ⟶ X)
        (i : ∀ V : X.affineOpens, (π ⁻¹ᵁ V.1).toScheme ≅ A.localProj V),
        (∀ V : X.affineOpens,
          (i V).hom ≫ A.localBase V ≫ V.1.ι = (π ⁻¹ᵁ V.1).ι ≫ π) →
        (∀ (V W : X.affineOpens) (h : W ≤ V),
          (i W).inv ≫ P.homOfLE (π.preimage_mono h) ≫ (i V).hom =
            A.localTransition h) →
        ∃! e : D.proj ≅ P,
          e.hom ≫ π = D.π ∧
            ∀ V : X.affineOpens,
              (D.restrictionIso V).inv ≫ (D.π ⁻¹ᵁ V.1).ι ≫ e.hom =
                (i V).inv ≫ (π ⁻¹ᵁ V.1).ι := by
  sorry

end AlgebraicGeometry
