/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q146
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import WeilConjectures.AlgebraicGeometry.AmpleTwistGlobalGeneration

/-!
# Projective-bundle projectivity over a base admitting an ample invertible module

Source: Stacks Project, Morphisms, Lemma 087S, clause (1)
(`lemma-projective-over-quasi-projective-is-H-projective`)
(blueprint: lem-trf-projective-bundle-to-h-projective).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A projective morphism in the projective-bundle sense over a scheme admitting an
absolutely ample invertible module is H-projective.

Source: Stacks Project, Morphisms, Lemma 087S, clause (1)
(blueprint: lem-trf-projective-bundle-to-h-projective).

Proof plan:
1. Unpack `IsProjectiveBundle` (def-trf-projective-bundle-morphism) to obtain a finite
   type quasi-coherent module E on S and a closed immersion i from V into P(E) over S.
   Choose an ample invertible module L from the hypothesis. Apply
   `exists_finite_generatingSections_tensorPow_of_isAmple`
   (lem-weil-pbc-coherent-twist-global-generation) to E and L. Choose a natural number
   d at least its integer bound, so E tensor L^d has finitely many generating sections.
2. The canonical relative-Proj twisting isomorphism
   (lem-trf-relative-proj-invertible-twist, Stacks 02NC) identifies P(E) with
   P(E tensor L^d) over S.
3. The globally generated projective-bundle lemma
   (lem-trf-projective-bundle-global-generated-h-projective, Stacks 087S) makes the
   latter structure morphism H-projective. Transport its closed immersion into finite
   projective space along the twisting isomorphism to make P(E) to S H-projective.
4. A closed immersion is H-projective by embedding into relative projective space of
   dimension zero (def-kun-projective). Apply `IsHProjective.comp`
   (lem-trf-h-projective-composition, Stacks 01WE) to i and P(E) to S, and use the
   factorization equality from step 1 to obtain H-projectivity of g. -/
theorem isHProjective_of_isProjectiveBundle {V S : Scheme.{u}} (g : V ⟶ S)
    (hg : IsProjectiveBundle g)
    (hS : ∃ (L : S.Modules) (hL : L.IsInvertible), @Scheme.Modules.IsAmple S L hL) :
    IsHProjective g := by
  sorry

end AlgebraicGeometry
