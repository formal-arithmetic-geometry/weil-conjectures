/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits

import Sheaf.Paper.FinitarySiteEnoughPoints
import Sheaf.CategoryTheory.ContinuousCocontinuousToposAdjunctionForCoverings
import WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Enough points from a cover by finitary slices

Source: Stacks Project, Sites, Lemma 0DW0, `lemma-criterion-points`, in Section 00YN
(blueprint: lem-sfb-site-finitary-slice-enough-points).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A cover of the terminal sheaf by sheafified representables whose slices have finite
limits and finite covering refinements gives a conservative set of points.
Source: Stacks Project, Sites, Lemma 0DW0, `lemma-criterion-points`, Section 00YN
(blueprint: lem-sfb-site-finitary-slice-enough-points).

The localized covering families are exactly `J.comap (Over.forget (U i))`: membership
means that the underlying family covers in `C`, and its generated topology is
`J.toGrothendieck.over (U i)` (def-pur-localized-ringed-site). The representables
are explicitly sheafified; subcanonicity is not assumed. The value and point-index
universe `max u v w` contains both site universes (def-weil-size-convention).
Every covering presieve has a presentation indexed in `Type (max u v)`, so the
finite-refinement condition covers arbitrary presentations, including repetitions.

Proof, following the node and Stacks 0DW0:
1. Apply lem-trf-finitary-site-enough-points (00YQ) to each localized site, after
   the small-category size transport if needed. Its finite-limit and finite-refinement
   hypotheses are exactly `hlimits` and `hfinite`. The forgetful functor is continuous:
   it sends coverings to coverings and preserves pullbacks of covering arrows, by
   the site axioms (def-weil-pbc-sites-and-cohomology). It is cocontinuous because
   any covering of its image lifts, by composing its arrows with the structure map
   to `U i` (def-weil-pbc-special-cocontinuous-functor). Thus restriction is the
   inverse image of a geometric morphism, by
   lem-weil-pbc-continuous-cocontinuous-topos-adjunction. Compose this morphism
   with each slice point using def-trf-geometric-morphism, as in Stacks 05V1.
2. If a sheaf morphism is inverted by all these points, slice conservativity makes
   every restriction invertible. Its component at every object mapping to some
   `U i` is therefore bijective (def-pur-localized-ringed-site).
3. By the sheafification adjunction (def-weil-pbc-sheafification), the coproduct
   in `hcover` is the sheafification of the presheaf coproduct of representables.
   The epi-local-surjectivity lemma
   lem-weil-pbc-site-sheaf-sets-epi-locally-surjective and local representability
   lem-weil-pbc-site-sheafification-sections-local give, for each `W`, a cover by
   objects mapping to some `U i`. Compose the two local covers by the site axioms.
   On that cover the component maps are bijective by step 2. Injectivity descends
   by separatedness. For surjectivity, lift a section on each covering object;
   injectivity on overlaps makes the lifts compatible, and the sheaf condition
   glues them uniquely. Thus all components are bijective and the morphism is iso.
4. Index the composite points by the disjoint union of the slice index sets,
   a set in the fixed universe. Steps 1--3 give joint reflection of isomorphisms.
   If the covering family is empty, every object has an empty cover, all sheaves
   are terminal, and the empty family of points is already conservative. -/
theorem finitarySlice_enoughPoints
    {C : Type u} [Category.{v} C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (I : Type (max u v w)) (U : I → C)
    (hcover : Epi (terminal.from
      (∐ fun i : I => (presheafToSheaf J.toGrothendieck (Type (max u v w))).obj
        (uliftYoneda.{max u w}.obj (U i)))))
    (hlimits : ∀ i : I, HasFiniteLimits (Over (U i)))
    (hfinite : ∀ (i : I) (X : Over (U i)) (A : Type (max u v))
      (V : A → Over (U i)) (f : ∀ a, V a ⟶ X),
      Presieve.ofArrows V f ∈ (J.comap (Over.forget (U i))) X →
        ∃ (K : Type (max u v)) (_ : Finite K) (W : K → Over (U i))
          (g : ∀ k, W k ⟶ X) (r : K → A),
          Presieve.ofArrows W g ∈ (J.comap (Over.forget (U i))) X ∧
            ∀ k, ∃ (q : W k ⟶ V (r k)), q ≫ f (r k) = g k) :
    ∃ (ι : Type (max u v w))
      (p : ι → GeometricMorphism (Type (max u v w))
        (Sheaf J.toGrothendieck (Type (max u v w)))),
      ∀ {F G : Sheaf J.toGrothendieck (Type (max u v w))} (a : F ⟶ G),
        (∀ j, Function.Bijective ((p j).inverse.map a)) → IsIso a := by
  sorry

end CategoryTheory
