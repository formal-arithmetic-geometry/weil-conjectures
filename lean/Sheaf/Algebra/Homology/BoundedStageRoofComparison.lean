/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.Algebra.Homology.SubcategoryLeftResolution
import Sheaf.CategoryTheory.RightFractionDenseSubcategory
import Sheaf.CategoryTheory.TruncationDescends

/-!
# Compatible cohomology comparisons for bounded stages

Source: Stacks Project, Derived Categories, Tag 0794,
`proposition-left-derived-exists`, bounded-stage roof argument before passage to colimits.
(blueprint: lem-trf-bounded-stage-roof-comparison).

The natural-number index `k` denotes the positive stage `k + 1` of the source statement.
-/

@[expose] public section

set_option autoImplicit false

universe uA vA uB vB wB

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace CategoryTheory.Functor

/-- An additive functor preserving quasi-isomorphisms between bounded-above complexes
in a quotient-generating additive class gives compatible derived isomorphisms between
any two supplied towers resolving the good truncations of quasi-isomorphic complexes.
The isomorphisms commute both with transitions and with the actual augmentations.
Here `k : ℕ` denotes stage `k + 1`; `X` and `Y` can be unbounded.

Source: Stacks Project, Derived Categories, Tag 0794,
`proposition-left-derived-exists`, paragraphs beginning "The problem is that" and
"The exact same argument". The arrow follows the displayed cohomology square.
(blueprint: lem-trf-bounded-stage-roof-comparison).

Proof:
1. In the homotopy category restrict the quasi-isomorphism right-fraction calculus
   (lem-pc-quasi-isomorphisms-multiplicative-system) to the full subcategory of objects
   with bounded-above cohomology. Ore sources and cancellation refinements stay there
   because their denominators are quasi-isomorphisms. Right-fraction representation
   (lem-pc-right-fraction-representation) and common refinements
   (lem-pc-right-fraction-common-refinement) give a fully faithful embedding of its
   localization in the ambient derived category (def-weil-abstract-derived-category).
   Choose all localizations in one larger universe, using HasDerivedCategory.standard.
2. Every object of this subcategory has a quasi-isomorphism from a bounded-above
   P-complex: first truncate above its cohomology bound
   (lem-weil-pbc-truncation-cohomology), then apply lem-sfb-subcategory-left-resolution.
   Thus lem-trf-right-fraction-dense-subcategory identifies its localization with the
   localization of bounded-above P-complexes and supplies right fractions there.
3. Homotopy preservation (lem-weil-pbc-homotopic-maps-equal-cohomology) makes termwise
   F followed by localization in D(B) a functor on these resolving complexes. By hF it
   inverts their quasi-isomorphisms. Descend it using
   lem-weil-pbc-localization-universal-property and the equivalence from step 2,
   retaining its natural comparison isomorphisms rho. This is the derived version
   of the node's functor H^i after F; applying cohomology recovers that functor.
4. Put n = k + 1. The maps c : truncLE n (E k) to E k and truncLE n (e k) are
   quasi-isomorphisms by the vanishing and augmentation hypotheses and
   lem-weil-pbc-truncation-cohomology. They identify E k with truncLE n X in the
   localization. Do the same for G k and Y. The truncated alpha is invertible by
   lem-weil-pbc-truncation-descends. Conjugation gives an isomorphism a_k from E k
   to G k whose composite with g k equals the composite of e k with alpha in the
   ambient derived category; this also applies when X and Y are unbounded.
5. Naturality of truncation inclusions, successive inclusions and truncated alpha
   (lem-weil-pbc-truncation-descends), together with he and hg, gives
   Q(u k) followed by a_(k+1) equal to a_k followed by Q(v k). Cancel only the
   invertible truncation inclusion for E k, never the inclusions into X or Y.
6. Apply the descended functor of step 3 to a_k and conjugate by rho to obtain Theta.
   Functoriality and rho-naturality turn step 5 into the transition equation below.
7. Represent a_k by a right roof E k <- V -> G k among bounded-above P-complexes
   (lem-pc-right-fraction-representation). Both legs are quasi-isomorphisms.
   The ambient augmentation equality admits a common quasi-isomorphism refinement
   (lem-pc-right-fraction-common-refinement). Resolve its source using step 2.
   This gives L with two quasi-isomorphisms to E k and G k, whose composites into Y
   are homotopic. Use hF only on these two composites between bounded-above P-complexes.
8. Applying F preserves this homotopy, so the composites agree after localization
   in D(B) (lem-weil-pbc-homotopic-maps-equal-cohomology and
   def-weil-abstract-derived-category). The roof formula for Theta and cancellation
   of the localized F-image of the quasi-isomorphism from L to E k give exactly the
   augmentation equation below. Applying cohomology gives the node's two equations.
   No colimits occur.
-/
theorem bounded_stage_roof_comparison
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (P : A → Prop) (hzero : P (0 : A))
    (hiso : ∀ (M N : A), (M ≅ N) → P M → P N)
    (hsum : ∀ (M N : A), P M → P N → P (M ⊞ N))
    (hcover : ∀ M : A, ∃ (N : A) (p : N ⟶ M), P N ∧ Epi p)
    (F : A ⥤ B) [F.Additive]
    (hF : ∀ (K L : CochainComplex A ℤ) (f : K ⟶ L),
      (∃ b : ℤ, ∀ j : ℤ, b < j → IsZero (K.X j)) →
      (∀ j : ℤ, P (K.X j)) →
      (∃ b : ℤ, ∀ j : ℤ, b < j → IsZero (L.X j)) →
      (∀ j : ℤ, P (L.X j)) → QuasiIso f →
      QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f))
    (E G : ℕ → CochainComplex A ℤ)
    (hEbound : ∀ k : ℕ, ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero ((E k).X j))
    (hGbound : ∀ k : ℕ, ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero ((G k).X j))
    (hEterms : ∀ (k : ℕ) (j : ℤ), P ((E k).X j))
    (hGterms : ∀ (k : ℕ) (j : ℤ), P ((G k).X j))
    (u : ∀ k : ℕ, E k ⟶ E (k + 1)) (v : ∀ k : ℕ, G k ⟶ G (k + 1))
    (X Y : CochainComplex A ℤ) (e : ∀ k : ℕ, E k ⟶ X) (g : ∀ k : ℕ, G k ⟶ Y)
    (he : ∀ k : ℕ, u k ≫ e (k + 1) = e k)
    (hg : ∀ k : ℕ, v k ≫ g (k + 1) = g k)
    (hEvanish : ∀ (k : ℕ) (j : ℤ), (k : ℤ) + 1 < j → IsZero ((E k).homology j))
    (hGvanish : ∀ (k : ℕ) (j : ℤ), (k : ℤ) + 1 < j → IsZero ((G k).homology j))
    (heiso : ∀ (k : ℕ) (j : ℤ), j ≤ (k : ℤ) + 1 →
      IsIso (HomologicalComplex.homologyMap (e k) j))
    (hgiso : ∀ (k : ℕ) (j : ℤ), j ≤ (k : ℤ) + 1 →
      IsIso (HomologicalComplex.homologyMap (g k) j))
    (α : X ⟶ Y) (hα : QuasiIso α) :
    ∃ Θ : ∀ k : ℕ,
        DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (E k)) ≅
          DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (G k)),
      (∀ k : ℕ,
        DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (u k)) ≫
            (Θ (k + 1)).hom =
          (Θ k).hom ≫
            DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (v k))) ∧
      (∀ k : ℕ,
        (Θ k).hom ≫
            DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (g k)) =
          DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (e k)) ≫
            DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map α)) := by
  sorry

/-- The cohomology form of `bounded_stage_roof_comparison`, retaining its transition
and augmentation equations simultaneously for every integer degree.

Source: Stacks Project, Derived Categories, Tag 0794,
`proposition-left-derived-exists`, the displayed cohomology square and compatibility
as the stage varies. (blueprint: lem-trf-bounded-stage-roof-comparison).

Proof: choose the standard derived category of B and apply the main derived comparison.
Apply `DerivedCategory.homologyFunctor B i` to its isomorphisms and both equations.
Conjugate by `DerivedCategory.homologyFunctorFactors B i` to identify these objects
and maps with the actual homology objects and homology maps of the termwise F-complexes.
Naturality of that comparison isomorphism gives the displayed equations. This works
for all k and i, with the same derived comparison family; no restriction on i is used.
-/
theorem bounded_stage_roof_comparison_homology
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (P : A → Prop) (hzero : P (0 : A))
    (hiso : ∀ (M N : A), (M ≅ N) → P M → P N)
    (hsum : ∀ (M N : A), P M → P N → P (M ⊞ N))
    (hcover : ∀ M : A, ∃ (N : A) (p : N ⟶ M), P N ∧ Epi p)
    (F : A ⥤ B) [F.Additive]
    (hF : ∀ (K L : CochainComplex A ℤ) (f : K ⟶ L),
      (∃ b : ℤ, ∀ j : ℤ, b < j → IsZero (K.X j)) →
      (∀ j : ℤ, P (K.X j)) →
      (∃ b : ℤ, ∀ j : ℤ, b < j → IsZero (L.X j)) →
      (∀ j : ℤ, P (L.X j)) → QuasiIso f →
      QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f))
    (E G : ℕ → CochainComplex A ℤ)
    (hEbound : ∀ k : ℕ, ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero ((E k).X j))
    (hGbound : ∀ k : ℕ, ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero ((G k).X j))
    (hEterms : ∀ (k : ℕ) (j : ℤ), P ((E k).X j))
    (hGterms : ∀ (k : ℕ) (j : ℤ), P ((G k).X j))
    (u : ∀ k : ℕ, E k ⟶ E (k + 1)) (v : ∀ k : ℕ, G k ⟶ G (k + 1))
    (X Y : CochainComplex A ℤ) (e : ∀ k : ℕ, E k ⟶ X) (g : ∀ k : ℕ, G k ⟶ Y)
    (he : ∀ k : ℕ, u k ≫ e (k + 1) = e k)
    (hg : ∀ k : ℕ, v k ≫ g (k + 1) = g k)
    (hEvanish : ∀ (k : ℕ) (j : ℤ), (k : ℤ) + 1 < j → IsZero ((E k).homology j))
    (hGvanish : ∀ (k : ℕ) (j : ℤ), (k : ℤ) + 1 < j → IsZero ((G k).homology j))
    (heiso : ∀ (k : ℕ) (j : ℤ), j ≤ (k : ℤ) + 1 →
      IsIso (HomologicalComplex.homologyMap (e k) j))
    (hgiso : ∀ (k : ℕ) (j : ℤ), j ≤ (k : ℤ) + 1 →
      IsIso (HomologicalComplex.homologyMap (g k) j))
    (α : X ⟶ Y) (hα : QuasiIso α) :
    ∃ θ : ∀ (k : ℕ) (i : ℤ),
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (E k)).homology i ≅
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (G k)).homology i,
      (∀ (k : ℕ) (i : ℤ),
        HomologicalComplex.homologyMap
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (u k)) i ≫
            (θ (k + 1) i).hom =
          (θ k i).hom ≫ HomologicalComplex.homologyMap
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (v k)) i) ∧
      (∀ (k : ℕ) (i : ℤ),
        (θ k i).hom ≫ HomologicalComplex.homologyMap
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (g k)) i =
          HomologicalComplex.homologyMap
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (e k)) i ≫
            HomologicalComplex.homologyMap
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map α) i) := by
  sorry

end CategoryTheory.Functor
