/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.CategoryTheory.Sites.GrothendieckTopos
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.Sites.SliceSubtoposSitePresentation

/-!
# Base change between slice sites realizes localization

Source: Stacks Project, Sites, Tag 09W9, lemma-relocalize-given-fibre-products,
clauses (1)-(3), using Tag 03CE (blueprint: lem-trf-slice-site-base-change-localization).

`Over.pullback f` is the base-change functor and `Over.map f` is localization.
The final natural isomorphism is the direct-image formula, simultaneously natural
in the sheaf and the slice object. The localization direct image is the existing
right Kan extension, rather than an unspecified right adjoint.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Base change is continuous for the actual localized covering families and
realizes the localization morphism of topoi. The first two clauses are the two
conditions of Stacks continuity (00WV); the third records continuity on sheaves.
The geometric morphism has restriction along `Over.map f` as its inverse image
and the cocontinuous direct image of that functor as its direct image. Its inverse
image is naturally isomorphic to the continuous pullback along `Over.pullback f`,
which is exact. The last functor isomorphism says that the direct image evaluated
at `T → W` is `F(T ×_W V → V)`, including all restriction maps and maps of sheaves.

Source: Stacks Project, Sites, Tag 09W9, clauses (1)-(3), and Tag 03CE
(blueprint: lem-trf-slice-site-base-change-localization).

Proof:
1. Fibre-product universal properties define the existing `Over.pullback f` on
   arrows. Localized covers are underlying covers, so their pullbacks cover by
   the site base-change axiom. The comparison between iterated fibre products is
   an isomorphism, giving the second continuity condition
   [def-weil-pbc-sites-and-cohomology, def-pur-localized-ringed-site].
2. The slice `C/W` has terminal object `W/W` and pullbacks, hence finite limits.
   Apply [lem-trf-slice-subtopos-site-presentation] there at `V/W`, and identify
   its iterated slice with `C/V` by relocalization. The restriction functor is
   precisely `overMapPullback`, and its right adjoint is precomposition with
   `Over.pullback f`. Uniqueness of adjoints identifies these with the existing
   continuous pullback and cocontinuous direct image. Restriction is left exact
   and preserves colimits as a left adjoint, giving the morphism of sites and
   the same geometric morphism [def-trf-geometric-morphism].
3. The product formula in that localization theorem becomes the displayed
   fibre-product formula. Its restriction maps and maps of sheaves are computed
   componentwise, so it is natural in both variables. -/
theorem sliceSiteBaseChangeLocalization
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    (K : Precoverage C) (hK : K.IsSiteForCoverings) {V W : C} (f : V ⟶ W) :
    (∀ (T : Over W) (R : Presieve T), Presieve.overEquiv T R ∈ K T.left →
      Presieve.overEquiv ((Over.pullback f).obj T) (R.map (Over.pullback f)) ∈
        K ((Over.pullback f).obj T).left) ∧
    (∀ (T S A : Over W) (R : Presieve T), Presieve.overEquiv T R ∈ K T.left →
      ∀ (a : S ⟶ T) (b : A ⟶ T), R a →
        PreservesLimit (cospan a b) (Over.pullback f)) ∧
    (Over.pullback f).IsContinuous (K.toGrothendieck.over W) (K.toGrothendieck.over V) ∧
    ∃ g : GeometricMorphism
        (Sheaf (K.toGrothendieck.over V) (Type (max u v w)))
        (Sheaf (K.toGrothendieck.over W) (Type (max u v w))),
      g.inverse = K.toGrothendieck.overMapPullback (Type (max u v w)) f ∧
      g.direct = (Over.map f).sheafPushforwardCocontinuous (Type (max u v w))
        (K.toGrothendieck.over V) (K.toGrothendieck.over W) ∧
      Nonempty ((Over.pullback f).sheafPullback (Type (max u v w))
        (K.toGrothendieck.over W) (K.toGrothendieck.over V) ≅ g.inverse) ∧
      PreservesFiniteLimits ((Over.pullback f).sheafPullback (Type (max u v w))
        (K.toGrothendieck.over W) (K.toGrothendieck.over V)) ∧
      PreservesFiniteColimits ((Over.pullback f).sheafPullback (Type (max u v w))
        (K.toGrothendieck.over W) (K.toGrothendieck.over V)) ∧
      Nonempty (g.direct ⋙ sheafToPresheaf (K.toGrothendieck.over W) (Type (max u v w)) ≅
        sheafToPresheaf (K.toGrothendieck.over V) (Type (max u v w)) ⋙
          (Functor.whiskeringLeft (Over W)ᵒᵖ (Over V)ᵒᵖ (Type (max u v w))).obj
            (Over.pullback f).op) := by
  sorry

end CategoryTheory
