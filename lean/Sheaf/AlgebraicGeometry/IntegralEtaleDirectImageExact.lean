/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.RightDerived

import WeilConjectures.SixFunctors.Finite.Exact
import Mathlib.CategoryTheory.Sites.EpiMono
import Sheaf.Paper.IntegralEtaleCoverDisjointRefinement
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleDisjointCover
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.CategoryTheory.Abelian.ExactFunctorHigherDerivedVanishing
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor

/-!
# Exactness of integral étale direct image

Source: Stacks Project, Étale Cohomology, Tag 04C2, parts (1) and (4), and Derived
Categories, Tag 015F (blueprint: sbc-lem-integral-etale-direct-image-exact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Integral direct image on abelian étale sheaves is exact, its positive right derived
functors vanish, and its canonical bounded-below derived comparison is invertible.
Source: Stacks Project, Tags 04C2 and 015F
(blueprint: sbc-lem-integral-etale-direct-image-exact).

Proof: Given an epimorphism of sheaves and a section of its direct image over an étale
object `V`, the local-surjectivity criterion gives a covering of `X ×_Y V` on which the
section lifts. At every point of `V`, the integral disjoint-refinement lemma supplies an
étale neighbourhood on which that covering refines to a disjoint open partition. Pull the
local lifts back to the pieces and glue using the disjoint-cover product formula, also
for the empty partition. Uniqueness of gluing shows that the glued section maps to the
original section. These neighbourhoods jointly cover `V`, so the local-surjectivity
criterion proves that direct image preserves epimorphisms. Direct image is already
additive and left exact; thus it is exact. Enough injectives and the exact-functor
higher-derived-vanishing lemma imply that every positive right derived functor is zero.
Finally, exact-functor derived factorization and preservation of bounded-below objects
identify the termwise functor with the right derived functor by its universal property:
the canonical comparison is invertible on every bounded-below complex. Passing to its
homotopy class gives the displayed comparison on `HomotopyCategory.Plus`. For finite
morphisms this specializes to `lemma-weil-pbc-finite-direct-image-exact`. -/
theorem integral_etale_direct_image_exact {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] :
    (PreservesFiniteLimits (lowerStar AddCommGrpCat.{u + 1} f) ∧
      PreservesFiniteColimits (lowerStar AddCommGrpCat.{u + 1} f)) ∧
    (∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ),
      IsZero (((lowerStar AddCommGrpCat.{u + 1} f).rightDerived (q + 1)).obj F)) ∧
    (∀ K : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      IsIso ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlusUnit.app K)) := by
  sorry

end AlgebraicGeometry.Etale
