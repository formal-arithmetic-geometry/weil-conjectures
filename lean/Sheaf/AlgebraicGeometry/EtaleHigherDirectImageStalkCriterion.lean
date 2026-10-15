/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Sheaf.AlgebraicGeometry.StrictHenselization
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Vanishing of higher direct images at geometric points

Source: blueprint, `sec-smooth-purity/sk-prop-sf-kunneth-ordinary`,
lemma `lem-kun-cd-stalk-criterion` (blueprint: lem-kun-cd-stalk-criterion).
The restricted cohomology presheaf is expressed by derived Hom from the pullback
of the free abelian sheaf on an etale representable, as in Stacks Tag 03Q8.
`Point.presheafFiber` takes its colimit over opposite pointed etale neighbourhoods.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- For a quasi-compact quasi-separated morphism and a torsion abelian etale sheaf,
a higher direct image vanishes exactly when all pointed-neighbourhood cohomology
colimits vanish. Source: blueprint, `sec-smooth-purity/sk-prop-sf-kunneth-ordinary`,
lemma `lem-kun-cd-stalk-criterion` (blueprint: lem-kun-cd-stalk-criterion).

Proof:
1. Stacks Tag 03Q8 (`sbc-lem-higher-direct-image-presheaf`) identifies the higher
   direct image with the sheafification of the displayed presheaf. Its value at W
   is Hom(f* Z[W][0], F[q]) = H^q(W x_Y X, F restricted to W x_Y X).
2. Stacks Tag 03PT (`lem-weil-pbc-sheafification-geometric-stalk`) identifies the
   presheaf fiber with the sheaf fiber of its sheafification. By
   `def-weil-pbc-geometric-stalks`, this is the colimit over opposite pointed
   etale neighbourhoods, and hence the geometric stalk of the higher direct image.
3. Apply `lemma-weil-pbc-geometric-stalk-conservative` to the map from the zero
   sheaf to the higher direct image. Its stalk maps are isomorphisms exactly when
   the target stalks vanish, since the fiber functors preserve zero objects.
   The map itself is an isomorphism exactly when its target is a zero object. -/
theorem isZero_higherDirectImage_iff_geometric_cohomology_colimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (q : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsTorsion) :
    IsZero ((DerivedCategory.Plus.homologyFunctor
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y),
        IsZero ((Y.pointSmallEtale y).presheafFiber.obj
          ((uliftYoneda.{u + 1} ⋙
            (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
            presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
            upperStar AddCommGrpCat.{u + 1} f ⋙
            DerivedCategory.Plus.singleFunctor _ 0).op ⋙
              preadditiveYoneda.obj
                (((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧))) := by
  sorry

end AlgebraicGeometry.Etale
