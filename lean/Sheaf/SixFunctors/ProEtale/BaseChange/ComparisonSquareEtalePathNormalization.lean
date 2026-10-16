/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquarePaths

/-! # Normalization of the etale comparison-square path under exact derivation

Source: blueprint comparison-square transport, expanded proof step 4.
(blueprint: stage3-proetale-comparison-square-etale-path-normalization)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Exact derivation of the ordinary Etale path, with the common source and target
composition factors. This identity concerns one path and assumes no square coherence.
The heterogeneous equality retains the two endpoint presentations; these endpoints
are definitionally equal. It avoids unfolding the derived functor constructions
when joining the two normalization identities.
Source: blueprint `stage3-proetale-comparison-square`, proof step 4; Stacks, Tag 0B65.
(blueprint: stage3-proetale-comparison-square-etale-path-normalization)

Proof: write C(F,G) for mapDerivedCategoryCompIso F G and J(f) for
leftDerivedUpperStarIsoMapDerivedCategory at f. First expand the ordinary path as
(se whiskered by nu_X') followed by the comparisons at g' and f. Derivation preserves
this composite by mapDerivedCategoryNatIso_trans. Apply
mapDerivedCategoryNatIso_isoWhiskerRight to its first and last factors and
mapDerivedCategoryNatIso_isoWhiskerLeft to its middle factor. The equation
mapDerivedCategoryCompIso_assoc collects the outer C factors into
comparisonSquareSourceIso and the exact-composition part of comparisonSquareTargetIso;
the intermediate C factors cancel with their inverses. The remaining three maps are
D(nu_X') applied to the derived etale square, the derived edge comparison at g', and
D(g'_proet) applied to the derived edge comparison at f.

For the first map, expand se using etaleComparisonSquare and the derived square using
Etale.pullbackSquareComparison and Etale.upperStarPlusComp. The ordinary composition
comparison is Etale.upperStarComp. The equations
Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app and
Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app identify the composition factors;
equality induction on the square's commutativity identifies the middle transports.
For the other maps, comparisonCoefficientPullbackIso is definitionally the inverse of
comparisonUpperStarCompUpperStarIso. Expanding leftDerivedUpperStarComparisonIso gives
exactly its derived image conjugated by C and followed by J(f).inv. Naturality of
J(g').inv moves it past the derived f-comparison, producing L(g') of that comparison.
The two remaining inverse J factors are precisely the final target factor. Evaluate
at M and use associativity and inverse-hom cancellation. No pro-etale square identity
or underived coherence equation is used; identity edges and the zero input satisfy
the same equations. -/
theorem comparisonSquareEtalePath_normalization
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    HEq
      (comparisonSquareDerivedPath Λ g' f' f g (comparisonSquareEtalePath Λ
        { toCommSq := sq.toCommSq, isoPullback := sq.isoPullback,
          hom_fst := sq.isoPullback_hom_fst, hom_snd := sq.isoPullback_hom_snd }) M)
      ((DerivedCategory.Plus.ι ⋙ D(ν^*(X')[ModuleCat.{u + 1} Λ])).map
            ((Etale.pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app M) ≫
          (leftDerivedUpperStarComparisonIso g' Λ).hom.app
            (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj M) ≫
          L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g').map
            ((leftDerivedUpperStarComparisonIso f Λ).hom.app M)) := by
  sorry

end AlgebraicGeometry.ProEtale
