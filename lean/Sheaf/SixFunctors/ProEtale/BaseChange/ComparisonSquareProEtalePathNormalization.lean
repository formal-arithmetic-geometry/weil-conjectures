/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquarePaths

/-! # Normalization of the pro-etale comparison-square path under exact derivation

Source: blueprint comparison-square transport, expanded proof step 4.
(blueprint: stage3-proetale-comparison-square-proetale-path-normalization)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Exact derivation of the ordinary ProEtale path, with the common source and target
composition factors. This identity concerns one path and assumes no square coherence.
The heterogeneous equality retains the two endpoint presentations; these endpoints
are definitionally equal. It avoids unfolding the derived functor constructions
when joining the two normalization identities.
Source: blueprint `stage3-proetale-comparison-square`, proof step 4; Stacks, Tag 0B65.
(blueprint: stage3-proetale-comparison-square-proetale-path-normalization)

Proof: write C(F,G) for mapDerivedCategoryCompIso F G and J(f) for
leftDerivedUpperStarIsoMapDerivedCategory at f. Expand the ordinary path as the
comparison at f' whiskered by g_et, the comparison at g whiskered by f'_proet, and
the pro-etale square whiskered by nu_Y. Apply mapDerivedCategoryNatIso_trans and its
left/right whiskering equations. The associativity equation for C collects the
source factors into comparisonSquareSourceIso and the target factors into the exact
part of comparisonSquareTargetIso; all intermediate C-inverse pairs cancel. This
leaves the two exact derived edge comparisons followed by the derived ordinary
pro-etale square.

Expand leftDerivedUpperStarComparisonIso at f' and g. Its ordinary comparison is
definitionally comparisonCoefficientPullbackIso, and its final factor is J.inv.
Naturality of J(f').inv moves the factor for f' past the exact derived comparison
at g. Thus the first two displayed arrows give the same exact derived edge path,
followed by the two inverse J factors for g and f'. Expand
leftDerivedUpperStarSquareIso into its inverse composition comparison, equality
transport, and forward composition comparison. In leftDerivedFunctorNatIso and
leftDerivedFunctorCompIso the J factor for a composite cancels with its inverse.
The remaining composition factors are C conjugated by the individual J factors.
Equality induction for leftDerivedUpperStarCongr identifies the middle transport
with the derived transport in proEtaleComparisonSquare. Cancel the J factors for
g and f' against those from the edge path. The surviving inverse J factors for
f and g' are exactly the final factors of comparisonSquareTargetIso. Evaluate at
M.obj and associate the composites. Restriction to D+ only contributes the identity
mapDerivedCategoryPlusCompatibility on the source edges; no etale square identity
or coherence hypothesis is used. Identity edges and zero input obey the same
naturality and cancellation equations. -/
theorem comparisonSquareProEtalePath_normalization
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    HEq
      (comparisonSquareDerivedPath Λ g' f' f g (comparisonSquareProEtalePath Λ
        { toCommSq := sq.toCommSq, isoPullback := sq.isoPullback,
          hom_fst := sq.isoPullback_hom_fst, hom_snd := sq.isoPullback_hom_snd }) M)
      ((leftDerivedUpperStarComparisonIso f' Λ).hom.app
            (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj M) ≫
          L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f').map
            ((leftDerivedUpperStarComparisonIso g Λ).hom.app M) ≫
          (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app
            ((DerivedCategory.Plus.ι ⋙ D(ν^*(Y)[ModuleCat.{u + 1} Λ])).obj M)) := by
  sorry

end AlgebraicGeometry.ProEtale
