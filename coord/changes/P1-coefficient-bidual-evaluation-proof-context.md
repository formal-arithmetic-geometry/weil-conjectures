# CategoryTheory.coefficientBidualEvaluation_shift_one

## Reason

Complete the coefficient-specific representative and signed shift proof. The delivery
adds proved private helpers, opens monoidal notation for their tensor calculations,
and adjusts local reducibility attributes to avoid unfolding the fixed resolution
and component constructions during elaboration. The public theorem, its visibility,
its public import and every definition appearing in its statement are unchanged.
The initial preflight required this record for the changed module-level commands.
No source-library module or declaration is edited.

## Old

```lean
theorem coefficientBidualEvaluation_shift_one
    (M : RingedSiteDualityModel.{c, v, r, w} J R) (X : D.{c, v, r, w} J R) :
    let O := ringedSiteDualityUnit.{c, v, r, w} J R
    let H := derivedInternalHomOfUniverses.{c, v, r, w} J R
    let T := Prod.sectL _ O ⋙ H
    ringedSiteBidual M.closed M.symmetric O (X⟦(1 : ℤ)⟧) ≫
        (-(H.map (Prod.mkHom ((sourceShift.{c, v, r, w} J R X 1).hom.app O).op
          (𝟙 O)) ≫ (sourceShift.{c, v, r, w} J R (T.obj (op X)) (-1)).inv.app O)) =
      (ringedSiteBidual M.closed M.symmetric O X)⟦(1 : ℤ)⟧' := by
  sorry
```

The original proof context opens `CategoryTheory`, `CategoryTheory.Limits`,
`Opposite`, and `CategoryTheory.RingedHomUniverses`, and marks
`CategoryTheory.homComplexFunctor` locally irreducible.

## New

```lean
theorem coefficientBidualEvaluation_shift_one
    (M : RingedSiteDualityModel.{c, v, r, w} J R) (X : D.{c, v, r, w} J R) :
    let O := ringedSiteDualityUnit.{c, v, r, w} J R
    let H := derivedInternalHomOfUniverses.{c, v, r, w} J R
    let T := Prod.sectL _ O ⋙ H
    ringedSiteBidual M.closed M.symmetric O (X⟦(1 : ℤ)⟧) ≫
        (-(H.map (Prod.mkHom ((sourceShift.{c, v, r, w} J R X 1).hom.app O).op
          (𝟙 O)) ≫ (sourceShift.{c, v, r, w} J R (T.obj (op X)) (-1)).inv.app O)) =
      (ringedSiteBidual M.closed M.symmetric O X)⟦(1 : ℤ)⟧' := by
  -- Complete proof from signed ordinary evaluation, normalized representative
  -- uncurrying, source-shift uniqueness, naturality and localization.
  -- The full checked body is in the delivered Lean module.
```

The exact additional proof-context commands are:

```lean
import all Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses

open CategoryTheory.MonoidalCategory
attribute [local irreducible] WeilConjectures.coefficientHomResolution
  CategoryTheory.ringedSiteDualityUnitComplex CategoryTheory.ringedSiteBidualDegree
  CategoryTheory.ringedSiteBidualComponent
```

The existing public shift import and all definitions used in the theorem's statement
remain verbatim. The added import exposes private normalization/descent helpers only.
Monoidal notation is additionally opened. The fixed resolution functor, coefficient
unit complex and ordinary bidual component constructions receive local irreducibility
attributes. These settings guide proof elaboration and do not change
mathematical data or exported declarations. All new helpers are private and proved.
No new unfinished statement is introduced.

The private `unsignedReindex_proj` equation is now written using
`SignedDoubleHomCone.Complex` and `SignedDoubleHomCone.proj`, with the explicit
product-limit family. These are the same complexes and projections as the former
`RingedSiteComplex` and `homComplexπ`. Its sole private caller immediately rewrites
the projection abbreviation back to `homComplexπ`. This presentation avoids expensive
conversion of the concrete product universal property while checking the proof;
it changes no mathematical equation or public signature.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.CoefficientBidualEvaluationShiftOne | P1 | Complete its proof; adjust private proof context only. |
| Sheaf.CategoryTheory.CoefficientBidualTriangleCompatibility | unclaimed | Direct importer; unchanged public statement and public imports require no adaptation. |

No other module directly imports the item. Its consumers see the same public interface;
no target or dependent definition requires statement review.

## Status

landed 20261021T021921-L-2792824 2026-10-21 (merge of deliver/P1/Sheaf.CategoryTheory.CoefficientBidualEvaluationShiftOne)
