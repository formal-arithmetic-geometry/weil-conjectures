# CategoryTheory.CoefficientBidual.compatibility proof scopes

## Reason

The new private proof helpers use opposite-category and composite functor shift instances.
Their component equations require local semireducible elaboration, as in the surrounding
existing scalar proof. Scope the settings to the new private lemmas and the ambient theorem.
No public signature, attribute, definition body or public import changes.

## Old

```lean
theorem compatibility (M : RingedSiteDualityModel.{c, v, r, w} J R) :
    ∃ S : (bidual.{c, v, r, w} J R).CommShift ℤ,
      (∀ X : D.{c, v, r, w} J R,
        (@Functor.commShiftIso _ _ _ _ (bidual.{c, v, r, w} J R) ℤ _ _ _ S 1).hom.app X =
          signedShift.{c, v, r, w} J R X) ∧
      (fun [_shiftInst : (bidual.{c, v, r, w} J R).CommShift ℤ] ↦
        TriangleCompatibility (bidual.{c, v, r, w} J R) (evaluation.{c, v, r, w} J R M))
        (_shiftInst := S)
```

## New

The signature above is verbatim unchanged. Its proof, and the three new proved private
helpers, locally use:

```lean
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
```

The opposite-category scope is opened locally only for `signed_bidual_exact`.
All new imports are proof-only. No private helper occurs in a public signature or definition.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.CoefficientBidualTriangleCompatibility | Q7 | Proof completion from separate source lemmas; public interface unchanged. |

`tools/downstream.py` reports zero downstream modules and only this module uses the ambient
compatibility declaration. DAG parents remain and prevent withdrawal. No forced adaptation.

## Status

landed 20261021T011030-L-2030374 2026-10-21 (merge of deliver/Q7/Sheaf.CategoryTheory.CoefficientBidualTriangleCompatibility)
