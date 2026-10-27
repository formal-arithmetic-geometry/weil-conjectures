# AlgebraicGeometry.Scheme.PurityIntegralTower.strictTateTensorTower_evaluation

## Reason

The universal equation was false for arbitrary level identifications `q`.
Postcomposing one `q n` with a nonidentity automorphism changes its inverse in the
left side, while `M`, its evaluation, `h`, and the right side stay fixed. At `d = 0`
over a nonempty scheme and an odd prime, multiplication by `-1` on the quotient
unit gives this discrepancy. Already the residue ring `ZMod 3` has `-1 ≠ 1`.

The source construction chooses level identifications compatible with evaluation.
The corrected theorem proves existence of such choices from any initial choices.
Its proof adjusts them by the unique lift of the discrepancy through ordinary
scalar restriction and the single-complex functor. The existential parent lift
retains its exact public signature and all of its conclusions. No target statement
or definition changes. The unused invertibility binder is named `_hT`.

## Old

```lean
theorem strictTateTensorTower_evaluation
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d : ℕ)
    (M : AdicTower T (datum.{u} ell))
    (q : ∀ n : ℕ, M.level n ≅
      (_root_.DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))).obj
        (quotientLine T ell n d))
    (h : M.tower = strictDerivedTower T ell d) :
    ∀ n : ℕ,
      (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) n)).map (q n).inv ≫
          (M.evaluation n).hom ≫
          (pbcTowerEvaluation T (pbcAdicCompletion T (datum.{u} ell)) n).map
            (eqToHom h) =
        (Functor.mapDerivedCategorySingleFunctor
          (pbcRestrict (pbcAdicProjection T (datum.{u} ell) n))
          (-(2 * (d : ℤ)))).hom.app (quotientLine T ell n d) ≫
        (Functor.mapDerivedCategorySingleFunctor
          ((CategoryTheory.evaluation ℕᵒᵖ
            (pbcModules T (pbcAdicCompletion T (datum.{u} ell)))).obj (op n))
          (-(2 * (d : ℤ)))).inv.app (strictTower T ell d)
```

## New

```lean
theorem strictTateTensorTower_evaluation
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (_hT : IsUnit (ell : Γ(T, ⊤))) (d : ℕ)
    (M : AdicTower T (datum.{u} ell))
    (q : ∀ n : ℕ, M.level n ≅
      (_root_.DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))).obj
        (quotientLine T ell n d))
    (h : M.tower = strictDerivedTower T ell d) :
    ∃ q' : ∀ n : ℕ, M.level n ≅
        (_root_.DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))).obj
          (quotientLine T ell n d),
      ∀ n : ℕ,
        (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) n)).map (q' n).inv ≫
          (M.evaluation n).hom ≫
          (pbcTowerEvaluation T (pbcAdicCompletion T (datum.{u} ell)) n).map
            (eqToHom h) =
        (Functor.mapDerivedCategorySingleFunctor
          (pbcRestrict (pbcAdicProjection T (datum.{u} ell) n))
          (-(2 * (d : ℤ)))).hom.app (quotientLine T ell n d) ≫
        (Functor.mapDerivedCategorySingleFunctor
          ((CategoryTheory.evaluation ℕᵒᵖ
            (pbcModules T (pbcAdicCompletion T (datum.{u} ell)))).obj (op n))
          (-(2 * (d : ℤ)))).inv.app (strictTower T ell d)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.StrictTateTensorTowerLift | unclaimed | Adapt the proof to unpack the corrected level identifications and use them as witnesses. The entire statement and visibility stay identical. |

This is the only direct Lean importer and the only other module mentioning the
changed theorem. Quarantined sources have no further callers. The parent node
`lem-pur-strict-tate-tensor-tower-lift` is its sole DAG citer; its proof description
is updated, with statement and dependencies unchanged. The unit's realized route
is preserved.

## Status

landed 20261027T233850-L-4126027 2026-10-27 (merge of deliver/D3/Sheaf.Paper.StrictTateTensorTowerLiftEvaluation)
