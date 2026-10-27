# condensed_exchange_one_open_restriction

## Reason

Isolate the comparison of the actual ambient exchange restricted to a single open
with the exact-pullback exchange of the localized square. Existing ringed open
restriction is on section modules; the internal-module transport theorem is ordinary.
Neither supplies this already-derived comparison as a directly applicable declaration.
The assigned theorem now supplies the affine quotient geometry, the covering family,
the degree-zero comparison and the final conservativity argument in Lean.

## Old

This declaration and its module did not exist. The assigned module contained one
whole-proof sorry. All existing signatures, public imports and definitions are preserved.

## New

```lean
theorem condensed_exchange_one_open_restriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y U XU YU' XU' : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (v : U ⟶ Y) [IsOpenImmersion v]
    (a : XU ⟶ X) (fU : XU ⟶ U)
    (b : YU' ⟶ Y') (gU : YU' ⟶ U)
    (hU : XU' ⟶ XU) (fU' : XU' ⟶ YU')
    (wf : IsPullback a fU f v) (wg : IsPullback b gU g v)
    (w : IsPullback hU fU' fU gU)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    IsIso ((upperStar Λ b).mapDerivedCategory.map ((condensedAmbientExchange Λ sq).app K)) ↔
      IsIso ((ClosedTestDerivedExchangeModel.exchange Λ w.toCommSq).app
        ((upperStar Λ a).mapDerivedCategory.obj K))
```

The new theorem has one whole-proof sorry, with a docstring and DAG node containing
the complete argument. No existing definition or instance body changes. The private
`exactSingleIso` helper constructs the canonical Mathlib isomorphism, without a hole.
Both modules select the published, definitionally equal structures locally to avoid
kernel unfolding of the closed-test cache wrappers. This is
a decomposition with one old hole closed and one strictly local comparison hole added.
The new theorem contains no covering family, affine quotient, or degree-zero hypothesis.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedClosedExchangeAffineDescent | F6 (assigned item) | New proof-only import; uses the single-open comparison separately on each quotient chart. Existing signature preserved. |

The new module has no pre-existing users. No module held by another group is adapted.
The only new consumer is the assigned item. No target definition or statement changes.

## Status

landed 20261026T001511-L-4054 2026-10-26 (merge of deliver/F6/Sheaf.Paper.CondensedClosedExchangeAffineDescent)
