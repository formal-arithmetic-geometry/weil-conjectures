# WeilConjectures.SmoothExchangeScalarCompatibility.middle

## Reason

The literal component construction causes conversion of repeated rational-category
and coefficient-instance aliases when proving naturality. Fully expanding its hom
projection exhausted both elaborator and kernel limits in the worker's probes.
Constructing the same map in the functor category gives naturality directly.

The new `middle_component` equation specifies exactly the old canonical composite.
The tensor comparison selected by `middleFunctor` is uniquely determined by all
its components: `tensorComparisonUnique` proves uniqueness by natural-transformation
extensionality, in addition to the existing component-normalized existence theorem.
Thus the selection uses uniquely determined data. The abstract constructor retains
the literal canonical component maps as data and uses the selected comparison only
in its naturality proof.

## Old

```lean
def middle (sq : u ≫ f = f' ≫ v) (d : ℕ)
    (E : AdicPurityScalarNaturality.Field D C) (K : RCat D C E Y) :
    (rationalDerivedPullback C.l E.val u).obj ((H D C f d E).obj K) ≅
      (H D C f' d E).obj ((rationalDerivedPullback C.l E.val v).obj K) := by
  dsimp only [H, RationalSmoothPurityCanonical.rationalSource, Functor.comp_obj,
    Functor.prod'_obj, Functor.const_obj_obj]
  exact canonicalRationalPullbackTensor C.l E.val u
      ((sfRationalTwistingCoefficient C.l E.val X (d : ℤ))⟦2 * (d : ℤ)⟧)
      ((rationalDerivedPullback C.l E.val f).obj K) ≪≫
    (rationalDerivedTensor C.l E.val X').mapIso
      (Iso.prod
        (((rationalDerivedPullback C.l E.val u).commShiftIso (2 * (d : ℤ))).app _ ≪≫
          (shiftFunctor _ (2 * (d : ℤ))).mapIso (CanonicalTate.rationalPull C.l E.val u d))
        ((TwistedPullbackScalars.t C.l E.val u f f' v sq).app K))
```

## New

```lean
def middle (sq : u ≫ f = f' ≫ v) (d : ℕ)
    (E : AdicPurityScalarNaturality.Field D C) (K : RCat D C E Y) :
    (rationalDerivedPullback C.l E.val u).obj ((H D C f d E).obj K) ≅
      (H D C f' d E).obj ((rationalDerivedPullback C.l E.val v).obj K) :=
  (middleFunctor D C u f f' v sq d E).app K
```

`middleFunctor` is constructed by `tensorExchangeIso` from the normalized tensor
comparison, the original shifted root-line pullback, and the original ordinary
pullback square. `middle_component` identifies every component with the Old body.
No original declaration signature, `Conclusion` clause, or target statement changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.SmoothExchangeScalarCompatibility` | F9 | `exchange` still uses `middle`; its canonical formula is preserved by `middle_component`. |

No other current Lean module directly imports this module. DAG parents remain
needed; this is not a withdrawal or a claim that those parents are proved.
The canonical-component equation is the semantic preservation check for the
independent reader, including every target that later uses this definition.

## Status

landed 20261027T021324-L-2757149 2026-10-27 (merge of deliver/F9/Sheaf.Paper.SmoothExchangeScalarCompatibility)
