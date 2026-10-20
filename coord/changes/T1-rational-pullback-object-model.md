# lisseRationalAutomorphismPullback

## Reason

The former choice of a rational functor records its object function only by propositional
equality. Rational scalar comparison consequently accumulates equality transports through
several layers of tensor Hom structures. Profiling the unchanged object-choice route
localized expensive kernel comparisons to those inherited Hom structures. The same
mathematical functor can use the prescribed integral model as its object function
literally, by extending the integral functor on tensor Hom modules with the
prescribed pure-tensor formula. This makes the object-identification theorem reflexive
and gives a direct pure-tensor map formula.

The item module is held by T1. No other module is edited. This repairs a computational
interface, without weakening any mathematical statement or changing a target signature.

## Old

```lean
def lisseRationalAutomorphismPullback :
    LisseRationalSheaf l E Y ⥤ LisseRationalSheaf l E Y :=
  (lisseRationalAutomorphismPullback_exists h l E).choose
```

## New

```lean
def lisseRationalAutomorphismPullback :
    LisseRationalSheaf l E Y ⥤ LisseRationalSheaf l E Y where
  obj F := ⟨(lisseIntegralAutomorphismPullback h l E).obj F.integral⟩
  map {F G} f := (lisseRationalAutomorphismData h l E).map F G f
  map_id := (lisseRationalAutomorphismData h l E).map_id
  map_comp := (lisseRationalAutomorphismData h l E).map_comp _ _ _
```

The public `LisseRationalAutomorphismData` record specifies an additive map on each
rational Hom by its value on every pure tensor, and records identity/composition laws.
Its proved existence theorem constructs the map using `TensorProduct.map` on the
coefficient-linear integral reindexing map. Tensor induction proves composition
preservation. Tensor induction also proves that any two additive maps with these
pure-tensor values are equal; the other record fields are proofs. Thus the chosen
record's data are determined uniquely. The new record, existence theorem and data
definition are attached to the existing construction node; no hole is introduced.
All remaining helpers are private and proved.

The module also gives the existing coefficient quotient ring and quotient algebra
locally registered names, `lisseAutomorphismCoefficientRingCommRing` and
`lisseAutomorphismCoefficientRingAlgebra`, to share their structure projections.
Both are literally the original quotient instances, and their registration is local
to this file. No operation on a coefficient ring or algebra changes. 
There is a canonical natural isomorphism from the new functor to the former chosen
functor. If `e F` is the old prescribed object equality, its component is
`eqToIso (e F).symm`. Tensor induction proves naturality: on each pure tensor both
maps are the specified integral pullback, conjugated by these equalities, and both
maps are additive. Thus every scalar and fibre comparison has the same meaning under
the canonical identification. `lisseRationalAutomorphismPullbackObjEq` retains its
signature and is now proved by `rfl`. Functor extensionality also gives propositional
equality with any functor satisfying the old specification: use the object equalities
and tensor induction on its additive maps. No target signature changes. As required by
the definition-change rule, review of any target whose statement uses this definition
is reopened; the canonical identification
above explains why its mathematical pullback meaning is preserved.

## Users

`tools/downstream.py Sheaf.Paper.LisseAdicAutomorphismPullback --uses
lisseRationalAutomorphismPullback` finds only the item module as a textual user.
The refreshed transitive importer list has the 25 modules below. No consumer
signature or source is adapted; no original consumer uses the old defining equation.
Holders are taken from the current shared claim records.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LisseAdicAutomorphismPullback | T1 | literal prescribed objects; same maps after transport |
| Sheaf.Paper.EtaleWeilFundamentalRepresentation | unclaimed | direct importer; unchanged algebraic pullback and fibre interface |
| Sheaf.Paper.EtaleWeilSheafEquivalence | unclaimed | indirect importer; no textual use of the changed declaration |
| Sheaf.Paper.RealBoundaryPathIndependence | unclaimed | indirect importer; no textual use of the changed declaration |
| TargetsCheck | unclaimed | indirect importer; no textual use of the changed declaration |
| WeilConjectures | unclaimed | indirect importer; no textual use of the changed declaration |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | indirect importer; no textual use of the changed declaration |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | indirect importer; no textual use of the changed declaration |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | indirect importer; no textual use of the changed declaration |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | indirect importer; no textual use of the changed declaration |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | indirect importer; no textual use of the changed declaration |
| WeilConjectures.Statement | unclaimed | indirect importer; no textual use of the changed declaration |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | indirect importer; no textual use of the changed declaration |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | indirect importer; no textual use of the changed declaration |
| WeilConjectures.ZetaFunction.Examples | unclaimed | indirect importer; no textual use of the changed declaration |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | indirect importer; no textual use of the changed declaration |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | indirect importer; no textual use of the changed declaration |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | indirect importer; no textual use of the changed declaration |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | indirect importer; no textual use of the changed declaration |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | indirect importer; no textual use of the changed declaration |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | indirect importer; no textual use of the changed declaration |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | indirect importer; no textual use of the changed declaration |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | indirect importer; no textual use of the changed declaration |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | indirect importer; no textual use of the changed declaration |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | indirect importer; no textual use of the changed declaration |
| WeilConjectures.ZetaFunction.Weights | unclaimed | indirect importer; no textual use of the changed declaration |

The complete item compiled against the current server library in 57.4 seconds. The
unchanged direct importer `Sheaf.Paper.EtaleWeilFundamentalRepresentation` compiled
against that sandbox artifact in 5.6 seconds. No consumer required adaptation.
`tools/downstream.py --uses` confirms no textual user outside this item. Every
existing signature is retained, and the canonical identification above preserves
the mathematical meaning of indirect consumers and targets.

## Status

landed 20261020T230835-L-619038 2026-10-20 (merge of deliver/T1/Sheaf.Paper.LisseAdicAutomorphismPullback)
