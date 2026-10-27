# WeilConjectures.IntegralAmbient.tensorRepresentative

## Reason

The original signature forces Lean to repeatedly normalize large cochain tensor,
Roos, and derived-category object constructions while comparing endpoints. A complete
proof using the direct interface checked but took 92.7 seconds, exceeding the file
limit. The new interface captures the existing category data once, constructs all
operations and their proved compatibility laws as `rawAmbientPackage`, and uses one
shared record `ambientPackage`. The latter is chosen from the **proved** theorem
that equality to this explicitly constructed record determines a unique value;
`ambientPackage_eq` proves literal equality of the entire record to that construction.
Thus every functor, comparison and augmentation is exactly the recorded one.
There is no selection from an unproved arbitrary existence theorem and no new hole.

The carrier and good-complex types reduce to the original ones through
`ambientTensorPresentation`. Named good localization and lift functors share their
endpoints. In particular, `modelPullUnitMap` and `modelTensorUnitMap` are the images
of the same quotient Roos units followed by the same strict tower maps. The tensor
representative is the component of the exact recorded tensor model comparison.
The theorem's hypotheses, universal-derived condition, good-object isomorphisms,
completion comparisons, strict tower normalizations and augmentation equations are
all retained. These changes concern S7's own non-target module; no adopted source
module and no statement in `Challenge.lean` is changed. Definitions used by targets
receive renewed statement/definition review. The final file compiled in 39.4 seconds.

## Old

```lean
def tensorRepresentative (W : Scheme.{t})
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) :
    DerivedCategory.Q.obj
      ((coefficientTotalTensor.{u, t + 1, t} (ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).obj (P.obj, Q.obj)) ≅
      (IntegralOnSlice.duality l E W none).closed.tensor.obj
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) :=
  CoefficientTensorModels.iso (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)
    (IntegralOnSlice.duality l E W none).closed
    (IntegralOnSlice.duality l E W none).models P.obj Q.obj P.property.1 Q.property.1
```

## New

```lean
def tensorRepresentative (W : Scheme.{t})
    (P Q : (ambientGood l E W).FullSubcategory) :
    (modelQ l E W).obj ((modelTotalTensor l E W).obj (P.obj, Q.obj)) ≅
      (modelOrdinaryTensor l E W).obj
        ((modelQ l E W).obj P.obj, (modelQ l E W).obj Q.obj) :=
  (modelTensorModelComparison l E W).app
    (⟨P.obj, ambientGoodFlat l E W P.obj P.property⟩,
      ⟨Q.obj, ambientGoodFlat l E W Q.obj Q.property⟩)
```

## Users

`tools/downstream.py Sheaf.Paper.IntegralAmbientOperationModels --uses
integralAmbientOperationModels tensorRepresentative` reports 40 modules downstream
by imports, and one actual declaration user for each changed name: this module.
A source and quarantine search distinguishes similarly named declarations in other
namespaces; none is a use of these changed declarations. The returned review additionally
identified an `import all` instance-environment consumer. The proof-import isolation
documented in `S7-point-integral-tensor-chain-instance-repair.md` removes the leak
at its source; no consumer adaptation is delivered. All original operation-interface
declarations are attached to the same node.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.IntegralAmbientOperationModels` | S7 | uses the exact shared operation interface; original mathematical content retained |
| `Sheaf.Paper.PointIntegralTensorChain` | unclaimed; quarantined | preserved unchanged; the proof-import boundary now hides the two broad instances |

## Status

landed 20261026T111926-L-1778770 2026-10-26 (merge of deliver/S7/Sheaf.Paper.IntegralAmbientOperationModels)
