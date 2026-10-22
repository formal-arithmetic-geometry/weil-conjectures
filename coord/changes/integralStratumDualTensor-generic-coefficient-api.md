# AlgebraicGeometry.ProEtale.CondensedRing.integralStratumDualTensor

## Reason

The coefficient-specific definition forces repeated reduction of the derived monoidal
structure when the generic duality argument is specialized to the integral coefficient
ring. Kernel profiling isolated comparisons of the projected tensor unit and tensor
functor taking about sixteen seconds each, and the complete item exceeded the sixty-second
file limit. Keep the same real construction behind a named generic coefficient interface,
then specialize that interface. No object is selected from an existence assertion.

The generic constructions `stratumModuleDerivedSections`, `stratumModuleDual` and
`stratumModuleDualTensor` are public because a public definition must not refer to a private
helper. They live in this item's module and are attached to its existing DAG node. Their
bodies are exactly derived Hom from the regular module, internal Hom evaluated at the
ordinary derived tensor unit, and tensor by that dual, respectively. The ordinary sections
abbreviation and all existing public declaration signatures and public imports stay unchanged.

## Old

```lean
def integralStratumDualTensor (S : Scheme.{u})
    (L : pulledBackModuleObjects (integralCoefficientRing l E) S) :
    integralDerived l E S ⥤ integralDerived l E S :=
  (derivedTensor (integralCoefficientRing l E) S).obj (integralStratumDual l E S L)
```

## New

```lean
def integralStratumDualTensor (S : Scheme.{u})
    (L : pulledBackModuleObjects (integralCoefficientRing l E) S) :
    integralDerived l E S ⥤ integralDerived l E S :=
  stratumModuleDualTensor (integralCoefficientRing l E) S L
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralStratumHomFormula | K6 | Same construction via a generic coefficient definition; the proof specializes the generic Hom formula. |

`tools/downstream.py Sheaf.Paper.IntegralStratumHomFormula --uses
integralStratumSections integralStratumDerivedSections integralStratumDual
integralStratumDualTensor` lists only the item itself as a textual user of these names.
The four downstream modules are `Sheaf.Paper.IntegralStratumExtBound`,
`Sheaf.Paper.IntegralConstructibleExt`, `Sheaf.Paper.BrownHypothesesGeneration` and
`Sheaf.SixFunctorsBasics.BrownHypotheses`. Their statements do not mention the changed
names; their imports and statements need no adaptation. No foreign module is edited.

The definitions retain the same ordinary, uncompleted derived categories and canonical
right-derived, internal-Hom and tensor constructions. No hypothesis or conclusion changes.
The target signatures remain untouched. The required semantic review is reopened for any
target that uses these definitions through its dependencies; the reviewer can unfold the
generic construction to recover the original definition.

## Status

landed 20261022T020109-L-22063 2026-10-22 (merge of deliver/K6/Sheaf.Paper.IntegralStratumHomFormula)
