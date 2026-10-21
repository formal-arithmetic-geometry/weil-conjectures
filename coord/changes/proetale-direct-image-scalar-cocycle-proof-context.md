# proEtaleDirectImageScalarCocycle proof elaboration context

## Reason

The complete normalized-mate proof needs local transparency control to prevent Lean
from unfolding chosen adjunctions, derived categories and tensor constructions while
comparing their API formulas. The stage-3 static check classifies the new `open`,
`noncomputable section`, option and local-attribute commands as an interface change.
This record documents that classification. All attributes are explicitly local;
none changes the persistent attributes of an imported declaration. The namespace,
exported theorem signature and four public imports are unchanged. Private proof
helpers and private proof imports supply the argument. There is no definition or
statement repair, no new hypothesis and no consumer adaptation.

## Old

The original elaboration context, verbatim:

```lean
@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale
```

## New

The new initial elaboration context, verbatim:

```lean
@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] HasDerivedCategory.standard
  SheafOfModules.SuccessiveDerivedQuotient.sectionTensor
  SheafOfModules.SuccessiveDerivedQuotient.pure
  Scheme.completedAdicDerivedChange
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Scheme.proEtaleRingModulePullback
  Scheme.proEtaleConstantRingComparison Scheme.proEtaleRingDerivedAdjunction
```

Additional local commands in the proof, verbatim:

```lean
attribute [local irreducible] coefficientAdjData

attribute [local irreducible] pbcScalarAdjunction pbcDerivedScalarAdjunction
  Adjunction.leftAdjointCompIso SheafOfModules.SuccessiveDerivedQuotient.ordinaryComp
  pbcDerivedRestrictComp

attribute [local semireducible] pbcDerivedRestrictComp Adjunction.leftAdjointCompIso
  SheafOfModules.SuccessiveDerivedQuotient.ordinaryComp
```

The exported theorem's signature remains verbatim identical to the old signature.
The noncomputable section permits the private presentation and adjunction-data
constructions; it does not change the theorem statement or its kernel proof rules.

## Users

`python3 tools/downstream.py Sheaf.SecSmoothPurity.ProEtaleDirectImageScalarCocycle
--uses proEtaleDirectImageScalarCocycle` reports zero downstream Lean modules and
one textual declaration use, in this item itself. DAG parents with unfinished proofs
are preserved; this delivery does not withdraw the item or any dependency module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SecSmoothPurity.ProEtaleDirectImageScalarCocycle | E2 | Complete proof; local elaboration context only; public theorem signature unchanged. |

No other module changes. No target definition or statement changes or needs renewed
semantic review.

## Status

landed 20261021T214746-L-1848167 2026-10-21 (merge of deliver/E2/Sheaf.SecSmoothPurity.ProEtaleDirectImageScalarCocycle)
