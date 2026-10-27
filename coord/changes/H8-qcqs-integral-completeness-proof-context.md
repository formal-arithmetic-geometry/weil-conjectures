# Sheaf.Paper.QcqsIntegralFiniteModelCompleteness proof context

## Reason

The complete proof uses internal-module scoped instances, limits and triangulated
category lemmas. Local irreducibility of `IsDerivedComplete` prevents elaboration
from unfolding the concrete strict-tower predicate; its public defining equation is
unchanged. Preflight requests a change record for the added command context.

The private unit-route import
`Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit` is retained. All six
public imports, the complete body of `HasClassicalFiniteReduction`, and the signature
of `qcqs_integral_finite_model_completeness` are preserved verbatim. No target or
public definition changes its meaning. The attribute is explicitly local and the
added opens only control elaboration within this module. No new public declaration
is introduced. The repair adds `import all Sheaf.Paper.LocalizingClosureCtfEqualsBc`
as a proof-only dependency and removes the two duplicate private comparison lemmas.
Their existing owner module is unchanged; its private `ordinary_constructible_iff`
is used directly in the proof.

## Old

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale
```

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale

open CategoryTheory.Limits

attribute [local irreducible] IsDerivedComplete
```

## Users

`tools/downstream.py Sheaf.Paper.QcqsIntegralFiniteModelCompleteness --uses
qcqs_integral_finite_model_completeness` reports zero downstream Lean modules and
only the defining module as a textual user. This does not withdraw any unfinished
parent DAG node. No consumer source is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.QcqsIntegralFiniteModelCompleteness | H8 | Complete the existing proof; public API unchanged. |

## Status

landed 20261023T231521-L-3611614 2026-10-23 (merge of deliver/H8/Sheaf.Paper.QcqsIntegralFiniteModelCompleteness)
