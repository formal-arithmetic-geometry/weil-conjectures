# CochainComplex.exists_quasiIso_degree_zero_of_bounded_degree

## Reason

The new proved private helpers establish the value of d on the zero object and its
invariance under isomorphism. They use `open scoped ZeroObject` to enable Mathlib's
chosen zero-object notation and associated instances. The delivery check classifies
a new top-level scope command as an interface-sensitive change. This record accounts
for that command. No declaration signature, public import, definition, or exported
instance is changed. The proof-only import replacement and private helpers support
the finite dimension-lowering proof documented in report.md and the existing node.

## Old

```lean
open CategoryTheory CategoryTheory.Limits
```

## New

```lean
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
```

This scope affects elaboration of this file. It adds no exported declaration or
registration to downstream files. The public theorem retains its original complete
type. All newly added helpers are private proved theorems; no public data definition
has a private helper in its body or signature.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.DegreeZeroComplexReplacement --uses
CochainComplex.exists_quasiIso_degree_zero_of_bounded_degree` reports zero downstream
modules and only the declaration's own module as a source occurrence. Text search of
both library roots agrees. No consumer needs adaptation and no target statement or
definition changes meaning. The theorem was assigned through declared proof
requirements of still-open parents; it currently has no direct importing parent.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.DegreeZeroComplexReplacement | V2 | Local notation scope for proved private helpers; public signature unchanged. |

## Status

landed 20261018T144425-L-3507107 2026-10-18 (merge of deliver/V2/Sheaf.Algebra.Homology.DegreeZeroComplexReplacement)
