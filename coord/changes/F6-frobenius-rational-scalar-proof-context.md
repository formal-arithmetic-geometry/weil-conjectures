# Frobenius rational scalar comparison proof context

## Reason

The rational operation scalar comparison is proved without changing its statement
or the constructed operations. Integrated profiling found repeated unfolding of
residue-field and derived-category constructions during instance search in the
geometric functors. Local irreducibility keeps the exact existing witnesses while
avoiding those reductions. The attribute affects this module's elaboration only.
The generic localization helper also takes the integral scalar isomorphism
explicitly, avoiding expensive inference from its component expression.

## Old

The public theorem signature and all existing definition bodies remain verbatim.
There were no local irreducibility attributes for the declarations listed below.
The proof of
`WeilConjectures.frobeniusCohomologyRationalOperationScalar_existsUnique`
was `by sorry`.

## New

The new file-local command is:

```lean
attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
```

Five fully proved private lemmas construct and characterize the localization of
an integral natural isomorphism, then specialize it to the selected operation.
There are no new public declarations, changed signatures, changed definition
bodies, public attributes, imports, or target meanings.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | F6 | One theorem hole closed; local elaboration attributes. |

The private helpers have no external consumers. The read-only
`tools/downstream.py Sheaf.SixFunctors.FrobeniusCohomologyTransportIso --names`
audit found the existing transitive consumers. Their public interface and
referenced definitions are unchanged, and no consumer adaptation is required.

## Status

landed 20261025T180657-L-4019164 2026-10-25 (merge of deliver/F6/Sheaf.SixFunctors.FrobeniusCohomologyTransportIso)
