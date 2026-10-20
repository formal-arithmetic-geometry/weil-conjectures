# CategoryTheory.ConstantScalarRealization proof-local reducibility settings

## Reason

Preflight classifies local attribute commands as changes requiring a change
record. The two new private canonical constructions use the module
sheafification Hom bijection. Their proof API states the transpose and its
factorization explicitly. Making these private definitions locally irreducible
prevents elaboration from repeatedly unfolding the large sheafification terms
when matching that API. A local elaborator transparency option retains the
setting under which the inverse-construction proofs were developed and checked.
The existing `restriction_properties` theorem proof was also simplified to
reflect finite limits and colimits through the underlying abelian sheaf functor
and use the explicit ordinary tensor adjunction. This avoids invoking the full
derived coefficient theorem merely to establish the ordinary adjunction.

These commands change neither public definitions nor signatures, and are not
exported attributes on existing declarations.

## Old

There were no private `restrictionSeed` or `restrictionComparison` declarations
and no corresponding local reducibility commands. There was no explicit
`backward.isDefEq.respectTransparency` option in this module.

All existing public signatures and definition bodies remain verbatim.

## New

The new private constructions are accompanied by these commands:

```lean
attribute [local irreducible] restrictionSeed
attribute [local irreducible] restrictionComparison
set_option backward.isDefEq.respectTransparency false
```

`restrictionSeed` is the constant module-sheafification unit with its restricted
R-linear action checked using naturality of the constant ring unit.
`restrictionComparison` is its canonical extension by
`PresheafOfModules.sheafificationHomEquiv`. Their transpose and factorization
lemmas are fully proved. Neither definition contains a hole or chooses an
arbitrary witness of a mere existence theorem.

These declarations are private, occur in no public signature or public
definition body, and have no external consumers. All original public imports,
attributes, declaration signatures, and non-theorem bodies are preserved.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstantRealizationDerivedScalarExtension | A3 | Private proof helper elaboration only; two original holes proved. |

There are no forced adaptations or changes to downstream modules. The completed
proofs do not weaken any statement, and this record does not request a statement
or definition repair.

## Status

landed 20261020T211617-L-3478223 2026-10-20 (merge of deliver/A3/Sheaf.Paper.ConstantRealizationDerivedScalarExtension)
