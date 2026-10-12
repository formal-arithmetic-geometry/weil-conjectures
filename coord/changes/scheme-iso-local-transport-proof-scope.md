# scheme_iso_local_perfect_transport proof scope

## Reason
The proof adds local proof infrastructure and proof-only imports. The delivery checker
requires a record for the module's scoped command changes. The second reader also
repairs slow elaboration: respecting transparency in the two remaining declarations compiled
within the 60-second limit, where the library's global false option repeatedly timed out.
The existing theorem's signature and docstring are byte for byte unchanged.

## Old
The repository's import and open commands, verbatim:

```lean
public import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.AlgebraicGeometry.DerivedCategory

@[expose] public section

universe u w₁ w₂

open CategoryTheory
```

There were no local attributes or declaration-scoped options in this module.

## New
The delivered import and open commands, verbatim:

```lean
public import Sheaf.AlgebraicGeometry.PerfectComplex
import all Sheaf.AlgebraicGeometry.DerivedPullbackPerfect
import all Sheaf.AlgebraicGeometry.SchemeIsoDerivedRestrictionSquare

@[expose] public section

universe u w₁ w₂

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
```

The added local attribute, verbatim:

```lean
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
```

Each of `localRestrictionSquare` and `scheme_iso_local_perfect_transport` is preceded
by this scoped option, verbatim:

```lean
set_option backward.isDefEq.respectTransparency true in
```

The proved private restriction-square helper supplies proof infrastructure. The
proof-only `import all` commands reuse the existing private strict-perfectness theorem
and moduleIsoEquivalence without changing their defining modules. The duplicate
moduleIsoEquivalence definition is deleted, as requested in return H4 by X-1a79a.
No duplicate finite-free, strict-perfectness or unit helper is declared. No signature or definition
of an existing declaration changes; no public import, attribute or option is added.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SchemeIsoPerfectTransport | unclaimed | Uses the unchanged target theorem; local opens, attributes and scoped elaborator options do not change its statement. |

## Status
landed 20261012T230753-L-1907282 2026-10-12 (merge of deliver/C3/Sheaf.AlgebraicGeometry.SchemeIsoPerfectLocalTransport)
