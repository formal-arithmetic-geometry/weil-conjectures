# AlgebraicGeometry.Scheme.etale_noetherian_global_constructibility

## Reason

Preflight classifies changes to file-level universe and open commands as interface changes.
The proofs need an independent universe for private site helpers and names from Limits.
This record documents those commands and the new proved local-system theorem. Both existing
public theorem signatures, their visibility, and both public imports remain identical.
No existing definition changes, and no target meaning changes.

## Old

The existing file commands, verbatim:

```lean
universe u v

open CategoryTheory
```

The new module Sheaf.CategoryTheory.CoefficientFiniteLocalSystemsPullback did not exist.

## New

The replacement file commands, verbatim:

```lean
universe u v w

open CategoryTheory CategoryTheory.Limits
```

The additional universe occurs only in private helper declarations. Both existing public
statements still use exactly universes u and v. Opening a namespace changes name resolution
in this file; it does not export a new instance, notation, attribute, or option.

The new module proves CategoryTheory.coefficient_finite_local_systems_pullback: on small
finite-limit sites, a continuous finite-limit-preserving functor's sheafified left Kan
extension preserves the existing locally constant finitely generated module predicate.
Its complete signature and proof are recorded in node
lem-sfb-coefficient-finite-local-systems-pullback. Its private definitions explicitly build
comparison isomorphisms from existing adjunctions. No data is chosen from an unproved
existence result. It is imported only as a proof dependency by the item.

## Users

The downstream.py check with --uses etale_noetherian_global_constructibility and
proEtale_noetherian_global_constructibility finds only their declarations in the item;
none of the 234 transitive downstream modules mentions either name. Those modules retain
the same public imports and statements. File-local open and universe commands do not
change their elaboration environments. No consumer adaptations are necessary.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.NoetherianGlobalConstructibility | H4 | Both proofs use the new helper; public signatures identical. |
| Sheaf.CategoryTheory.CoefficientFiniteLocalSystemsPullback | new in this delivery, H4 | Proved generic local-model preservation theorem, used by the item. |

## Status

landed 20261019T005302-L-2748285 2026-10-19 (merge of deliver/H4/Sheaf.AlgebraicGeometry.NoetherianGlobalConstructibility)
