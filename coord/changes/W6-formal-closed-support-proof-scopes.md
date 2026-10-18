# formal_closed_support_sheaves proof elaboration scopes

## Reason

The stage-3 static checker requests a change record for added open commands and
private helper elaboration scopes. These commands support only proofs. Every existing
signature, definition body, visibility and public import is unchanged. No global
instance or attribute is introduced. No target statement or definition changes;
no target statement review is reopened.

## Old

```lean
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
```

## New

```lean
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing
```

Six private, completely proved helpers precede the unchanged variable command.
Their binders are explicit and do not become public declarations. The setting
`backward.isDefEq.respectTransparency false` is scoped with `in` to four private
helper proofs. The original variable command remains verbatim before the existing
definitions and theorem. The added open commands affect local proof name/notation
resolution; they do not register instances, notation, or attributes for importers.

## Users

The read-only downstream.py query lists the two transitive consumers below.
Its declaration-use query also includes this item. Both consumers use only the
unchanged closedModuleSectionsWithSupport API; neither needs adaptation. Claim
holders were read from coord/claims at preparation time.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FormalClosedSupportSheaves | W6 | private proved helpers and local proof scopes only |
| Sheaf.Paper.FormalClosedSupportDerived | W5 | unchanged signatures and functor definitions; no adaptation |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | unchanged signatures and functor definitions; no adaptation |

## Status

landed 20261018T150151-L-3800951 2026-10-18 (merge of deliver/W6/Sheaf.Paper.FormalClosedSupportSheaves)
