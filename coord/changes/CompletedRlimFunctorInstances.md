# CompletedRlimFunctor instance scoping

## Reason

The new Roos proof imports pro-etale countable-product exactness. Its transitive
imports expose sheafification instances with independent coefficient universes.
Specialize the published sheafification and locally-bijective instances to
`AddCommGrpCat.{t + 1}` so elaboration uses the coefficient universe in the
existing statements. Disable the broad essentially-small sheafification instance
only for the individual declarations that need these specializations.

The file also sets `backward.isDefEq.respectTransparency` to `false` for its own
elaboration. Neither this option nor the local registrations changes an imported
module's elaboration environment. The mechanical interface check records the
changed commands, so this record documents them for independent review.

## Old

The repository module has no `completedRlimAbSheafify` or
`completedRlimAbLocallyBijective` helper, no local registrations of these facts,
and no scoped removal of the broad sheafification instance. Its setup includes:

```lean
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [instance] reductionTower_isGrothendieckAbelian
```

## New

The existing declarations keep their original signatures and constructions.
The setup additionally contains:

```lean
set_option backward.isDefEq.respectTransparency false
```

and the following proved private facts and local registrations:

```lean
private theorem completedRlimAbSheafify (T : Scheme.{t}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{t, 0} T

private theorem completedRlimAbLocallyBijective (T : Scheme.{t}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} T

attribute [local instance] completedRlimAbSheafify completedRlimAbLocallyBijective
```

Each affected declaration is individually preceded by:

```lean
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
```

There is no unscoped removal of this instance. The pre-existing registration of
`reductionTower_isGrothendieckAbelian` is retained verbatim. No new global
instance is registered.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompletedRlimFunctor | M3 | Uses the local facts during elaboration; all existing public signatures and constructions are retained. |

`tools/downstream.py Sheaf.Paper.CompletedRlimFunctor --uses completedRlimAbSheafify`
found zero source users of the new private name. Both new helper names are private,
and their instance registrations and the broad-instance removal are local.
All downstream importers retain the existing public API and global instances;
no consumer requires adaptation. There is no target-statement or definition change
requiring a target semantics review.

## Status

landed 20261019T005341-L-2755768 2026-10-19 (merge of deliver/M3/Sheaf.Paper.CompletedRlimFunctor)
