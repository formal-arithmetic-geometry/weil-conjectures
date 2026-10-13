# resolutionSectionClass_open_restriction local proof options

## Reason

The static interface checker classifies additions to the file's command stream
as changes other modules see. The added commands are local irreducibility
attributes and options scoped to proved declarations, used to keep the named
cohomology maps folded while elaborating composition identities. They do not
change any exported declaration, definition, notation, instance or attribute.
No consumer needs an adaptation.

## Old

```
attribute [local instance] enoughInjectives
```

The target theorem originally had no scoped proof-elaboration options.

## New

```
attribute [local instance] enoughInjectives
attribute [local irreducible] moduleCohomologyFMap sectionCohomologyTheta
  resolutionSectionClass
```

The private proved helper is scoped by:

```
set_option backward.defeqAttrib.useBackward true in
```

The target theorem's elaboration is scoped by:

```
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 800000 in
```

The increased heartbeat allowance is explained beside the theorem: comparing
section complexes unfolds the scheme and ringed-space module interfaces.
Existing signatures, visibility, definition bodies and public imports are
identical. Local attributes are not exported; the options apply only to their
following declaration, not to importing modules.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ResolutionSectionClassOpenRestriction | G1 | Local proof elaboration only; no exported interface change |

There are no declaration-level changes to enumerate in downstream users.
No module held by another group is adapted.

## Status

landed 20261013T164047-L-1668050 2026-10-13 (merge of deliver/G1/Sheaf.AlgebraicGeometry.ResolutionSectionClassOpenRestriction)
