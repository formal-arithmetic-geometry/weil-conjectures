# Smooth lisse integral lattice proof context

## Reason

The main theorem now uses proved private localization and embedding helpers and an
abstract integral-model theorem. Preflight classifies the additional section variables
and elaborator options as a visible context change. All original public declarations,
instances, definitions, signatures, universes and public imports are retained verbatim.
The added section variables bind only private helpers. The elaborator options affect
proof elaboration, not exported mathematical data.

This packet also proves two existing commutativity lemmas in the unclaimed dependency
`Sheaf.Paper.CompletedIntegralCoefficients`. It changes only those proof bodies and
adds a private proof import. No module held by another group is edited or adapted.

## Old

The main file's options were:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
```

Both `completedIntegralCoefficient_mul_commUnrestricted` and
`completedIntegralCoefficient_mul_comm` had proof `by sorry`.
Their statements are unchanged.

## New

The main file additionally uses:

```lean
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
```

Private helpers use locally scoped section variables for the site, coefficient rings,
modules and coefficient map. The original theorem is proved from its original
hypotheses. Its new proof-only imports are not re-exported.

The unrestricted commutativity proof evaluates the inverse limit, applies joint
injectivity of the projections, and uses commutativity in each finite quotient
constant sheaf. The finite-field-datum wrapper applies the unrestricted theorem.
No definition, statement, signature or visibility changes in that dependency.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.SmoothLisseIntegralLattice | T8 | theorem proof and private proof context; original interface unchanged |
| Sheaf.Paper.NormalCompletedIntegralModel | new, T8 | new abstract model statement; one remaining hole |
| Sheaf.Paper.CompletedIntegralCoefficients | unclaimed | two theorem proofs closed; no interface change |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | sole direct main-module importer; unchanged interface |
| Sheaf.SixFunctors.IntegralDualizing | G8 | direct textual user of unrestricted commutativity; identical statement |

Other importers of the completed coefficients see the same definitions and statements.
No forced adaptation is required. The new model statement has its own DAG node. All
three delivered modules compile together with the changed dependency.

## Status

landed 20261019T231355-L-579479 2026-10-19 (merge of deliver/T8/Sheaf.Paper.SmoothLisseIntegralLattice)
