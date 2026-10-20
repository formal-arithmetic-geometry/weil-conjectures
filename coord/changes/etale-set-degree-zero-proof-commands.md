# EtaleSetDegreeZeroFlatBaseChange proof commands

## Reason

The static interface comparison records changes to top-level `open` commands and
scoped elaboration options. The completed proof opens the limit and opposite-category namespaces and scoped
étale notation, and uses local transparency options for its chart comparisons.
These commands affect elaboration in this file. Both public theorem signatures,
all existing public imports and the canonical exchange construction are unchanged.
All added declarations are private and fully proved or concretely constructed.
No downstream adaptation is required.

## Old

```lean
open CategoryTheory

namespace AlgebraicGeometry
```

No local `backward.isDefEq.respectTransparency` options occurred in the old file.

## New

```lean
open CategoryTheory Limits Opposite
open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry
```

The following scoped commands precede private comparison proofs;
each `in` restricts its option to the following declaration:

```lean
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
```

Local irreducibility attributes on
`Functor.sheafPullbackConstruction.sheafPullback`, `setComp`, and `setRestriction`
apply within this module and prevent expensive unfolding in these proofs.

There is no changed public definition or statement. The two theorem signatures are
verbatim those of the previous version.

## Users

`tools/downstream.py` lists the following five downstream modules. Neither theorem
name occurs in them yet; all original interfaces are preserved. They are not
adapted by this delivery, irrespective of their current holders.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbelianDegreeZeroFlatBaseChange | not queried; no adaptation | unchanged |
| Sheaf.AlgebraicGeometry.ArbitrarySchemeUntensoredBaseChange | not queried; no adaptation | unchanged |
| Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReduction | not queried; no adaptation | unchanged |
| Sheaf.AlgebraicGeometry.PunctualTensorBaseChange | not queried; no adaptation | unchanged |
| Sheaf.Targets.BaseChangeTowardsFields | not queried; no adaptation | unchanged |

The assigned module itself, held by J1, now contains the completed proofs.
Target statements and their mathematical meaning are unchanged.

## Status

landed 20261020T122110-L-476831 2026-10-20 (merge of deliver/J1/Sheaf.AlgebraicGeometry.EtaleSetDegreeZeroFlatBaseChange)
