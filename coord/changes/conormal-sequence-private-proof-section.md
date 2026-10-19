# AlgebraicGeometry.Scheme.Hom.conormalStalkFibre_shortExact_of_smooth

## Reason

Prove the conormal fibre sequence using the actual stalk rings and private helpers.
The static interface checker flags the added section, universe, open and option commands.
They serve only proof elaboration. Every existing declaration signature, visibility and
all four public definition bodies remain identical. No target meaning changes.

## Old

The original commands preceding the theorem, after the fourth public definition, were empty:

```lean
```

The original theorem proof was:

```lean
:= by
  sorry
```

## New

The following commands enclose the private helpers and existing theorem:

```lean
section Proof

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe v w t

open TensorProduct CategoryTheory.Limits TopologicalSpace
```

Before the public theorem the transparency options are restored:

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
```

The added section is closed immediately after the theorem:

```lean
end Proof
```

The section's universe names, opens and options do not propagate to importers.
No instances, notation or elaboration attributes are registered. The only new import is
private: `import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk`.
All added helpers are private and proved; the theorem has a complete proof.
The complete replacement proof is in the delivered module.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ConormalSequenceSmoothImmersion --uses`
with all five existing declaration names found no downstream textual users. There are
29 transitive importers; the two direct importers are listed below. Their statements and
proofs see exactly the original public interface. Neither consumer requires adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ConormalSequenceSmoothImmersion | C9 | Proves the theorem; existing signatures and definitions preserved. |
| Sheaf.AlgebraicGeometry.RegularImmersionLinearization | Q7 | Direct private importer; unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.BertiniSingularLocusDimension | unclaimed | Direct private importer; unchanged interface; no adaptation. |

## Status

landed 20261019T160418-L-3355149 2026-10-19 (merge of deliver/C9/Sheaf.AlgebraicGeometry.ConormalSequenceSmoothImmersion)
