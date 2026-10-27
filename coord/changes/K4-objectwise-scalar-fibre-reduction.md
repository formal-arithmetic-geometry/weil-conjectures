# ScalarFibreComponents and ScalarFibreCoherence

## Reason

Separate the original scalar fibre theorem into objectwise geometric construction,
naturality on fractional lattice maps, and tensor/mixed coherence. The item then
constructs natural isomorphisms and their fixed full-heart comparison maps explicitly.
Existing declarations and signatures remain verbatim, including NormalizedScalar.
No module outside this delivery is adapted. No target statement or definition it uses
changes mathematical meaning.

## Old

The five declarations below did not exist. The item had one sorry in
`AlgebraicGeometry.Scheme.AdicFibreComparison.adic_normalized_fibre_scalar`:

```lean
theorem adic_normalized_fibre_scalar :
    ∃ (ω : Fibres (k := k) l R) (α : NormalizedPullback l R ω),
      Nonempty (NormalizedScalar l R ω α) := by
  sorry
```

## New

New data in `Sheaf.Paper.ScalarFibreComponentData`:

- `scalarHeartUnit`: NatIso.ofComponents of the actual raw scalar unitor,
  lifted by ObjectProperty.isoMk; naturality is the raw unitor's naturality.
- `scalarHeartComp`: the same restriction of the actual raw scalar associator.
- `scalarHeartMixed`: the same restriction of the realization family's raw mixed map.
- `ScalarFibreComponents`: objectwise scalar isomorphisms with the original germ and
  local lattice reduction-cone normalization formulas; no naturality or coherence field.
- `ScalarFibreCoherence`: the identity, composition and mixed equations for those
  specified components, using the three actual restricted heart comparisons.

The definitions are written constructions or structure declarations, with no sorry.
The three new public theorem signatures are recorded verbatim in their DAG nodes.
Their proofs are postponed. The item's statement and NormalizedScalar data are unchanged;
its proof forms natural isomorphisms from components and naturality, retains the two
normalization fields, and supplies the exact raw-normalized heart comparison witnesses.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicNormalizedFibreScalar | K4 | Constructs the unchanged assertion from the three separate steps. |
| Sheaf.Paper.ScalarFibreComponents | K4, new | States objectwise existence for the new data. |
| Sheaf.Paper.ScalarFibreNaturality | K4, new | States naturality of given components. |
| Sheaf.Paper.ScalarFibreCoherence | K4, new | States coherence of given components. |
| Sheaf.Paper.AdicNormalizedFibreCommonStage | unclaimed; not adapted | Existing NormalizedScalar interface is identical. |

`tools/downstream.py Sheaf.Paper.AdicNormalizedFibreScalar --uses NormalizedScalar`
reported only the item and AdicNormalizedFibreCommonStage as declaration users.
The new names have no pre-existing users.

## Status

landed 20261025T143554-L-1053051 2026-10-25 (merge of deliver/K4/Sheaf.Paper.AdicNormalizedFibreScalar)
