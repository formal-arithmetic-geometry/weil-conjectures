## What changed

Filled `lisse_finite_level_proetale_local_iso_sections` by composing two named
intermediate statements. Added `LisseFiniteLevelFixedRealizationLocalModel`, which
states the local transport of the supplied model marking through the fixed realization,
and `LisseFiniteLevelProEtaleLocalIsoDescent`, which states the geometric point lifting
and inverse-pair descent step. The main module now imports the derived morphism
comparison API publicly, since its statement mentions the derived local Isom presheaf.
All three modules compile in import order.

## Proved and sorry left

The original theorem is proved from the two new intermediate declarations. The two new
public declarations remain as intentional split-off obligations:

- `lisse_finite_level_fixed_realization_local_model` — `sorry`, node
  `new-lem-weil-pbc-lisse-finite-level-fixed-realization-local-model`.
- `exists_proetale_local_iso_section_of_fixed_realization_local_model` — `sorry`, node
  `new-lem-weil-pbc-lisse-finite-level-proetale-local-iso-descent`.

Thus one original sorry is closed and two strictly smaller proof obligations are added.

## No longer needed

Removed the public import of `Sheaf.AlgebraicGeometry.DerivedIsomSheafComparisonFromHom`;
the delivered route uses the derived morphism comparison API and the two split modules.
The original proof dependencies `lem-weil-pbc-derived-hom-sheaf-comparison-lisse`,
`lem-weil-pbc-derived-isom-comparison-from-hom`, and `thm-weil-pbc-site-comparison` are
not directly used by the Lean route and were removed from the item's node. The detailed
Hom comparison and equalizer construction therefore remain available to their own users
without being imported here.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan treated finite Hom comparison and inverse-pair equalizers as the
immediate route, but the item statement also requires transporting the supplied model
through `constantAdicQuotientRealization` and lifting a geometric point through a sieve.
Those are separate obligations in the delivered route, so they are represented by the
two new nodes rather than hidden inside an unfinished proof.

## New nodes

`new-lem-weil-pbc-lisse-finite-level-fixed-realization-local-model` records the local
fixed-realization transport from a model marking. `new-lem-weil-pbc-lisse-finite-level-proetale-local-iso-descent`
records geometric point lifting and descent of the inverse pair to the displayed Isom
presheaf section. Both nodes and their Lean modules are included in this delivery.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.LisseFiniteLevelFixedRealizationLocalModel": "b26593ab6b47a003b17a888c424f03a81028c772", "Sheaf.Paper.LisseFiniteLevelProEtaleLocalIsoDescent": "3eafc4b503d493833c874cfd2945e96859bd0aba", "Sheaf.Paper.LisseFiniteLevelProEtaleLocalIsoSections": "7fcfd4ffe25eaffe1c5a6b62461f9fadd41977cd"}, "results": {"Sheaf.Paper.LisseFiniteLevelEtaleLocalIsomorphisms": {"hash": "f8674c4dc52da453ee46e36207bde58015c17f03", "status": "OK"}}, "seconds": 12, "time": "2026-10-28T10:58:22+0800", "transitive": 0, "version": 1}
```

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
