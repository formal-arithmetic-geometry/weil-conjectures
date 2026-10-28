## What changed

Withdrew the false split `reductionTower_components_augmentation` through
`deleted.txt`, retained its DAG node with a null Lean attachment, and replaced
its only caller's proof. The statement of
`WeilConjectures.IntegralHom.reductionTower_components` and its module
`Sheaf.Paper.IntegralHomReductionTowerComponents`' public import are unchanged.

The replacement obtains two separate unit-normalized tensor models. It constructs
one signed chain comparison, proves its quotient components invertible using the
existing two-term free criterion, localizes, inverts and conjugates. Naturality
of this isomorphism gives the transition equation. Naturality at the coefficient
unit, with the two separate model augmentation equations, gives the augmentation
equation for that same family after cancellation of invertible components.
A proved private helper isolates the elementary naturality calculation.

Added `Sheaf.Paper.IntegralHomReductionTowerUnitModels`, with the missing
representation step as `reductionTower_unit_models`. It records separate
models and their units, and normalizes the signed map only at R[0]. It does
not assert an isomorphism between the two modeled quotient towers, or the
invertibility of a signed map at any Q_n. The parent proves those parts.
This is a strictly lower representation obligation, not the original universal
augmentation assertion with its hypotheses repackaged.

Validation: the current new model module, parent and unchanged direct consumer
`Sheaf.Paper.IntegralHomAugmentedTowerComparison` compiled cleanly in import
order through `lcompile.py` (8.9 s, 13.0 s and 7.6 s). The temporary unchanged
consumer copy was removed from the packet after this check.

The older tensor-model module is held by H1 on the current server; it and the
transition module are unchanged. No source-library declaration, target statement,
definition, instance, attribute or unit route changes.

## Proved and sorry left

The false original hole
`WeilConjectures.IntegralHom.reductionTower_components_augmentation`
(node `lem-sf-integral-hom-tower-components-augmentation`) is withdrawn, not proved.
Thus 0 of the item's original 1 holes are proved as stated.

`WeilConjectures.IntegralHom.reductionTower_components` has a complete replacement
Lean proof of its unchanged statement from the named lower declarations. Its
private `augmentation_of_unit` helper is completely proved.

One new hole remains, and its entire proof is `:= by sorry`:
`WeilConjectures.IntegralHom.reductionTower_unit_models`
(node `lem-sf-integral-hom-tower-unit-models`). Its docstring and node give the
actual coefficient tower, the unit cone, the K-flat/K-injective calculations,
the resolution transport and the signed degree-zero unitor calculation.
There are no other holes in the delivered Lean sources. This is a correction
and decomposition, not a claim of a completed proof or a net proved-hole gain.

## No longer needed

The parent removes its proof imports of:

- `Sheaf.Paper.IntegralHomReductionTowerAugmentation`, withdrawn because its
  universal assertion is false; its node is retained and no longer cited.
- `Sheaf.Paper.IntegralHomReductionTowerTransition`, whose transition-only
  comparison does not provide the normalization needed for the augmentation.

A source import-closure calculation from `TargetsCheck`, comparing the shared
sources with this packet, prunes exactly these three existing modules:
`IntegralHomReductionTowerAugmentation`, `IntegralHomReductionTowerTransition`
and `IntegralHomReductionTowerTensorModels` (all under `Sheaf.Paper`). The last
two files are retained unchanged, including the tensor-model group's work.
Their nodes `lem-sf-integral-hom-tower-components-transition` and
`lem-sf-integral-hom-tower-tensor-models` are not needed by the replacement parent.

The false split's planned dependencies `lem-sf-integral-hom-models-exist` and
`lem-sf-integral-hom-comparison-is-iso` are not used here: they give finite-level
statements, without the common natural comparison and its unit normalization.
They remain available for other consumers. Resolution independence remains
needed in the new representation lemma; it is not pruned.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the original assertion quantifies over every
transition-compatible family independently of its fixed apex isomorphism e.
Negating such a family preserves all transition equations but changes the
augmentation. For ell=3, E=Q_3 and a nonempty pro-etale site, take the coefficient
unit in degree zero and its identity resolutions. The usual Hom-unit
identification gives a compatible family whose augmentation at the first
quotient sends 1 to 1. Its negative sends 1 to -1 in the nonzero residue field
of characteristic 3. They cannot both equal the same fixed augmentation.
The parent only needs one family constructed with its normalization.

The previous separate tensor-model statement omits unit information even though
its natural-language construction mentions it. Arbitrary model isomorphisms
cannot supply that information. The new lower statement retains the unit in
the model construction; the parent proves the resulting comparison and both
squares together, instead of applying an invalid universal augmentation lemma.
The current server claim records were checked before deciding to leave the
H1-held model module unchanged. The unit's finite-free coefficient route is kept.

## New nodes

`lem-sf-integral-hom-tower-unit-models` is the one new node. It supplies the
separate coefficient tensor models, the degree-zero unit cone, their separate
augmentation equations and their normalization at R[0]. It has one hole and
makes no quotient-level comparison or invertibility assertion. The existing
signed comparison and degreewise invertibility declarations supply those
strictly separate parts of the argument in the parent.

Change record: `coord/changes/U8-integral-hom-augmentation-normalization.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralHomReductionTowerAugmentation": "fdd6fd89e33daef28207b2d920705ea5b4231ed8", "Sheaf.Paper.IntegralHomReductionTowerComponents": "37709d81caf0944ff4db4a8376204b76b0991557", "Sheaf.Paper.IntegralHomReductionTowerUnitModels": "e0eb68f14447147d099e953fcf3a79f1624c23dc"}, "results": {"Sheaf.Paper.IntegralHomAugmentedTowerComparison": {"hash": "b5ff6f5fbe78a46ff2f094fa4d9ff1572c1db394", "status": "OK"}}, "seconds": 11, "time": "2026-10-28T10:36:40+0800", "transitive": 0, "version": 1}
```

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
