# Local tensor-product instance for the affine comparison proof

## Reason

The proof needs Mathlib's canonical right-factor algebra to construct scalar
towers for first-factor localization. The static preflight treats the added
local attribute command as an interface change and requires this record.

## Old

No command activating `Algebra.TensorProduct.rightAlgebra` as a local instance
appeared in `Sheaf.Algebra.Homology.AffineDirectLocalizedTensorSquareCore`.
The original theorem was `AlgebraicGeometry.affineDirectLocalizedTensorSquare_core`
with proof `:= by sorry`; its signature is preserved verbatim in this delivery.

## New

```lean
attribute [local instance] Algebra.TensorProduct.rightAlgebra
```

The attribute is local to the item module. It introduces no new global instance
and changes no existing definition, statement, visibility, or target meaning.
All added helpers in the item are private and proved; proof imports are non-public.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AffineDirectLocalizedTensorSquareCore | H4 | Local instance is available to construct proof scalar towers. |
| Sheaf.Algebra.Homology.AffineDirectLocalizedTensorSquare | unclaimed in this checkout | No effect: local attribute; unchanged imported theorem signature. |

The named external user is the sole direct importer in this checkout. All transitive
importers likewise see the unchanged interface.

No module outside the item is edited or requires adaptation. No definition used
by a target is changed, so no target statement review is reopened by this command.

## Status

landed 20261014T022545-L-4045719 2026-10-14 (merge of deliver/H4/Sheaf.Algebra.Homology.AffineDirectLocalizedTensorSquareCore)

Both delivered modules and their declaration probes compiled in the dry run.
Independent review should confirm that the attribute is local and the existing
public interface is unchanged. The new public result and its one remaining proof
hole have a separate module and matching DAG node.
