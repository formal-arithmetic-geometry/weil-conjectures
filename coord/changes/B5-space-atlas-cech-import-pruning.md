# AlgebraicGeometry.AlgebraicSpace.space_atlas_base_change_cech_geometry

## Reason

The atlas geometry and overlap naturality need no cotangent-ring construction.
Remove its unused public import from the item. Both public theorem signatures,
all existing definitions, instances, and attributes stay identical. The new
private imports provide the residue-field morphism and Spec full faithfulness
used by the proof. The redundant private joint-surjectivity import is already
provided publicly by AlgebraicSpaceFibreProductsEtaleCovers.

## Old

```lean
public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
```

## New

```lean
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SpaceAtlasBaseChangeCechGeometry | B5 | Two complete proofs; public signatures unchanged. |

A source search of lean/ found no direct importers of the item. No other existing
module is changed or needs adaptation. DAG parents retain the item and its exact
statements. The fibre-product node remains a statement dependency and its module
remains publicly imported; this delivery withdraws no module or declaration.

The unused-variable linter is disabled only for the naturality theorem, whose
fixed public interface contains geometric hypotheses that its categorical proof
does not need. No elaboration, transparency, or kernel-checking option is changed.

## Status

landed 20261026T091146-L-3315779 2026-10-26 (merge of deliver/B5/Sheaf.AlgebraicGeometry.SpaceAtlasBaseChangeCechGeometry)
