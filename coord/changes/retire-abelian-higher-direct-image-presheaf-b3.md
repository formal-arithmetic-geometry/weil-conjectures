# Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf

## Reason

Complete the worker retirement listed in coord/retire-items.tsv under the human's
handoff in coord/changes/retire-sheaf-twins-20261020.md. D2 already replaced the
duplicate declarations by a public upstream re-export and repointed node
sbc-lem-higher-direct-image-presheaf. The remaining task is to redirect the three
active consumers and withdraw the declaration-free shim. All three consumers are
unclaimed at the time of this delivery. No source-library file is changed.

## Old

The item contains only the following public import, module documentation and an
empty public section; it declares no constants:

```lean
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
```

Each of the three consumers has this private proof import:

```lean
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
```

## New

The item is withdrawn through deleted.txt. Each consumer imports the same upstream
provider directly:

```lean
import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
```

Every other byte of each consumer is preserved. The module's upstream re-export
already made exactly these declarations available to each private importer, so the
replacement preserves both the mathematical API and public visibility. This holds
without restrictions on schemes, sheaves or cohomological degree. No target changes
meaning. The canonical comparison constructions and their proved properties stay
upstream. The existing node attachment and dependency edges require no change.

## Users

tools/downstream.py finds exactly these three active downstream modules; direct
import scanning agrees. Claim records show no holder for any of them.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CommutativeExchangeChart | unclaimed | Replace private import, no other edit. |
| Sheaf.AlgebraicGeometry.EtaleHigherDirectImageStalkCriterion | unclaimed | Replace private import, preserve complete proof. |
| Sheaf.AlgebraicGeometry.RelativeHigherDirectImageContinuity | unclaimed | Replace private import, no other edit. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology | unclaimed; quarantined | Archive preserved; migrate import when restoring. |
| Sheaf.AlgebraicGeometry.PrimeCurveArtinSchreierKernel | unclaimed; quarantined | Archive preserved; migrate import when restoring. |
| Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages | unclaimed; quarantined | Archive preserved; migrate import when restoring. |
| Sheaf.Paper.PurityRelativeKummer | unclaimed; quarantined | Archive preserved; migrate import when restoring. |

The four archived users do not enter the current library import graph. Nothing in
their nodes is withdrawn: their dependency still resolves to the existing upstream
theorem. No quarantined source is deleted or replaced by an empty module.

## Status

landed 20261020T155156-L-3204382 2026-10-20 (merge of deliver/B3/Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf)
