# AlgebraicGeometry.VectorBundleZeroSection.antiEquivalence

## Reason

Restore the module quarantined by the 2026-10-20 upstream sync. Its public exposed
`antiEquivalence` and `algebraIso` definitions use `affine_morphism_relative_spec` as data.
A private import does not make that theorem available in their exposed bodies. Compiling
the archive reproduced the unknown-identifier errors at lines 55 and 126. A public import
of its source module fixes both errors without changing any declaration.

## Old

```lean
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
```

The import moves into the public-import block. All declaration signatures, definition
bodies, theorem proofs, attributes and docstrings are verbatim from the archive.

## Users

`tools/downstream.py --allow-missing` has no live users because this module and its
consumers were quarantined. The table additionally includes every archived source that
mentions `VectorBundleZeroSection`; it therefore includes the direct archived importers.
No consumer requires adaptation: the only interface change adds import visibility.
Quarantined consumers remain assigned to their own restoration items.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConormalConeZeroSectionPullback | unclaimed in shared snapshot | declarations unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ReesConeNormalization | unclaimed in shared snapshot | declarations unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.VectorBundleIntegration | unclaimed in shared snapshot | declarations unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.VectorIntegrationMate | unclaimed in shared snapshot | declarations unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.VectorProjectiveCompletion | unclaimed in shared snapshot | declarations unchanged; no adaptation |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed in shared snapshot | declarations unchanged; no adaptation |
| Sheaf.Paper.FiniteRingSectionDeformation | unclaimed in shared snapshot | declarations unchanged; no adaptation |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed in shared snapshot | declarations unchanged; no adaptation |
| Sheaf.Paper.FiniteSmoothCanonicalInterfaces | unclaimed in shared snapshot | declarations unchanged; no adaptation |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed in shared snapshot | declarations unchanged; no adaptation |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed in shared snapshot | declarations unchanged; no adaptation |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | unclaimed in shared snapshot | declarations unchanged; no adaptation |
| Sheaf.Paper.PurityNormalBundle | unclaimed in shared snapshot | declarations unchanged; no adaptation |
| Sheaf.Paper.PurityNormalCone | unclaimed in shared snapshot | declarations unchanged; no adaptation |
| Sheaf.Paper.PurityRegularSection | unclaimed in shared snapshot | declarations unchanged; no adaptation |
| Sheaf.Paper.PurityVectorBundleZeroSection | unclaimed in shared snapshot | declarations unchanged; no adaptation |
| Sheaf.Paper.VectorBundlePurity | unclaimed in shared snapshot | declarations unchanged; no adaptation |
| Sheaf.Paper.VectorBundleThomClass | unclaimed in shared snapshot | declarations unchanged; no adaptation |
| Sheaf.Paper.VectorPurityBaseChange | unclaimed in shared snapshot | declarations unchanged; no adaptation |
| Sheaf.Paper.VectorPurityDirectSum | unclaimed in shared snapshot | declarations unchanged; no adaptation |
| Sheaf.Paper.VectorPurityFiniteReduction | unclaimed in shared snapshot | declarations unchanged; no adaptation |
| Sheaf.Paper.VectorPurityNormalization | unclaimed in shared snapshot | declarations unchanged; no adaptation |
| Sheaf.Targets.VectorBundlePurity | unclaimed in shared snapshot | declarations unchanged; no adaptation |

No target statement or definition changes meaning. In particular the choice of the
relative-spectrum equivalence, augmentation, zero section and coordinates is unchanged,
including rank zero and the empty base. No source-library declaration is edited.

## Status

landed 20261020T145506-L-2401447 2026-10-20 (merge of deliver/F3/Sheaf.AlgebraicGeometry.VectorBundleZeroSection)
