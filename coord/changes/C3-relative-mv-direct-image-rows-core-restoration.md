# AlgebraicGeometry.relativeMV_direct_image_rows_core

## Reason

Restore the missing module specified by `coord/rework.tsv`, preserved at
`quarantine/Sheaf/AlgebraicGeometry/RelativeMVDirectImageRowsCore.lean` after
a failed cluster restore. The archive already has a complete zero-hole proof.
Its row-roof and generic strictification dependencies are available.

## Old

The live path
`lean/Sheaf/AlgebraicGeometry/RelativeMVDirectImageRowsCore.lean` is absent.
The archived import block is:

```lean
public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
import Sheaf.AlgebraicGeometry.RelativeMVHomotopyPullback
import Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowRoof
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisUnderivedOpenCounitSquare
import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisPresentation
import WeilConjectures.AlgebraicGeometry.RingedSpaceDirectImageKInjectiveAcyclic
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
```

## New

Restore the archived module, preserving the public declaration's entire
signature, its proof and docstring, and the private helper verbatim. The
only change to the archived text is the import block:

```lean
public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
import Sheaf.AlgebraicGeometry.RelativeMVHomotopyPullback
import Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowRoof
```

The four removed private imports are unused by this proof. Both public
imports and the two directly used proof dependencies remain. The proof
strictifies the normalized row roof and transports the three equations by
adjunction naturality. No hypothesis, conclusion, definition, source-library
declaration or target changes. Zero holes are closed or added.

The item compiled without errors or warnings in 13.7 seconds. Its original
archived direct consumer compiled unchanged in 5.3 seconds. The theorem's
axiom list contains only `propext`, `Classical.choice` and `Quot.sound`.
The current row-roof source was recompiled unchanged to avoid its published
stale compiled import; it contributes no delivery diff. Scratch validation
files and archives are not changed or withdrawn.

## Users

The direct source search includes both `lean/` and `quarantine/`, preserving
parents whose proofs are still awaiting restoration. The sole direct
archived consumer below applies the theorem with exactly the same arguments,
witnesses and equations and compiles unchanged. Indirect consumers receive
the identical public interface. No consumer adaptation is needed and no
DAG dependency or attachment is removed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsCore | C3 (assigned rework) | Restore complete module with identical public interface. |
| Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsPreoverlap | unclaimed in shared snapshot (quarantined) | Original consumer compiles unchanged. |

## Status

landed 20261021T013812-L-2338010 2026-10-21 (merge of deliver/C3/Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsCore)
