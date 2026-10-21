# AlgebraicGeometry.relativeMV_direct_image_rows_preoverlap

## Reason

Restore the missing module assigned by `coord/rework.tsv`. Its preserved
source is
`quarantine/Sheaf/AlgebraicGeometry/RelativeMVDirectImageRowsPreoverlap.lean`.
The row records a cluster-restore rollback, not a mathematical withdrawal.
The current row-core and mate dependencies are available and proved.

## Old

The live path
`lean/Sheaf/AlgebraicGeometry/RelativeMVDirectImageRowsPreoverlap.lean`
is absent. The archived import block is:

```lean
public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
import Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsCore
import Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsMates
```

The archived proof is:

```lean
  classical
  dsimp only
  obtain ⟨P, P', m, e₁, e₂, e₃, e₁', e₂', e₃', hα, hβ, hγ, hdata⟩ :=
    relativeMV_direct_image_rows_core f f' g g' hpull K K' φ U V hcover
  have hP := hdata.1
  have hP' := hdata.2
  have hm := relativeMV_direct_image_rows_mates f f' g g' hpull K K' φ U V
    P P' m e₁ e₂ e₃ e₁' e₂' e₃' hα hβ hγ
  rcases hm with ⟨h₁, h₂, h₃⟩
  exact ⟨P, P', m, e₁, e₂, e₃, e₁', e₂', e₃', hP, hP', h₁, h₂, h₃⟩
```

## New

Restore the complete archived file verbatim, including the imports and proof
above. The public theorem's entire signature, its visibility and its
docstring stay byte-identical. No definition, hypothesis or conclusion
changes. The node's Lean attachment and proof dependencies are preserved.
Zero holes are closed or added; zero remain in this module.

The restored item compiled cleanly in 7.4 seconds, and the original archived
direct consumer compiled unchanged in 6.1 seconds. Both were compiled in
one scratch validation sandbox to use the restored source consistently.
Both axiom lists contain only `propext`, `Classical.choice` and `Quot.sound`.
No source-library declaration is modified or removed.

## Users

The source search includes both `lean/` and `quarantine/`, and the parent
node's `proof_deps` and proof-step `uses` were checked. The sole direct
consumer is the archived module below; it compiles unchanged against the
restored theorem. Indirect consumers receive the same public interface.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsPreoverlap | B4 (assigned rework) | Restore the complete module with identical interface and proof. |
| Sheaf.AlgebraicGeometry.RelativeMVDirectImageRows | unclaimed in shared snapshot (quarantined) | Same theorem signature and witnesses; original consumer compiles unchanged. |

## Status

landed 20261021T020057-L-2582139 2026-10-21 (merge of deliver/B4/Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsPreoverlap)
