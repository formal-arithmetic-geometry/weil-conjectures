# AlgebraicGeometry.relativeMV_direct_image_rows

## Reason

Restore the module assigned by `coord/rework.tsv` from
`quarantine/Sheaf/AlgebraicGeometry/RelativeMVDirectImageRows.lean`.
The live Lean path is absent after the cluster restore. The archived parent
`RelativeMVDirectImageHomotopyComparison` imports and applies it, and that
parent's DAG proof still cites this node: the item remains needed.

The current row-core theorem already supplies the two short exact rows, all
six vertex comparisons, and all three normalized mate equations. Applying
the inverse adjunction equivalence and cancelling a target isomorphism proves
each desired equation directly. Three intermediate wrappers are unnecessary.

## Old

The live path `lean/Sheaf/AlgebraicGeometry/RelativeMVDirectImageRows.lean`
is absent. The archived import block is:

```lean
public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
import Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsPreoverlap
import Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsOverlapMate
```

Its archived theorem proof is:

```lean
  classical
  dsimp only
  have hrows := relativeMV_direct_image_rows_preoverlap f f' g g' hpull K K' φ U V hcover
  rcases hrows with ⟨P, P', m, e₁, e₂, e₃, e₁', e₂', e₃', hdata⟩
  have hP := hdata.1
  have hP' := hdata.2.1
  have h₁ := hdata.2.2.1
  have h₂ := hdata.the project server
  have h₃ := hdata.the project server
  refine ⟨P, P', m, e₁, e₂, e₃, e₁', e₂', e₃', hP, hP', h₁, h₂, ?_⟩
  exact relativeMV_direct_image_rows_overlap_mate f f' g g' hpull K K' φ U V
    P P' m e₃ e₃' h₃

```

## New

The complete public signature, visibility, universe parameters and docstring
are restored byte-identically. A direct comparison verifies that the signature
equals the existing node's `lean.statement`. Only the private proof imports
and theorem proof differ from the archive:

```lean
public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
import Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsCore
```

```lean
  classical
  dsimp only
  obtain ⟨P, P', m, e₁, e₂, e₃, e₁', e₂', e₃', hα, hβ, hγ, hP, hP'⟩ :=
    relativeMV_direct_image_rows_core f f' g g' hpull K K' φ U V hcover
  refine ⟨P, P', m, e₁, e₂, e₃, e₁', e₂', e₃', hP, hP', ?_, ?_, ?_⟩
  · rw [hα, Equiv.symm_apply_apply]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · rw [hβ, Equiv.symm_apply_apply]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · rw [hγ, Equiv.symm_apply_apply]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

```

The existing node's proof, proof dependencies and proof origin now record the
core theorem followed by elementary cancellation. Its statement, Lean
attachment and unit route are unchanged. No definition or target changes.
The module has zero holes before and after restoration.

The restored module compiled cleanly against the published server build in
8.0 seconds. In a separate validation sandbox, the final module and its
byte-identical archived direct consumer compiled in 8.5 and 30.2 seconds.
Both declarations' `#print axioms` lists contain exactly `propext`,
`Classical.choice` and `Quot.sound`. All compilation used `lcompile.py`.

## Users

`tools/downstream.py` reports the module unknown because its live source is
absent. A source search of both `lean/` and `quarantine/` finds the single
direct consumer below. Its node retains this node in `proof_deps` and in the
first proof step's `uses`. It receives identical row witnesses, exactness and
three mate identities. No consumer adaptation is needed. The wrapper modules
remain in the library and their declarations are not changed or withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RelativeMVDirectImageRows | J1 (assigned rework) | Restore interface; shorten proof by using the existing row-core directly. |
| Sheaf.AlgebraicGeometry.RelativeMVDirectImageHomotopyComparison | unclaimed in shared snapshot (quarantined) | Identical public interface; original consumer requires no changes. |

## Status

landed 20261021T021916-L-2791844 2026-10-21 (merge of deliver/J1/Sheaf.AlgebraicGeometry.RelativeMVDirectImageRows)
