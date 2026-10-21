# AlgebraicGeometry.Scheme.picard_derived_fibre_residue_model_data proof dependencies

## Reason

The assigned rework row records the earlier post-restoration global-build failure.
The current source already includes N4's explicit-universe repair and compiles
unchanged in 19.4 seconds. Preserve that restoration and its complete theorem.

The proof unnecessarily depends on `exists_tensorPullbackAdjunction`, whose
extra conclusion fixes the unit sectionwise. The only fact used is that tensor
pullback is a left adjoint. `TensorPullback` already proves
`nonempty_tensorPullbackAdjunction`. Use it in a proved private helper and use
that helper at the three coefficient pullbacks. Remove the resulting unused
private import of `TensorPullbackAdjunction` and the redundant private
`Mathlib.AlgebraicGeometry.AffineScheme` import. The revised module compiles in
11.4 seconds; these are individual observed timings, not a performance guarantee.

No public declaration, definition, instance, attribute, public import or target
statement changes. No target definition review is reopened. The existing node's
first proof step and proof origin are updated to record the actual adjunction
used; its dependencies, Lean attachment and mathematical statement are retained.

## Old

Private proof imports:

```lean
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Mathlib.AlgebraicGeometry.AffineScheme
```

The source coefficient proof uses:

```lean
    let e := (Classical.choose
      (Modules.exists_tensorPullbackAdjunction (pullback.fst f k))).leftAdjointUniq
        (Modules.pullbackPushforwardAdjunction (pullback.fst f k))
    letI : Modules.IsInvertible G := Modules.IsInvertible.of_iso (e.app L).symm
```

The target coefficient proof uses:

```lean
    let e := (Classical.choose
      (Modules.exists_tensorPullbackAdjunction (ui i))).leftAdjointUniq
        (Modules.pullbackPushforwardAdjunction (ui i))
    letI : Modules.IsInvertible ((Modules.tensorPullback (ui i)).obj L) :=
      Modules.IsInvertible.of_iso (e.app L).symm
    let N := (Modules.tensorPullback (ui i)).obj L
    let e' := (Classical.choose
      (Modules.exists_tensorPullbackAdjunction (pullback.fst (fi i) k))).leftAdjointUniq
        (Modules.pullbackPushforwardAdjunction (pullback.fst (fi i) k))
    have hM : Modules.IsInvertible M :=
      Modules.IsInvertible.of_iso (e'.app N).symm
    letI : Modules.IsInvertible M := hM
```

## New

Remove the two private imports and prove:

```lean
private theorem tensorPullback_invertible_local {X Y : Scheme.{v}} (g : X ⟶ Y)
    (M : Y.Modules) [M.IsInvertible] : ((Modules.tensorPullback g).obj M).IsInvertible := by
  obtain ⟨adj⟩ := Modules.nonempty_tensorPullbackAdjunction g
  exact Modules.IsInvertible.of_iso
    ((adj.leftAdjointUniq (Modules.pullbackPushforwardAdjunction g)).app M).symm
```

Use `tensorPullback_invertible_local _ _` for the source coefficient and both
successive target coefficient pullbacks. All other proof steps and all public
signatures remain identical. Both removed imports remain reachable transitively
through retained dependencies; no whole-module closure pruning is claimed.

## Users

`tools/downstream.py` reports no live importers and finds only the theorem's own
source use. An explicit import scan of `lean/` and `quarantine/`, with live
sources overriding archives, finds two direct and twenty transitive consumers.
The following complete table preserves the existing quarantine-aware review.
The public theorem signature and public import list were compared byte-for-byte
with the current live source. No consumer needs adaptation. The two direct
archived consumers compile unchanged in a separate scratch compilation set:
`PicardDerivedFibreResidueBridgeCore` in 19.5 seconds and
`PicardDerivedFibreResidueBridge` in 53.4 seconds, after the revised root module
compiled in 13.8 seconds. No consumer edit is included.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed in shared snapshot | Transitive archived consumer; unchanged meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed in shared snapshot | Transitive archived consumer; unchanged meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreNaturality | unclaimed in shared snapshot | Transitive archived consumer; unchanged meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueBridge | unclaimed in shared snapshot | Direct archived consumer; unchanged statement and import visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueBridgeCore | unclaimed in shared snapshot | Direct archived consumer; unchanged statement and import visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed in shared snapshot | Transitive archived consumer; unchanged meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed in shared snapshot | Transitive archived consumer; unchanged meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed in shared snapshot | Transitive archived consumer; unchanged meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | unclaimed in shared snapshot | Transitive archived consumer; unchanged meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed in shared snapshot | Transitive archived consumer; unchanged meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed in shared snapshot | Transitive archived consumer; unchanged meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed in shared snapshot | Transitive archived consumer; unchanged meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed in shared snapshot | Transitive archived consumer; unchanged meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed in shared snapshot | Transitive archived consumer; unchanged meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed in shared snapshot | Transitive archived consumer; unchanged meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed in shared snapshot | Transitive archived consumer; unchanged meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparison | unclaimed in shared snapshot | Transitive archived consumer; unchanged meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonSource | unclaimed in shared snapshot | Transitive archived consumer; unchanged meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonTargets | unclaimed in shared snapshot | Transitive archived consumer; unchanged meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologySourceResidueComparison | unclaimed in shared snapshot | Transitive archived consumer; unchanged meaning; no adaptation. |

## Status

landed 20261021T233644-L-844410 2026-10-21 (merge of deliver/E4/Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueModelData)
