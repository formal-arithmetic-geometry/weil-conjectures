# AlgebraicGeometry.ProjectiveLine.Charts_isIso

## Reason

Repair the returned delivery against the current quarantined source, listed in
`coord/rework.tsv`. The live path is absent. Empty scoped commands cause redundant
binder errors and unbalanced sections; the extracted instance also refers to
upstream's private `subsingleton_ne_one`. The current upstream Charts module
already proves the identical `IsIso` instance. Remove empty extracted context and
reuse that instance via `infer_instance`. Preserve all current public imports.
No source-library file changes.

## Old

The current quarantined declaration as intended in namespace
`AlgebraicGeometry.ProjectiveLine`, with `(S : Scheme.{u})`:

```lean
instance Charts_isIso : IsIso (AffineSpace.reindex (fun _ : {j : ULift.{u} (Fin 2) // j ≠ ⟨1⟩} ↦
    PUnit.unit.{u + 1}) S) := by
  have := subsingleton_ne_one.{u}
  refine ⟨AffineSpace.reindex (fun _ ↦ ⟨⟨0⟩, by simp⟩) S, ?_, ?_⟩ <;>
    refine AffineSpace.hom_ext (by simp [AffineSpace.reindex_over]) fun i ↦ ?_ <;>
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord,
      AffineSpace.reindex_appTop_coord, Scheme.Hom.id_appTop, CommRingCat.id_apply]
  exact congrArg _ (Subsingleton.elim _ _)
```

The original does not elaborate: dangling `variable {n S} in` and scoped
`set_option` commands before `end Sections` cause cascading section errors and
incorrectly leave the declaration inside `AlgebraicGeometry.ProjectiveSpace`.
There is no successfully compiled alternative signature from that broken scope.
The current original failure was reproduced with lcompile.py during this retry
after return of head `b6fa9a111c` (base `e0d550965`). The original archive was
read again and copied into the sandbox before reapplying the substantive repair.

## New

In namespace `AlgebraicGeometry.ProjectiveLine`, with the same universe and binder:

```lean
instance Charts_isIso : IsIso (AffineSpace.reindex (fun _ : {j : ULift.{u} (Fin 2) // j ≠ ⟨1⟩} ↦
    PUnit.unit.{u + 1}) S) := by
  infer_instance
```

Keep all five public imports of the current quarantined source. Remove only the
empty extracted scoped context and unused opens; preserve module documentation,
wrap its provenance comment, and document the compatibility instance. No public imports are removed. The repaired module compiles
cleanly through lcompile.py.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts | U7 | Restore compilation; same intended named instance and type. |

No live or quarantined Lean source imports this extracted module or mentions
`Charts_isIso`, apart from the defining quarantined file. All DAG nodes were
searched; none attaches this module or references this declaration. No consumer
adaptations or node changes are needed. The upstream Charts module and all of
its consumers keep their declarations unchanged.

## Status

landed 20261020T145543-L-2410944 2026-10-20 (merge of deliver/U7/Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts)
