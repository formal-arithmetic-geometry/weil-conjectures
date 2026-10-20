# AlgebraicGeometry.ProjectiveLine.Line_isIso

## Reason

Restore the quarantined zero-hole module after the upstream sync. This repair retry
re-reads the current quarantined source and reapplies the changes after the return of
`91017ab2b0` for a stale delivery base (`e0d550965`). The current live path is absent;
`coord/rework.tsv` still records the original quarantined module. The old proof refers
to the upstream private helper `subsingleton_ne_zero`, which is inaccessible across
module boundaries. The canonical upstream module already exports an instance with the
identical proposition, so instance synthesis proves the existing named instance.

The extraction also left ten dangling `variable (S) in` commands around an empty
Frobenius section. These produce redundant binder annotation and scope errors. Remove
the dangling commands and empty section. Remove three redundant public imports: the
retained canonical Line import re-exports all three. Wrap the generated provenance
comment to the required width. No target statement or definition changes its meaning,
no source-library file changes, and no declaration is removed.

## Old

From the quarantine file recorded in `coord/rework.tsv`; imports, instance and trailing
scope commands verbatim:

```lean
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.AlgebraicGeometry.Frobenius
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearProjection
public import WeilConjectures.Mathlib.FieldTheory.Finite.Polynomial

instance Line_isIso : IsIso (AffineSpace.reindex (fun _ : {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} ↦
    PUnit.unit.{u + 1}) S) := by
  have := subsingleton_ne_zero.{u}
  refine ⟨AffineSpace.reindex (fun _ ↦ ⟨⟨1⟩, by simp⟩) S, ?_, ?_⟩ <;>
    refine AffineSpace.hom_ext (by simp [AffineSpace.reindex_over]) fun i ↦ ?_ <;>
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord,
      AffineSpace.reindex_appTop_coord, Scheme.Hom.id_appTop, CommRingCat.id_apply]
  exact congrArg _ (Subsingleton.elim _ _)

variable (S) in
variable (S) in
variable (S) in
variable (S) in
variable (S) in
variable (S) in
variable (S) in
variable (S) in
variable (S) in
variable (S) in
section Frobenius

variable (F : Type u) [Field F] [Finite F]
  {Φ : ProjectiveLine (Spec (.of F)) ⟶ ProjectiveLine (Spec (.of F))}

end Frobenius
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line

instance Line_isIso : IsIso (AffineSpace.reindex (fun _ : {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} ↦
    PUnit.unit.{u + 1}) S) := by
  -- Reuse the upstream isomorphism instance for this exact map over the arbitrary base S.
  infer_instance
```

The instance name, implicit scheme parameter, universe, type and instance registration
are unchanged. `IsIso` is a proposition; replacing its proof has no data-level effect.
The removed imports remain transitively public through the retained Line module.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line` | U9 | Restored with a compiling proof and balanced scopes; no statement change. |

`tools/downstream.py Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
--uses Line_isIso` reports an unknown module because its live source is quarantined.
A literal import search in both `lean/` and `quarantine/` finds no consumer of this
module. A declaration-name search in both trees finds `Line_isIso` only at its
quarantined declaration. Consequently no consumer adaptations are necessary. The
underlying projective-line constructions, and the blueprint node `sk-d-lines` and unit
`sk-d-lines`, remain supplied by the unchanged upstream module. No DAG attachment
names this extracted instance module, so there is no node update.

The current quarantine source was restored afresh and compiled on this retry: it
failed with the private identifier and dangling-scope errors in 2.1 seconds. The
repaired copy then compiled without warnings in 2.0 seconds. The archive remains
untouched. The current source search finds no Lean importer, declaration consumer
or DAG attachment requiring adaptation.

## Status

landed 20261020T145544-L-2411327 2026-10-20 (merge of deliver/U9/Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line)
