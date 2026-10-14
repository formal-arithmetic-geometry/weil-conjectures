## What changed

Repair of broken tip 5bf94fe6cda6b904f1042bf7e0efe2a2724a39b7.
Added `public import Mathlib.Init` and two explanatory comments to
`lean/Sheaf/ConstructibleSheaf/TorsorEquivariantPresheafSheaf.lean`.
This makes command elaboration and axiom inspection available to the build's
importing probe. The canonical mathematical theorem remains in
`Sheaf.ConstructibleSheaf.TorsorEquivariantModuleIsSheaf`.

Both landed consumers are kept byte-for-byte identical to the fresh snapshot:
`TorsorInvariantSections.lean` and `TorsorSectionEvaluationBijective.lean`.
All existing statements, proofs, definitions, visibility, and docstrings are
preserved. Updated change record:
`coord/changes/retire-equivariant-sheaf-compatibility.md`.

## Proved and sorry left

Holes closed: none (0 of 0). Holes added: none. No split statements.
The three allowed Lean files contain no sorry or new declarations.

Checked each file separately using only
`python3 /home/ubuntu/weil-launcher/lcompile.py <file>` (60-second limit).
All final sources compile without errors or warnings.
Temporarily appended the existing stage-3 axiom/sorry probe to each file and
compiled each separately: SHEAF-PROBED counts 0, 1, and 1 respectively,
with no SHEAF-SORRY or SHEAF-AXIOM findings.
Also temporarily appended the exact global BATCH_PROBE to the retired file,
inspecting its imported Mathlib.Init module: SHEAF-PROBED Mathlib.Init 3,
with no sorry or forbidden-axiom findings. This checks the command APIs that
failed at the broken tip; it does not claim a global build was run.
The temporary tool probes emitted only their existing long-line style warning;
all probe text was removed before checking the final sources.

No multi-module build, server compile, delivery, push, .check file, or new
second-reading evidence was created.

## No longer needed

The public mathematical compatibility import remains retired. Both consumers
continue to import the canonical module directly. The historical module remains
outside the targets' import closure as in the landed delivery. No mathematical
proof dependency or DAG node is removed by this repair.

## Where the brief, the DAG or earlier work was wrong

The previous delivery treated a failed probe on a declaration-free module as
harmless. The global build requires the probe to run even for such a module:
its generated importer supplies no explicit Lean.Elab.Command import.
Removing every public import therefore caused `unknown namespace Command` and
`include import Lean.Elab.Command`. The public Mathlib.Init infrastructure
import repairs this omission without reinstating the retired theorem re-export.

The preserved module docstring's historical phrase "no declarations or imports"
predates this repair: it now has one infrastructure import and no declarations
or mathematical imports. Its text was preserved as requested.

## Forced adaptations

`Sheaf.ConstructibleSheaf.TorsorInvariantSections` was compiled from the repository version against the changed dependency and failed at line 78 with `lean.invalidField`: the environment no longer contains `AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf`. The delivered one-line import replacement to `TorsorEquivariantModuleIsSheaf` compiles and restores exactly that field.

`Sheaf.ConstructibleSheaf.TorsorSectionEvaluationBijective` was likewise compiled unchanged against the changed dependency and failed at line 69 with the same `lean.invalidField`. Its one-line import replacement is therefore forced and the adapted file compiles. No other lines in either unclaimed module changed.

## Second reading by XRb0cc22400e136910

1. **Repository comparison — PASS.** Compared all three delivered Lean files with the repository at the requested base and reviewed `delivery.diff`. The retired module changes only its import and explanatory comments; the two caller edits are the necessary direct-import replacements recorded in the change record. Existing declaration signatures, definitions, visibility, proof bodies, and target statements are unchanged.

2. **Compilation and forbidden constructs — PASS.** Compiled each touched Lean file separately with `/home/ubuntu/weil-launcher/lcompile.py`; all completed successfully within 60 seconds (0.5s, 5.6s, and 3.2s). The files contain no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definitions. The retired module has no mathematical declarations. The `Mathlib.Init` public import supplies the command elaboration needed by the stage-3 generated probe without restoring the retired theorem export.

3. **Mathematics and targets — PASS.** The canonical `AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf` theorem remains in `TorsorEquivariantModuleIsSheaf`; both callers now import that defining module directly and continue to use the same theorem and proof expressions. No theorem is weakened, strengthened, renamed, or duplicated, and no target route or unit statement changes. The change record identifies both forced adaptations and the original `lean.invalidField` failure.

4. **Pruning and import minimality — PASS.** Removing the historical mathematical re-export is the intended duplicate/interface retirement. `Mathlib.Init` is required only to make the global axiom/sorry probe elaborate on the declaration-free historical module; it introduces no project theorem dependency. The two caller imports are proof-only plain imports, while their public statement imports remain unchanged. No additional nodes or split statements are introduced.

5. **DAG, report, and probe consistency — PASS.** The report records zero holes closed, zero holes added, and no split-offs; the DAG continues to point at the retained canonical theorem. The stage-3 failure in the request is specifically addressed by the infrastructure import, and the touched source is free of workaround axioms or sorries. I changed only this second-reading section and added the required `.check` marker; no Lean source or mathematical content needed further repair.

## Forced adaptations

### Sheaf.ConstructibleSheaf.TorsorInvariantSections
Original against changed dependencies failed:
```
/tmp/forced-adaptation-pisyqtx7/lean/Sheaf/ConstructibleSheaf/TorsorInvariantSections.lean:78:6: error(lean.invalidField): Invalid field `equivariantModulePresheaf_isSheaf`: The environment does not contain `AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf`, so it is not possible to project the field `equivariantModulePresheaf_isSheaf` from an expression
  c
of type
  GaloisCover (ULift.{u + 1, u} P) V

(with the modules compiled into /tmp/forced-adaptation-pisyqtx7/.lbuild) [5.3 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.ConstructibleSheaf.TorsorSectionEvaluationBijective
Original against changed dependencies failed:
```
/tmp/forced-adaptation-ezn1zzal/lean/Sheaf/ConstructibleSheaf/TorsorSectionEvaluationBijective.lean:69:8: error(lean.invalidField): Invalid field `equivariantModulePresheaf_isSheaf`: The environment does not contain `AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf`, so it is not possible to project the field `equivariantModulePresheaf_isSheaf` from an expression
  c
of type
  GaloisCover (ULift.{u + 1, u} P) V

(with the modules compiled into /tmp/forced-adaptation-ezn1zzal/.lbuild) [2.6 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
