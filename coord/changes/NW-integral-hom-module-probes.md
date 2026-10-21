## Maintenance repair: use module-mode compiler probes (2026-10-21 UTC)

The previous BLOCKED reports came from scratch files missing `module`. A bare
`import Sheaf.Paper.IntegralHomReduction` loads conflicting private proof imports
and reports the duplicate `CochainComplex.isKFlat_of_boundedAbove_flat`. This
does not reproduce the environment of the stage-2 module you must deliver.

Start every scratch probe and delivery file with `module` as its first Lean
command. Keep statement-dependency imports public and proof-dependency imports
plain, as required by the stage rules. For example, this probe compiles against
the current published library and resolves the required theorem:

```lean
module

import Sheaf.Paper.IntegralHomReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

@[expose] public section

#check WeilConjectures.integralHomReduction
```

Maintenance verified all eight recorded statement-dependency imports together
with every recorded proof-dependency import and their recorded declarations.
Both `tools/lean_file.sh` (one file, 60 seconds) and the prescribed `scompile.py`
pass. The full probe is retained at `scratchpad/RequiredImports.lean` in this
item's sandbox; `scratchpad/Probe2.lean` and `scratchpad/Checks.lean` now also use
module mode, with their original contents saved in `.NW-maint-1792598210.bak`.

Read the maintenance correction at the end of the retained `report.md`, then
continue the original stage-2 statement work. The old report's assertion that
published-source edits are necessary is superseded by these successful checks.
Keep the mandatory proof dependencies, including `IntegralHomReduction`; the
models-only module does not replace its theorem. There is no need to wait for a
new published build or change the item's mathematics to resolve this failure.
Remove diagnostic `#check` lines from the final delivery. Use `scompile.py` for
worker compilations, then the normal dry run and delivery.


Server validation (2026-10-21 UTC): the live published tree was used without
changing any library source or artifact. Bare `Clash.lean` reproduces the original
duplicate in 2.3 s. `ModuleClash.lean` passes in 2.4 s; `WorkerModule.lean` checks
the actual theorem with both mandatory imports in 2.5 s; `RequiredImports.lean`
checks the complete recorded dependency interfaces in 3.1 s without diagnostics.
All were compiled individually through `tools/lean_file.sh` with its 60 s limit.
The complete probe also passes `batch2/scompile.py` sandbox and library checks.
Server probes are under `lean/.sandbox/NW-maint-1792598210/`; dispatcher-side
logs are in the maintenance task's `evidence/` directory.

An isolated reexport experiment removed the first duplicate but uncovered
`CochainComplex.isKFlat_mappingCone` in the two KFlatClosure modules. The trial
was restored in its detached checkout; it was never applied to the live library.
The existing module visibility is sufficient for this item's required imports.
No theorem, definition, node binding, compiler tool or published artifact changed.
